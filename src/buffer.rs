use crate::region::Region;
use crate::error::TriskellError;

#[derive(Debug, Copy, Clone)]
enum RegionType {
    LeftRegion,
    RightRegion,
}

#[derive(Debug)]
pub(crate) struct Reservation {
    start: usize,
    len: usize,
    r_type: RegionType,
}

impl Reservation {
    #[inline]
    fn new(start:usize, len: usize, r_type: RegionType) -> Self {
        Reservation { start, len, r_type }
    }

    #[inline]
    fn r_type(&self) -> RegionType {
        self.r_type
    }

    #[inline]
    fn start(&self) -> usize {
        self.start
    }

    #[inline]
    fn end(&self) -> usize {
        self.start + self.len
    }

    #[cfg(test)]
    #[inline]
    fn len(&self) -> usize {
        self.len
    }
}

#[derive(Debug, PartialEq)]
pub enum AllocationStrategy {
    Exact,
    AtLeast,
    NonGrowable,
}

impl Default for AllocationStrategy {
    fn default() -> Self {
        AllocationStrategy::AtLeast
    }
}

/// A TRBuffer is similar to a circular buffer, but data is inserted in three revolving
/// regions of the buffer space. This allows reads to return contiguous blocks of memory, even
/// if they span a region that would normally include a wrap-around in a circular buffer. It's
/// especially useful for APIs requiring blocks of contiguous memory, eliminating the need to
/// copy data into an interim buffer before use.
///
/// # Example
///
/// ```
/// use triskell::TRBuffer;
///
/// // Creates a TRBuffer of u8 and allocates 8 elements.
/// let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(8);
/// {
///   // Reserves 4 slots at the back for insert
///   let reserved = buffer.reserve_back(4).unwrap();
///   reserved[0] = 2;
///   reserved[1] = 12;
///   reserved[2] = 34;
///   reserved[3] = 7;
/// }
/// // Stores the values into an available region
/// buffer.commit(4);
/// {
///   // Gets the front data stored in the region as a contiguous block
///   let block = buffer.read_front().unwrap();
///   assert_eq!(block[0], 2);
///   assert_eq!(block[1], 12);
///   assert_eq!(block[2], 34);
///   assert_eq!(block[3], 7);
/// }
/// // Release the first two front elements of the block
/// buffer.free_front(2);
/// {
///   let block = buffer.read_front().unwrap();
///   assert_eq!(block[0], 34);
///   assert_eq!(block[1], 7);
/// }
/// ```
#[derive(Debug, Default)]
pub struct TRBuffer<T> {
    buffer: Vec<T>,
    // Left Region
    l_region: Region,
    // Main Region
    m_region: Region,
    // Right Region
    r_region: Region,
    allocation_strategy: AllocationStrategy,
    reservation: Option<Reservation>,
}

impl<T> TRBuffer<T> {
    /// Construct a new empty TRBuffer.
    ///
    // The TRBuffer will not allocate until space is reserved.
    pub fn new() -> Self {
        TRBuffer {
            buffer: Vec::new(),
            l_region: Default::default(),
            m_region: Default::default(),
            r_region: Default::default(),
            allocation_strategy: AllocationStrategy::default(),
            reservation: None,
        }
    }

    /// Construct a new empty TRBuffer with at least the specified capacity.
    ///
    /// The TRBuffer will be able to hold at least capacity elements without reallocating.
    pub fn with_capacity(len: usize) -> Self {
        let mut buffer = Vec::with_capacity(len);

        // SAFETY: new_len is equal to capacity()
        unsafe { buffer.set_len(buffer.capacity()) };

        TRBuffer {
            buffer,
            l_region: Default::default(),
            m_region: Default::default(),
            r_region: Default::default(),
            allocation_strategy: AllocationStrategy::default(),
            reservation: None,
        }
    }

    /// Return a raw mutable pointer to the TRBuffer.
    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        self.buffer.as_mut_ptr()
    }

    /// Return the total number of elements the TRBuffer can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buffer.capacity()
    }

    /// Define the allocation strategy.
    #[inline]
    pub fn set_allocation_strategy(&mut self, allocation_strategy: AllocationStrategy) {
        self.allocation_strategy = allocation_strategy;
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn l_region(&self) -> &Region {
        &self.l_region
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn m_region(&self) -> &Region {
        &self.m_region
    }
    
    #[cfg(test)]
    #[inline]
    pub(crate) fn r_region(&self) -> &Region {
        &self.r_region
    }
    
    /// Returns `true` if the TRBuffer contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.reservation.is_none() &&
        self.l_region.is_empty() &&
        self.m_region.is_empty() &&
        self.r_region.is_empty()
    }

    #[inline]
    pub(crate) fn reservation(&self) -> Option<&Reservation> {
        self.reservation.as_ref()
    }

    /// Returns the number of elements in the TRBuffer.
    #[inline]
    pub fn len(&self) -> usize {
        self.l_region.len() + self.m_region.len() + self.r_region.len()
    }

    /// Clears all regions and reservations.
    #[inline]
    pub fn clear(&mut self) {
        self.l_region.reset();
        self.m_region.reset();
        self.r_region.reset();
        self.reservation = None;
    }
   
    #[inline]
    fn reallocate(&mut self, additional: usize) -> Result<(), TriskellError> {
        match self.allocation_strategy {
            AllocationStrategy::Exact => {
                self.buffer.reserve_exact(additional);
            },
            AllocationStrategy::AtLeast => {
                self.buffer.reserve(additional);
            },
            AllocationStrategy::NonGrowable => {
                return Err(TriskellError::NotEnoughMemory);
            },
        }

        // SAFETY: new_len is equal to capacity()
        unsafe { self.buffer.set_len(self.buffer.capacity()) };
        Ok(())
    }

    fn reallocate_front(&mut self, additional: usize) -> Result<(), TriskellError> {
        self.reallocate(additional)?;

        // Move Right Region at the end of the buffer.
        if self.r_region.len() > 0 {
            unsafe {
                std::ptr::copy(
                    self.as_mut_ptr().add(self.r_region.start()),
                    self.as_mut_ptr().add(self.capacity() - self.r_region.len()),
                    self.r_region.len());
            }
            self.r_region.set(self.capacity() - self.r_region.len(), self.capacity());
        }

        Ok(())
    }

    fn reallocate_back(&mut self, additional: usize) -> Result<(), TriskellError> {
        self.reallocate(additional)?;

        // Move Right Region at the end of the buffer.
        if self.r_region.len() > 0 {
            unsafe {
                std::ptr::copy(
                    self.as_mut_ptr().add(self.r_region.start()),
                    self.as_mut_ptr().add(self.capacity() - self.r_region.len()),
                    self.r_region.len());
            }
            self.r_region.set(self.capacity() - self.r_region.len(), self.capacity());
        }
        // Append Left Region to Main Region 
        if self.l_region.len() > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(
                    self.as_mut_ptr().add(self.l_region.start()),
                    self.as_mut_ptr().add(self.m_region.end()),
                    self.l_region.len());
            }
            self.m_region.add_end(self.l_region.len());
            self.l_region.reset();
        }

        Ok(())
    }

    /// Reserves `len` bytes to be prepended and return a mutable slice of `T`.
    ///
    /// If there is not enough space, reallocates the buffer.
    pub fn reserve_front(&mut self, len: usize) -> Result<&mut [T], TriskellError> {
        debug_assert!(len > 0);

        // Right Region is not empty, it means Main Region is already full.
        let reserve_start = if !self.r_region.is_empty() {
            let space_after_m = self.r_region.start() - self.m_region.end();
            // There is enough space to prepend to the Right Region
            if space_after_m >= len {
                // TODO: replace by `unchecked_sub` when the API become stable
                self.r_region.start().wrapping_sub(len)
            }
            // No more space, need to allocate more bytes
            else {
                self.reallocate_front(len)?;
                // TODO: replace by `unchecked_sub` when the API become stable
                (self.capacity() - self.r_region.len()).wrapping_sub(len)
            }
        }
        // Right Region is empty, check if Main Region has enough space
        // to prepend additional bytes.
        else {
            let space_before_m = self.m_region.start() - self.l_region.end();
            // There is enough space to prepend the Main Region
            if space_before_m >= len {
                // TODO: replace by `unchecked_sub` when the API become stable
                self.m_region.start().wrapping_sub(len)
            }
            // Need to reserve in the Right Region
            else {
                let space_after_m = self.capacity() - self.m_region.end();
                
                // No space available, need to allocate more bytes
                if space_after_m < len {
                    self.reallocate_front(len - space_after_m)?;
                }
                
                // TODO: replace by `unchecked_sub` when the API become stable
                self.capacity().wrapping_sub(len)
            }
        };

        self.reservation = Some(Reservation::new(reserve_start, len, RegionType::RightRegion));
        Ok(&mut self.buffer[reserve_start..reserve_start + len])
    }


    /// Reserves `len` bytes to be appended and return a mutable slice of `T`.
    ///
    /// If there is not enough space, reallocates the buffer.
    pub fn reserve_back(&mut self, len: usize) -> Result<&mut [T], TriskellError> {
        debug_assert!(len > 0);

        // Left Region is not empty, it means Main Region is already full.
        let reserve_start = if !self.l_region.is_empty() {
            let space_before_m = self.m_region.start() - self.l_region.end();
            // There is enough space to append the Left Region
            if space_before_m >= len {
                self.l_region.end()
            }
            // No more space, need to allocate more bytes
            else {
                self.reallocate_back(len)?;
                self.m_region.end()
            }
        }
        // Left Region is empty, check if Main Region has enough space
        // to append additional bytes.
        else {
            let space_after_m = self.capacity() - self.m_region.end() - self.r_region.len();

            // There is enough space to append the Main Region
            if space_after_m >= len {
                self.m_region.end()
            }
            // There is enough space to reserve in the Left Region
            else if self.m_region.start() >= len {
                0
            }
            // No more space, need to allocate more bytes
            else {
                self.reallocate_back(len - space_after_m)?;
                self.m_region.end()
            }
        };

        self.reservation = Some(Reservation::new(reserve_start, len, RegionType::LeftRegion));
        Ok(&mut self.buffer[reserve_start..reserve_start + len])
    }

    /// Commits the data in the reservation, allowing it to be read later
    pub fn commit(&mut self, len: usize) {
        if len == 0 {
            return;
        }

        let capacity = self.capacity();
        if let Some(reservation) = self.reservation() {
            let to_commit = std::cmp::min(len, reservation.len);
            match reservation.r_type() {
                RegionType::LeftRegion => {
                    // Initial commit
                    if self.m_region.len() == 0 && self.l_region.len() == 0 {
                        self.m_region.set(reservation.start(), reservation.start() + to_commit);
                    }
                    // Bytes reserved just after Main Region
                    else if reservation.start() == self.m_region.end() {
                        self.m_region.add_end(to_commit);
                    }
                    // Increase Left Region
                    else {
                        self.l_region.add_end(to_commit);
                    }
                },
                RegionType::RightRegion => {
                    // Initial commit
                    if self.m_region.len() == 0 && self.r_region.len() == 0 {
                        self.m_region.set(reservation.end() - to_commit, reservation.end());
                    }
                    // Bytes reserved just before Main Region
                    else if reservation.end() == self.m_region.start() {
                        self.m_region.sub_start(to_commit);
                    }
                    // Increase Right Region
                    else {
                        if self.r_region.len() == 0 {
                            self.r_region.set(capacity - to_commit, capacity);
                        }
                        else {
                            self.r_region.sub_start(to_commit);
                        }
                    }
                },
            }
        }
        self.reservation = None;
    }

    /// Retrieves available (committed) data as a contiguous block (FIFO).
    ///
    /// Returns `None` if there is no data available
    /// Must called `free_front()` to free data.
    #[inline]
    pub fn read_front(&self) -> Option<&[T]> {
        self.read_front_indexes().map(|(start, end)| self.get(start, end))
    }
    pub fn read_front_indexes(&self) -> Option<(usize, usize)> {
        if !self.r_region.is_empty() {
            Some((self.r_region.start(), self.r_region.end()))
        }
        else if !self.m_region.is_empty() {
            Some((self.m_region.start(), self.m_region.end()))
        }
        else if !self.l_region.is_empty() {
            Some((self.l_region.start(), self.l_region.end()))
        }
        else {
            None
        }
    }

    /// Retrieves available (committed) data as a contiguous block (LIFO).
    ///
    /// Returns `None` if there is no data available
    /// Must called `free_back()` to free data.
    #[inline]
    pub fn read_back(&self) -> Option<&[T]> {
        self.read_back_indexes().map(|(start, end)| self.get(start, end))
    }
    pub fn read_back_indexes(&self) -> Option<(usize, usize)> {
        if !self.l_region.is_empty() {
            Some((self.l_region.start(), self.l_region.end()))
        }
        else if !self.m_region.is_empty() { 
            Some((self.m_region.start(), self.m_region.end()))
        }
        else if !self.r_region.is_empty() {
            Some((self.r_region.start(), self.r_region.end()))
        }
        else {
            None
        }
    }

    #[inline]
    pub fn get(&self, start: usize, end: usize) -> &[T] {
        &self.buffer[start..end]
    }

    #[inline]
    pub fn get_mut(&mut self, start: usize, end: usize) -> &mut [T] {
        &mut self.buffer[start..end]
    }

    /// Remove `len` bytes at the beginning of the buffer.
    ///
    /// The next time `read()` is called, it will not include these elements.
    pub fn free_front(&mut self, mut len: usize) {
        let r_len = self.r_region.len();
        // Free the Right Region
        if len >= r_len {
            len -= r_len;

            let m_len = self.m_region.len();
            // Free the Main Region
            if len >= m_len {
                len -= m_len;

                // If `len` is greater than Left Region, remove remaining bytes to Left Region and
                // swap Left Region and Main Region
                if self.l_region.len() > len {
                    self.l_region.add_start(len);
                    self.m_region.set_region(&self.l_region);
                }
                else {
                    self.m_region.reset();
                }

                self.l_region.reset();
            }
            // Remove remaining bytes from Main Region
            else {
                self.m_region.add_start(len);
            }
            self.r_region.reset();
        }
        // Remove `len` from the Right Region
        else {
            self.r_region.add_start(len);
        }
    }

    /// Remove `len` bytes at the end of the buffer.
    ///
    /// The next time `read()` is called, it will not include these elements.
    pub fn free_back(&mut self, mut len: usize) {
        let l_len = self.l_region.len();
        // Free the Left Region
        if len >= l_len {
            len -= l_len;

            // Free the Main Region
            let m_len = self.m_region.len();
            if len >= m_len {
                len -= m_len;

                // If `len` is greater than Right Region, remove remaining bytes to Right Region and
                // swap Right Region and Main Region
                if self.r_region.len() > len {
                    self.r_region.sub_end(len);
                    self.m_region.set_region(&self.r_region);
                }
                else {
                    self.m_region.reset();
                }

                self.r_region.reset();
            }
            // Remove remaining bytes from the Main Region
            else {
                self.m_region.sub_end(len);
            }

            self.l_region.reset();
        }
        // Remove remaining bytes from the Left Region
        else {
            self.l_region.sub_end(len);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::MaybeUninit;

    #[test]
    fn read_front_empty() {
        let buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        let block = buffer.read_front();
        assert!(block.is_none());
    }

    #[test]
    fn read_back_empty() {
        let buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        let block = buffer.read_back();
        assert!(block.is_none());
    }

    #[test]
    fn allocation_non_growable() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        buffer.set_allocation_strategy(AllocationStrategy::NonGrowable);
        assert_eq!(buffer.reserve_back(4), Err(TriskellError::NotEnoughMemory));
    }

    #[test]
    fn read_front_uncommited() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        buffer.reserve_back(2).unwrap();
        let block = buffer.read_front();
        assert!(block.is_none());
    }

    #[test]
    fn read_back_uncommited() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        buffer.reserve_front(2).unwrap();
        let block = buffer.read_back();
        assert!(block.is_none());
    }

    #[test]
    fn initial_allocation_front() {
        let mut buffer: TRBuffer<u8> = TRBuffer::new();
        let reserved = buffer.reserve_front(4).unwrap();
        assert_eq!(reserved.len(), 4);
    }

    #[test]
    fn initial_allocation_back() {
        let mut buffer: TRBuffer<u8> = TRBuffer::new();
        let reserved = buffer.reserve_back(4).unwrap();
        assert_eq!(reserved.len(), 4);
    }

    #[test]
    fn reserve_greater_len_front() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        assert!(buffer.reservation().is_none());
        let reserved = buffer.reserve_front(4).unwrap();
        assert_eq!(reserved.len(), 4);
        assert_eq!(buffer.reservation().unwrap().len(), 4);
    }

    #[test]
    fn reserve_greater_len_back() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(3);
        assert!(buffer.reservation().is_none());
        let reserved = buffer.reserve_back(4).unwrap();
        assert_eq!(reserved.len(), 4);
        assert_eq!(buffer.reservation().unwrap().len(), 4);
    }

    #[test]
    fn reserve_two_times() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(3);
        assert!(buffer.reservation().is_none());
        {
            // [ 1 9 c d ]
            let reserved = buffer.reserve_back(4).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[2].write(0xd);
        }
        assert_eq!(buffer.reservation().unwrap().len(), 4);
        {
            // [ a b e ]
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0xa);
            reserved[1].write(0xb);
            reserved[2].write(0xe);
        }
        assert_eq!(buffer.reservation().unwrap().len(), 3);

        buffer.commit(3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0xa);
        assert_eq!(unsafe { block[1].assume_init() }, 0xb);
        assert_eq!(unsafe { block[2].assume_init() }, 0xe);
    }

    #[test]
    fn reserve_full_front() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(4);
        buffer.reserve_back(4).unwrap();
        buffer.commit(4);
        let reserved = buffer.reserve_front(1).unwrap();
        assert_eq!(reserved.len(), 1);
    }

    #[test]
    fn reserve_full_back() {
        let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(4);
        buffer.reserve_front(4).unwrap();
        buffer.commit(4);
        let reserved = buffer.reserve_back(1).unwrap();
        assert_eq!(reserved.len(), 1);
    }

    #[test]
    fn reallocate_back() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::new();
        buffer.set_allocation_strategy(AllocationStrategy::Exact);
        {
            // [ 1 9 c ]
            let reserved = buffer.reserve_back(3).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
        }
        
        assert_eq!(buffer.len(), 0);
        assert_eq!(buffer.capacity(), 3);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
        
        {
            // [ 1 9 c . . . ]
            // [ 1 9 c 2 a 3 ]
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0x2);
            reserved[1].write(0xa);
            reserved[2].write(0x3);
        }

        assert_eq!(buffer.capacity(), 6);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 3);
        assert_eq!(buffer.r_region().len(), 3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);

        {
            // [ 1 9 c 2 a 3 . . . ]
            // [ 1 9 c . . . 2 a 3 ]
            // [ 1 9 c a b c 2 a 3 ]
            let reserved = buffer.reserve_back(3).unwrap();
            reserved[0].write(0xa);
            reserved[1].write(0xb);
            reserved[2].write(0xc);
        }
        
        assert_eq!(buffer.capacity(), 9);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 6);
        assert_eq!(buffer.r_region().len(), 3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 6);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
        assert_eq!(unsafe { block[3].assume_init() }, 0xa);
        assert_eq!(unsafe { block[4].assume_init() }, 0xb);
        assert_eq!(unsafe { block[5].assume_init() }, 0xc);

        // [ . . . a b c . . . ]
        buffer.free_front(6);
        
        assert_eq!(buffer.capacity(), 9);
        assert_eq!(buffer.m_region().len(), 3);
        assert_eq!(buffer.r_region().len(), 0);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0xa);
        assert_eq!(unsafe { block[1].assume_init() }, 0xb);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
        
        {
            // [ . . . a b c 1 2 . ]
            let reserved = buffer.reserve_back(2).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x2);
        }
     
        buffer.commit(2);

        {
            // [ d e . a b c 1 2 . ]
            let reserved = buffer.reserve_back(2).unwrap();
            reserved[0].write(0xd);
            reserved[1].write(0xe);
        }

        assert_eq!(buffer.capacity(), 9);
        buffer.commit(2);
        assert_eq!(buffer.m_region().len(), 5);
        assert_eq!(buffer.l_region().len(), 2);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 2);
        assert_eq!(unsafe { block[0].assume_init() }, 0xd);
        assert_eq!(unsafe { block[1].assume_init() }, 0xe);

        // [ d e . . . . . . . ]
        buffer.free_front(2);
        buffer.free_front(3);
        
        assert_eq!(buffer.capacity(), 9);
        assert_eq!(buffer.m_region().len(), 2);
        assert_eq!(buffer.l_region().len(), 0);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 2);
        assert_eq!(unsafe { block[0].assume_init() }, 0xd);
        assert_eq!(unsafe { block[1].assume_init() }, 0xe);
    }

    #[test]
    fn reallocate_front() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::new();
        buffer.set_allocation_strategy(AllocationStrategy::Exact);
        {
            // [ 1 9 c ]
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
        }
        
        assert_eq!(buffer.len(), 0);
        assert_eq!(buffer.capacity(), 3);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
        
        {
            // [ 1 9 c . . . ]
            // [ 1 9 c 2 a 3 ]
            let reserved = buffer.reserve_back(3).unwrap();
            reserved[0].write(0x2);
            reserved[1].write(0xa);
            reserved[2].write(0x3);
        }

        assert_eq!(buffer.capacity(), 6);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 6);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 6);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
        assert_eq!(unsafe { block[3].assume_init() }, 0x2);
        assert_eq!(unsafe { block[4].assume_init() }, 0xa);
        assert_eq!(unsafe { block[5].assume_init() }, 0x3);

        {
            // [ 1 9 c 2 a 3 . . . ]
            // [ 1 9 c 2 a 3 a b c ]
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0xa);
            reserved[1].write(0xb);
            reserved[2].write(0xc);
        }
        
        assert_eq!(buffer.capacity(), 9);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 6);
        assert_eq!(buffer.r_region().len(), 3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 6);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
        assert_eq!(unsafe { block[3].assume_init() }, 0x2);
        assert_eq!(unsafe { block[4].assume_init() }, 0xa);
        assert_eq!(unsafe { block[5].assume_init() }, 0x3);
        buffer.free_back(7);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 2);
        assert_eq!(unsafe { block[0].assume_init() }, 0xa);
        assert_eq!(unsafe { block[1].assume_init() }, 0xb);
       
        {
            // [ . . . . . . a b . ]
            // [ . . . 1 2 3 a b . ]
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x2);
            reserved[2].write(0x3);
        }
        
        assert_eq!(buffer.capacity(), 9);
        buffer.commit(3);
        {
            // [ . . . 1 2 3 a b . ]
            // [ . 5 6 1 2 3 a b . ]
            let reserved = buffer.reserve_front(2).unwrap();
            reserved[0].write(0x4);
            reserved[1].write(0x5);
        }
        
        assert_eq!(buffer.capacity(), 9);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 7);
        assert_eq!(buffer.r_region().len(), 0);
        let block = buffer.read_front().unwrap();
        assert_eq!(block.len(), 7);
        assert_eq!(unsafe { block[0].assume_init() }, 0x4);
        assert_eq!(unsafe { block[1].assume_init() }, 0x5);
        assert_eq!(unsafe { block[2].assume_init() }, 0x1);
        assert_eq!(unsafe { block[3].assume_init() }, 0x2);
        assert_eq!(unsafe { block[4].assume_init() }, 0x3);
        assert_eq!(unsafe { block[5].assume_init() }, 0xa);
        assert_eq!(unsafe { block[6].assume_init() }, 0xb);

        {
            // [ . 4 5 1 2 3 a b . . . ]
            // [ . 4 5 1 2 3 a b d e f ]
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0xd);
            reserved[1].write(0xe);
            reserved[2].write(0xf);
        }
    
        assert_eq!(buffer.capacity(), 11);
        buffer.commit(3);
        assert_eq!(buffer.m_region().len(), 7);
        assert_eq!(buffer.r_region().len(), 3);
    
        {
            // [ . 4 5 1 2 3 a b c d e f . ]
            // [ . 4 5 1 2 3 a b c . d e f ]
            // [ . 4 5 1 2 3 a b c 7 d e f ]
            let reserved = buffer.reserve_front(1).unwrap();
            reserved[0].write(0x7);
        }
        
        assert_eq!(buffer.capacity(), 12);
        buffer.commit(1);
        assert_eq!(buffer.m_region().len(), 7);
        assert_eq!(buffer.r_region().len(), 4);
        let block = buffer.read_front().unwrap();
        assert_eq!(block.len(), 4);
        assert_eq!(unsafe { block[0].assume_init() }, 0x7);
        assert_eq!(unsafe { block[1].assume_init() }, 0xd);
        assert_eq!(unsafe { block[2].assume_init() }, 0xe);
        assert_eq!(unsafe { block[3].assume_init() }, 0xf);

        buffer.free_front(2);
        buffer.free_front(2);
        
        assert_eq!(buffer.m_region().len(), 7);
        assert_eq!(buffer.r_region().len(), 0);
        let block = buffer.read_front().unwrap();
        assert_eq!(block.len(), 7);
        assert_eq!(unsafe { block[0].assume_init() }, 0x4);
        assert_eq!(unsafe { block[1].assume_init() }, 0x5);
        assert_eq!(unsafe { block[2].assume_init() }, 0x1);
        assert_eq!(unsafe { block[3].assume_init() }, 0x2);
        assert_eq!(unsafe { block[4].assume_init() }, 0x3);
        assert_eq!(unsafe { block[5].assume_init() }, 0xa);
        assert_eq!(unsafe { block[6].assume_init() }, 0xb);
    }

    #[test]
    fn commit_and_read_front() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        {
            let reserved = buffer.reserve_front(3).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
        }
        assert_eq!(buffer.len(), 0);
        buffer.commit(3);
        let block = buffer.read_back().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
    }

    #[test]
    fn commit_and_read_back() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        {
            // [ 1 9 c ]
            let reserved = buffer.reserve_back(3).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
        }
        assert_eq!(buffer.len(), 0);
        buffer.commit(3);
        let block = buffer.read_front().unwrap();
        assert_eq!(block.len(), 3);
        assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        assert_eq!(unsafe { block[2].assume_init() }, 0xc);
    }

    #[test]
    fn free_front() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        {
            // [ 1 9 c f ]
            let reserved = buffer.reserve_front(4).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
        }
        buffer.commit(4);
        buffer.free_front(2);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0xc);
            assert_eq!(unsafe { block[1].assume_init() }, 0xf);
        }
        buffer.free_front(1);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 1);
            assert_eq!(unsafe { block[0].assume_init() }, 0xf);
        }
    }

    #[test]
    fn free_back() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        {
            // [ 1 9 c f ]
            let reserved = buffer.reserve_back(4).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
        }
        buffer.commit(4);
        buffer.free_back(2);
        {
            let block = buffer.read_back().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        }
        buffer.free_back(1);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 1);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
        }
    }

    #[test]
    fn reserve_after_front() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        {
            // [ 1 9 c f ]
            let reserved = buffer.reserve_back(4).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
        }
        buffer.commit(4);

        // [ . . c f ]
        buffer.free_front(2);
        {
            // [ . . c f . . . . ]
            // [ . . c f 2 3 4 5 ]
            let reserved = buffer.reserve_front(4).unwrap();
            reserved[0].write(0x2);
            reserved[1].write(0x3);
            reserved[2].write(0x4);
            reserved[3].write(0x5);
        }

        // [ . . c f . . 4 5 ]
        buffer.commit(2);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0x4);
            assert_eq!(unsafe { block[1].assume_init() }, 0x5);
        }
        
        // [ . . c f . . . . ]
        buffer.free_front(2);
        {
            let block = buffer.read_back().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0xc);
            assert_eq!(unsafe { block[1].assume_init() }, 0xf);
        }
        // [ . . . . . . . . ]
        buffer.free_back(4);
        assert!(buffer.read_front().is_none());
    }

    #[test]
    fn reserve_after_back() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        buffer.set_allocation_strategy(AllocationStrategy::Exact);
        {
            // [ 1 9 c f ]
            let reserved = buffer.reserve_front(4).unwrap();
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
        }
        buffer.commit(4);

        // [ 1 9 . . ]
        buffer.free_back(2);
        assert_eq!(buffer.capacity(), 4);
        assert_eq!(buffer.m_region().len(), 2);
        {
            // [ 1 9 . . . . ]
            // [ 1 9 2 3 4 5 ]
            let reserved = buffer.reserve_back(4).unwrap();
            reserved[0].write(0x2);
            reserved[1].write(0x3);
            reserved[2].write(0x4);
            reserved[3].write(0x5);
        }
        // [ 1 9 2 3 . . ]
        buffer.commit(2);
        assert_eq!(buffer.capacity(), 6);
        {
            let block = buffer.read_back().unwrap();
            assert_eq!(block.len(), 4);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
            assert_eq!(unsafe { block[2].assume_init() }, 0x2);
            assert_eq!(unsafe { block[3].assume_init() }, 0x3);
        }
        // [ 1 9 . . . . ]
        buffer.free_back(2);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        }
        // [ . . . . . . ]
        buffer.free_front(4);
        assert!(buffer.read_back().is_none());
    }

    #[test]
    fn reserve_complex_back() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(8);
        {
            let reserved = buffer.reserve_back(4).unwrap();
            // [ 1 9 c f ]
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
        }
        buffer.commit(4);
        {
            let reserved = buffer.reserve_front(2).unwrap();
            // [ 1 9 c f . . ]
            // [ 1 9 c f a b ]
            reserved[0].write(0xa);
            reserved[1].write(0xb);
        }
        buffer.commit(2);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0xa);
            assert_eq!(unsafe { block[1].assume_init() }, 0xb);
        }
        {
            let block = buffer.read_back().unwrap();
            assert_eq!(block.len(), 4);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
            assert_eq!(unsafe { block[2].assume_init() }, 0xc);
            assert_eq!(unsafe { block[3].assume_init() }, 0xf);
        }
        // [ 1 9 . . a b ]
        buffer.free_back(2);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0xa);
            assert_eq!(unsafe { block[1].assume_init() }, 0xb);
        }
        {
            let block = buffer.read_back().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
        }
    }


    #[test]
    fn reserve_complex_front() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(8);
        {
            let reserved = buffer.reserve_back(6).unwrap();
            // [ 1 9 c f 2 3 ]
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
            reserved[4].write(0x2);
            reserved[5].write(0x3);
        }
        buffer.commit(6);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 6);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
            assert_eq!(unsafe { block[2].assume_init() }, 0xc);
            assert_eq!(unsafe { block[3].assume_init() }, 0xf);
            assert_eq!(unsafe { block[4].assume_init() }, 0x2);
            assert_eq!(unsafe { block[5].assume_init() }, 0x3);
        }
        {
            let reserved = buffer.reserve_front(2).unwrap();
            // [ 1 9 c f 2 3 . . ]
            // [ 1 9 c f 2 3 a b ]
            reserved[0].write(0xa);
            reserved[1].write(0xb);
        }
        buffer.commit(2);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 2);
            assert_eq!(unsafe { block[0].assume_init() }, 0xa);
            assert_eq!(unsafe { block[1].assume_init() }, 0xb);
        }
        
        // [ 1 9 c f . .  a b ]
        buffer.free_back(2);
        assert_eq!(buffer.capacity(), 8);
        {
            let block = buffer.read_back().unwrap();
            assert_eq!(block.len(), 4);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x9);
            assert_eq!(unsafe { block[2].assume_init() }, 0xc);
            assert_eq!(unsafe { block[3].assume_init() }, 0xf);
        }
        {
            let reserved = buffer.reserve_front(2).unwrap();
            // [ 1 9 c f 1 2 a b ]
            reserved[0].write(0x1);
            reserved[1].write(0x2);
        }
        buffer.commit(4);
        assert_eq!(buffer.capacity(), 8);
        {
            let block = buffer.read_front().unwrap();
            assert_eq!(block.len(), 4);
            assert_eq!(unsafe { block[0].assume_init() }, 0x1);
            assert_eq!(unsafe { block[1].assume_init() }, 0x2);
            assert_eq!(unsafe { block[2].assume_init() }, 0xa);
            assert_eq!(unsafe { block[3].assume_init() }, 0xb);
        }
    }

    #[test]
    fn clear() {
        let mut buffer: TRBuffer<MaybeUninit<u8>> = TRBuffer::with_capacity(4);
        {
            let reserved = buffer.reserve_back(4).unwrap();
            // [ 1 9 c f ]
            reserved[0].write(0x1);
            reserved[1].write(0x9);
            reserved[2].write(0xc);
            reserved[3].write(0xf);
        }
        assert_eq!(buffer.reservation().unwrap().len(), 4);
        buffer.commit(4);
        assert!(buffer.reservation().is_none());
        buffer.clear();
        assert_eq!(buffer.len(), 0);
    }
}
