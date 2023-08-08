#[derive(Debug)]
pub struct Region {
    start: usize,
    end: usize,
}

impl Region {
    #[inline]
    pub(crate) fn new() -> Self {
        Region { start: 0, end: 0 }
    }

    #[inline]
    pub(crate) fn start(&self) -> usize {
        self.start
    }

    #[inline]
    pub(crate) fn end(&self) -> usize {
        self.end
    }

    #[inline]
    pub(crate) fn set(&mut self, start: usize, end: usize) {
        debug_assert!(start <= end, "set start={} end={}", start, end);
        self.start = start;
        self.end = end;
    }

    #[inline]
    pub(crate) fn set_region(&mut self, region: &Region) {
        self.start = region.start;
        self.end = region.end;
    }

    #[inline]
    pub(crate) fn add_start(&mut self, off: usize) {
        debug_assert!(
            self.start + off <= self.end,
            "add start [{}-{}] offset={}",
            self.start,
            self.end,
            off
        );
        self.start += off;
    }

    #[inline]
    pub(crate) fn sub_start(&mut self, off: usize) {
        debug_assert!(
            self.start >= off,
            "sub start [{}-{}] offset={}",
            self.start,
            self.end,
            off
        );
        self.start -= off;
    }

    #[inline]
    pub(crate) fn add_end(&mut self, off: usize) {
        self.end += off;
    }

    #[inline]
    pub(crate) fn sub_end(&mut self, off: usize) {
        debug_assert!(
            self.end >= self.start,
            "sub end [{}-{}] offset={}",
            self.start,
            self.end,
            off
        );
        self.end -= off;
    }

    // Size of the `Region`
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.end - self.start
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.end == self.start
    }

    #[inline]
    pub(crate) fn reset(&mut self) {
        self.start = 0;
        self.end = 0;
    }
}

impl Default for Region {
    fn default() -> Self {
        Region::new()
    }
}
