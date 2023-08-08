# triskell
A tri-partite ring buffer is similar to a circular buffer, but data is inserted in three
revolving regions of the buffer space. This allows reads to return contiguous
blocks of memory, even if they span a region that would normally include a
wrap-around in a circular buffer. It's especially useful for APIs requiring
blocks of contiguous memory, eliminating the need to copy data into an interim
buffer before use.

It is heavily inspired by the article of Simon Cooke's [Bip-Buffer][1].

## Examples
```rust
use triskell::TRBuffer;

// Creates a TRBuffer of u8 and allocates 8 elements
let mut buffer: TRBuffer<u8> = TRBuffer::with_capacity(8);
{
  // Reserves 4 slots at the back for insert
  let reserved = buffer.reserve_back(4).unwrap();
  reserved[0] = 2;
  reserved[1] = 12;
  reserved[2] = 34;
  reserved[3] = 7;
}
// Stores the values into an available region
buffer.commit(4);
{
  // Gets the front data stored in the region as a contiguous block
  let block = buffer.read_front().unwrap();
  assert_eq!(block[0], 2);
  assert_eq!(block[1], 12);
  assert_eq!(block[2], 34);
  assert_eq!(block[3], 7);
}
// Release the first two front elements of the block
buffer.free_front(2);
{
  let block = buffer.read_front().unwrap();
  assert_eq!(block[0], 34);
  assert_eq!(block[1], 7);
}
```

## Capacity and reallocation

The capacity of a tri-partite ring buffer is the amount of space allocated for any future elements that will be added
onto it. If a reservation exceeds its capacity, its capacity will automatically be increased.

There is two allocation strategy:
* **AllocationStrategy::Exact**: Reserves the minimum capacity required to insert a specified number of additional elements.
* **AllocationStrategy::AtLeast**: With this strategy, capacity is reserved to accommodate at least the specified number of additional elements.
* **AllocationStrategy::NonGrowable**: If attempting to reserve capacity beyond the buffer's limit, return an error.
```rust
use triskell::{TRBuffer, AllocationStrategy};

let mut buffer: TRBuffer<u8> = TRBuffer::new();

buffer.set_allocation_strategy(AllocationStrategy::Exact);
```

## What is the difference with a Bip-Buffer ?

As its name imply a tri-partite ring buffer use three regions instead of two. This allows to
read and write data at the back and/or at the front of the buffer.

[1]: https://www.codeproject.com/articles/3479/the-bip-buffer-the-circular-buffer-with-a-twist
