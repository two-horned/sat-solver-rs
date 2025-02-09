use std::alloc::{AllocError, Allocator, Layout};
use std::iter;
use std::ptr::NonNull;
use std::sync::Mutex;

pub struct PoolAlloc {
    memory: Mutex<BumpMemory>,
}

struct BumpMemory {
    buffer: Vec<u8>, // Pre-allocated memory buffer
    offset: usize,      // Current allocation offset
}

impl PoolAlloc {
    pub fn new() -> Self {
        Self {
            memory: Mutex::new(BumpMemory {
                buffer: Vec::with_capacity(10_000),
                offset: 0,
            }),
        }
    }
}

unsafe impl Allocator for PoolAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let mut memory = self.memory.lock().unwrap();
        let start = memory.offset;
        let end = start + layout.size();

        if end > memory.buffer.len() {
            memory.buffer.extend(iter::repeat_n(0, end));
        } 
            memory.offset = end;
            let slice = &mut memory.buffer[start..end];
            Ok(NonNull::from(slice))
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // No-op: deallocation is unsupported in a bump allocator.
    }
}
