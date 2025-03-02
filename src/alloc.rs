use core::alloc::{AllocError, Allocator, Layout};
use core::ptr::NonNull;
use core::slice;
use std::alloc::{alloc, dealloc};
use std::sync::Mutex;

impl PoolAlloc {
    pub fn new(layout: Layout, capacity: usize) -> Self {
        let objalg = layout.align();
        let (memlyt, objsiz) = layout.repeat(capacity).unwrap();
        let memory = unsafe { alloc(memlyt) };
        let frptrs = Mutex::new(
            (0..capacity)
                .map(|x| unsafe { memory.add(x * objsiz) })
                .collect(),
        );
        Self {
            objsiz,
            objalg,
            frptrs,
            memlyt,
            memory,
        }
    }
}

unsafe impl Sync for PoolAlloc {}

impl Drop for PoolAlloc {
    fn drop(&mut self) {
        unsafe { dealloc(self.memory, self.memlyt) }
    }
}

#[derive(Debug)]
pub struct PoolAlloc {
    objsiz: usize,
    objalg: usize,
    frptrs: Mutex<Vec<*mut u8>>,
    memlyt: Layout,
    memory: *mut u8,
}

unsafe impl Allocator for PoolAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let (align, size) = (layout.align(), layout.size());
        if align > self.objalg || size > self.objsiz {
            return Err(AllocError);
        }
        let mut frptrs = self.frptrs.lock().unwrap();
        if let Some(start) = frptrs.pop() {
            let slice = unsafe { slice::from_raw_parts_mut(start, size) };
            return Ok(unsafe { NonNull::new_unchecked(slice) });
        }
        Err(AllocError)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, _: Layout) {
        let mut frptrs = self.frptrs.lock().unwrap();
        frptrs.push(ptr.as_ptr());
    }
}
