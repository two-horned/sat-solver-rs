use core::alloc::{AllocError, Allocator, Layout};
use core::ptr::NonNull;
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use core::usize;
use std::alloc::{alloc, dealloc};

impl PoolAlloc {
    pub fn from(mbrl: Layout, capc: usize) -> Option<Self> {
        let pilot = {
            let size = mbrl.size();
            let align = mbrl.align();

            if align > size_of::<usize>() {
                return None;
            }

            let true_size = 2 * size_of::<usize>() + size - size & (size_of::<usize>() - 1);

            match Layout::from_size_align(true_size * capc, align) {
                Err(_) => return None,
                Ok(x) => x,
            }
        };

        let space = unsafe { alloc(pilot) };
        let goons = AtomicUsize::new(capc);

        {
            let ptr = space.cast::<*mut u8>();
            for i in 0..capc {
                unsafe { *ptr.add(i) = space }
            }
        }

        Some(Self {
            layout: mbrl,
            pilot,
            space,
            goons,
        })
    }
}

pub struct PoolAlloc {
    layout: Layout,
    pilot: Layout,
    space: *mut u8,
    goons: AtomicUsize,
}

impl Drop for PoolAlloc {
    fn drop(&mut self) {
        unsafe { dealloc(self.space, self.pilot) }
    }
}

unsafe impl Sync for PoolAlloc {}

unsafe impl Allocator for PoolAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout != self.layout {
            return Err(AllocError);
        }

        match self.goons.fetch_update(
            Relaxed,
            Relaxed,
            |x| if x == 0 { None } else { Some(x - 1) },
        ) {
            Err(_) => Err(AllocError),
            Ok(x) => {
                let res = unsafe {
                    self.space
                        .cast::<*mut u8>()
                        .add(x - 1)
                        .read()
                        .cast::<NonNull<[u8]>>()
                        .read()
                };
                Ok(res)
            }
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
        let x = self.goons.update(Relaxed, Relaxed, |x| x + 1);
        self.space.cast::<NonNull<u8>>().add(x - 1).write(ptr);
    }
}
