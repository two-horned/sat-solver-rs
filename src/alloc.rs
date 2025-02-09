use std::alloc::{AllocError, Allocator, Layout};
use std::iter;
use std::ptr::NonNull;
use std::sync::Mutex;

pub struct PoolAlloc {
    objsiz: usize,
    memory: Mutex<PoolMemory>,
}

struct PoolMemory {
    buffr: Box<[u8]>,
    frees: Vec<usize>,
}

impl PoolAlloc {
    pub fn new(obj_len: usize, capacity: usize) -> Self {
        Self {
            objsiz: obj_len,
            memory: Mutex::new(PoolMemory {
                buffr: iter::repeat_n(0, obj_len * capacity).collect(),
                frees: (0..capacity).map(|x| obj_len * x).collect(),
            }),
        }
    }
}

unsafe impl Allocator for PoolAlloc {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.size() != self.objsiz {
            println!("Wrong size!, {:?} instead {:?}", layout.size(), self.objsiz);
            return Err(AllocError);
        }

        let mut memory = self.memory.lock().unwrap();
        if let Some(start) = memory.frees.pop() {
            let slice = &mut memory.buffr[start..start + self.objsiz];
            Ok(NonNull::from(slice))
        } else {
            Err(AllocError)
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
        let mut memory = self.memory.lock().unwrap();
        let ptro = NonNull::from(&memory.buffr[0]);
        let diff = ptr.sub_ptr(ptro);
        memory.frees.push(diff);
    }
}
