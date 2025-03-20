use crate::alloc::StacklikeAlloc;
use crate::bits::bit_tools::integers_needed;
use core::alloc::Layout;

use crate::problem::Problem;

use core::iter::Iterator;

impl Solver {
    pub fn new(var_numbr: usize, cls_numbr: usize) -> Self {
        // let max_steps = usize::min(var_numbr, cls_numbr / 3 + 3);

        let allocator = {
            let integers_needed =
                cls_numbr * integers_needed(var_numbr) * integers_needed(var_numbr);
            let layout = Layout::from_size_align(integers_needed * var_numbr * var_numbr, 4096).unwrap();
            Box::into_raw(Box::new(StacklikeAlloc::new(layout)))
        };

        let work_onto = {
            Task::Todo(Problem::with_capacity_in(cls_numbr, var_numbr, unsafe {
                allocator.as_ref().unwrap()
            }))
        };

        Self {
            allocator,
            var_numbr,
            cls_numbr,
            work_onto,
        }
    }

    pub fn need_to_add(&self) -> bool {
        match &self.work_onto {
            Task::Todo(x) => x.clauses() < self.cls_numbr,
            _ => false,
        }
    }

    pub fn add_clause(&mut self, literals: Vec<isize>) -> Result<(), SolverError> {
        match &mut self.work_onto {
            Task::Todo(x) if x.clauses() < self.cls_numbr => {
                if let Some(_) = literals.iter().find(|&&x| x == 0) {
                    return Err(SolverError::VariableIsZero);
                }
                if let Some(&x) = literals
                    .iter()
                    .find(|&&x| x.abs() as usize > self.var_numbr)
                {
                    return Err(SolverError::VariableTooLarge(x));
                }

                println!("Attempting to add..{:?}", literals);

                x.add_clause(literals.into_iter());
                Ok(())
            }
            _ => Err(SolverError::TooManyClauses),
        }
    }

    pub fn solve(&mut self) -> Result<Solution, SolverError> {
        match &mut self.work_onto {
            Task::Done(x) => Ok(x.clone()),
            Task::Todo(x) => {
                if x.clauses() < self.cls_numbr {
                    return Err(SolverError::TooFewClauses);
                }
                x.prepare();
                let solution = if x.clone().solve() {
                    // let mut tmp: Vec<_> = x.guessed.iter_literals().collect();
                    // tmp.sort_by_key(|x| x.abs());
                    Solution::Satisfiable(vec![])
                } else {
                    Solution::Unsatisfiable
                };

                dbg!("Attempting to solve..");

                self.work_onto = Task::Done(solution.clone());
                return Ok(solution);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Solution {
    Satisfiable(Vec<isize>),
    Unsatisfiable,
}

pub struct Solver {
    allocator: *mut StacklikeAlloc,
    var_numbr: usize,
    cls_numbr: usize,
    work_onto: Task<Problem<&'static StacklikeAlloc>, Solution>,
}

enum Task<A, B> {
    Todo(A),
    Done(B),
}

#[derive(Debug)]
pub enum SolverError {
    VariableIsZero,
    VariableTooLarge(isize),
    TooManyClauses,
    TooFewClauses,
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe {
            let _ = Box::from_raw(self.allocator);
        }
    }
}
