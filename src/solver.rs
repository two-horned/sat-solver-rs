use crate::alloc::PoolAlloc;
use crate::data::{create_clause_blocks, Clause};
use crate::utils::*;
use core::cmp::Reverse;
use core::usize;
use rand::prelude::*;

fn prepare(clauses: &mut Vec<Clause>) {
    clauses.retain(|x| x.disjoint_switched_self());
    clauses.sort_by_key(Clause::elements);
}

fn remove_pure_literals(clauses: &mut Vec<Clause>) {
    if clauses.len() == 0 {
        return;
    }
    let mut acc = clauses[0].clone();
    for i in 1..clauses.len() {
        acc.unsafe_zip_clause_in(&clauses[i], |x, y| *x |= y);
    }
    let pure_literals = acc.difference_switched_self();
    clauses.retain(|x| pure_literals.disjoint(x));
}

fn remove_long_clauses(clauses: &mut Vec<Clause>) {
    while let Some(last) = clauses.last_mut() {
        if last.elements() >= clauses.len() {
            clauses.pop();
        } else {
            return;
        }
    }
}

fn remove_rarest_literal(clauses: &mut Vec<Clause>, a: &PoolAlloc) -> bool {
    fn fix_clause(clauses: &mut Vec<Clause>, k: usize) {
        if clauses[k].disjoint_switched_self() {
            clauses.ascend(k);
        } else {
            clauses.remove(k);
        }
    }

    fn work_once(literal: isize, clauses: &mut Vec<Clause>) {
        let k = clauses.iter().position(|x| x.read(literal)).unwrap();
        let mut c = clauses.remove(k);
        c.unset(literal);

        let to_modify: Box<[usize]> = clauses
            .iter()
            .enumerate()
            .filter_map(|(i, x)| if x.read(-literal) { Some(i) } else { None })
            .rev()
            .collect();

        for i in to_modify {
            clauses[i].unset(-literal);
            clauses[i].unsafe_zip_clause_in(&c, |x, y| *x |= y);
            fix_clause(clauses, i);
        }
    }

    fn work_twice(literal: isize, clauses: &mut Vec<Clause>) {
        let mut a: [usize; 4] = [0; 4];
        a[0] = clauses.iter().position(|x| x.read(literal)).unwrap();
        a[1] = clauses
            .iter()
            .skip(a[0])
            .position(|x| x.read(literal))
            .unwrap();
        a[2] = clauses.iter().position(|x| x.read(-literal)).unwrap();
        a[3] = clauses
            .iter()
            .skip(a[2])
            .position(|x| x.read(-literal))
            .unwrap();

        for i in 0..2 {
            clauses[i].unset(literal);
            clauses[i + 2].unset(-literal);
        }

        let copies: [Clause; 4] = {
            let u = clauses[a[0]].clone();
            let v = clauses[a[1]].clone();
            let w = clauses[a[2]].clone();
            let x = clauses[a[3]].clone();
            [u, v, w, x]
        };

        for i in 0..2 {
            clauses[i].unsafe_zip_clause_in(&copies[i + 1], |x, y| *x |= y);
            clauses[i + 1].unsafe_zip_clause_in(&copies[i ^ 1], |x, y| *x |= y);
        }

        a.sort_by_key(|x| Reverse(*x));
        a.iter().for_each(|&i| fix_clause(clauses, i));
    }

    if 0 == clauses.len() {
        return false;
    }
    let len = clauses[0].content_length();

    let mut once = create_clause_blocks(len, a);
    let mut twice = create_clause_blocks(len, a);
    let mut thrice = create_clause_blocks(len, a);

    for clause in &mut *clauses {
        once.unsafe_zip_clause_in(&clause, |x, y| *x |= y);
        twice.unsafe_zip3_clause_in(&clause, &once, |x, y, z| *x |= y & z);
        thrice.unsafe_zip3_clause_in(&clause, &twice, |x, y, z| *x |= y & z);
    }
    once.unsafe_zip3_clause_in(&twice, &thrice, |x, y, z| *x &= !(y | z));
    twice.unsafe_zip_clause_in(&thrice, |x, y| *x &= !y);

    match once.iter_literals().next() {
        None => (),
        Some(x) => {
            work_once(x, clauses);
            return true;
        }
    }

    while let Some(x) = twice.iter_literals().next() {
        if twice.read(-x) {
            work_twice(x, clauses);
            return true;
        }
    }

    false
}

fn resolve(literal: isize, clauses: &mut Vec<Clause>) {
    clauses.retain(|x| !x.read(literal));
    for i in 0..clauses.len() {
        let x = &mut clauses[i];
        if x.read(-literal) {
            x.unset(-literal);
            clauses.descend(i);
        }
    }
}

fn subjugate(clauses: &mut Vec<Clause>, k: usize) {
    /* Subjugate */
    let current = clauses[k].clone();
    clauses.retain_from(|x: &Clause| !current.subset_of(x), k + 1);

    /* Symmetry ellimination */
    let mut i = k + 1;
    while i < clauses.len() {
        let other = &mut clauses[i];
        let (badness, control) = {
            let mut difference = current.unsafe_iter_differences(other).take(2);
            (difference.next(), difference.next())
        };

        if badness.is_some() && control.is_none() {
            let badness = badness.unwrap();
            other.unset(-badness);
            let mut j = clauses.descend(i);
            if j < k {
                if clauses[j] >= current {
                    while j < k {
                        clauses.swap(j, j + 1);
                        j += 1;
                    }
                } else {
                    subjugate(clauses, j);
                }
            }
        }
        i += 1
    }
}

fn combine(clauses: &mut Vec<Clause>) {
    let mut k = 0;
    while k + 1 < clauses.len() {
        subjugate(clauses, k);
        k += 1;
    }
}

fn components(mut clauses: Vec<Clause>) -> Vec<Vec<Clause>> {
    let mut v = Vec::with_capacity(clauses.len());
    let mut e = Vec::with_capacity(clauses.len());

    while let Some(x) = clauses.pop() {
        let mut w = Vec::with_capacity(clauses.len());
        let mut r = x.variables();
        w.push(x.clone());
        loop {
            e.clear();
            clauses.extract_in(&mut e, |x| x.unsafe_has_variables(&r));
            if e.is_empty() {
                break;
            }
            e.iter().for_each(|x| x.unsafe_enrich_variables(&mut r));
            w.extend_from_slice(&e);
        }
        w.sort_by_key(Clause::elements);
        v.push(w);
    }
    v.sort_by(|x, y| usize::cmp(&x.len(), &y.len()));
    v
}

fn kernelize(clauses: &mut Vec<Clause>, a: &PoolAlloc) {
    loop {
        combine(clauses);
        loop {
            let old_length = clauses.len();
            remove_long_clauses(clauses);
            remove_pure_literals(clauses);
            if old_length != clauses.len() {
                continue;
            }
            break;
        }
        if remove_rarest_literal(clauses, a) {
            continue;
        }
        break;
    }
}

fn choice(clauses: &Vec<Clause>) -> Option<isize> {
    let literals: Vec<isize> = clauses[0].iter_literals().collect();
    literals.choose(&mut rand::rng()).copied()
}

fn guess<'a>(clauses: Vec<Clause>, conflicts: &mut Clause, a: &'a PoolAlloc) -> bool {
    if clauses.is_empty() {
        return true;
    }
    if clauses[0].is_null() {
        false;
    }

    let comps = components(clauses);
    for mut c in comps {
        match choice(&c) {
            None => return false,
            Some(x) => {
                resolve(x, &mut c);
                kernelize(&mut c, a);
                conflicts.set(-x);

                match guess(c, conflicts, a) {
                    false => return false,
                    true => conflicts.unset(-x),
                }
            }
        }
    }
    true
}

pub fn solve_problem<'a>(mut clauses: Vec<Clause<'a>>, a: &'a PoolAlloc) -> bool {
    let mut wrong_guesses = 0;
    if clauses.len() == 0 {
        return true;
    };
    let len = clauses[0].content_length();
    prepare(&mut clauses);
    loop {
        kernelize(&mut clauses, a);
        let mut conflicts = create_clause_blocks(len, a);
        let res = guess(clauses.clone(), &mut conflicts, a);
        match res {
            true => {
                println!("Wrong guesses: {}", wrong_guesses);
                return true;
            }
            false => {
                wrong_guesses += 1;
                if conflicts.is_null() {
                    println!("Wrong guesses: {}", wrong_guesses);
                    return false;
                }
                clauses.push(conflicts);
                clauses.descend(clauses.len() - 1);
            }
        }
    }
}

//  fn guess(mut clauses: Vec<Clause>, a: &PoolAlloc) -> bool {
//      kernelize(&mut clauses, a);
//      if clauses.is_empty() {
//          return true;
//      }
//      let comps = components(clauses);
//      //println!("Length of components is {}", comps.len());

//      for mut c in comps {
//          let v = choice(&c);
//          match v {
//              None => return false,
//              Some(x) => {
//                  let mut d = c.clone();
//                  resolve(x, &mut c);
//                  if guess(c, a) {
//                      continue;
//                  }
//                  resolve(-x, &mut d);
//                  if !guess(d, a) {
//                      return false;
//                  }
//              }
//          }
//      }
//      true
//  }

//  pub fn solve_problem(mut clauses: Vec<Clause>, a: &PoolAlloc) -> bool {
//      prepare(&mut clauses);
//      guess(clauses, a)
//  }
