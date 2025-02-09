use sat_solver::alloc::PoolAlloc;
use sat_solver::data::{blocks_needed, create_clause_blocks, ParseProblemError};
use sat_solver::solver::solve_problem;
use std::alloc::Layout;
use std::{io, time::Instant};

fn parse_numbers(line: &str) -> Result<Vec<isize>, ParseProblemError> {
    line.trim()
        .split_whitespace()
        .map(|x| str::parse::<isize>(x).map_err(|_| ParseProblemError::NotANumber(x.to_string())))
        .collect()
}

fn parse_header(line: String) -> Result<Header, ParseProblemError> {
    if !line.starts_with("p cnf") {
        return Err(ParseProblemError::MissingHeader);
    }
    let nums = parse_numbers(&line["p cnf".len()..])?;
    if nums.iter().any(|&x| x < 0) {
        return Err(ParseProblemError::NegativeNumber(line));
    }
    Ok(Header {
        vrs: nums[0] as usize,
        cls: nums[1] as usize,
    })
}

fn main() -> io::Result<()> {
    println!("Enter satisfiability problem in DIMACS format.");
    println!("Press Ctrl-D to quit.");

    let mut h = None;

    for line in io::stdin().lines() {
        let e = line?;
        if e.starts_with("c") {
            continue;
        }
        if let Ok(x) = parse_header(e) {
            h = Some(x);
            break;
        } else {
            return Ok(println!("Incorrect header received."));
        }
    }

    if let Some(header) = h {
        let len = blocks_needed(header.vrs);
        let layout = unsafe {
            Layout::from_size_align_unchecked(len * size_of::<usize>(), size_of::<usize>())
        };
        //let a = PoolAlloc::from(layout, header.cls * header.vrs).unwrap();
        let a = PoolAlloc::new();
        let mut problem = Vec::new();
        while problem.len() < header.cls {
            let mut clause = create_clause_blocks(len, &a);
            for line in io::stdin().lines() {
                let e = line?;
                if e.is_empty() {
                    return Ok(println!("Empty lines are disallowed."));
                }
                if let Ok(v) = parse_numbers(&e) {
                    if v.iter().any(|&x| header.vrs < x.abs() as usize) {
                        return Ok(println!("Literal out of range."));
                    }
                    if v.iter().take(v.len() - 1).any(|&x| x == 0) {
                        return Ok(println!(
                            "Variables need to have a value greater than zero."
                        ));
                    }

                    if v[v.len() - 1] == 0 {
                        v.iter().take(v.len() - 1).for_each(|&x| clause.set(x));
                        break;
                    } else {
                        v.iter().take(v.len() - 1).for_each(|&x| clause.set(x));
                    }
                } else {
                    return Ok(println!("Incorrect clause formulation."));
                }
            }
            problem.push(clause);
        }

        let start = Instant::now();
        println!("Solving problem...");
        println!("Solution is {}", solve_problem(problem, &a));
        println!("Time spent is {}ms", start.elapsed().as_millis());
        return Ok(println!("Bye."));
    }
    Ok(println!("Abort? Ok..."))
}

struct Header {
    vrs: usize,
    cls: usize,
}
