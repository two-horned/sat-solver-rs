#![feature(allocator_api)]
use std::io;
use std::time::Instant;

use sat_solver::solver::Solver;

use core::str::FromStr;

fn parse_numbers(line: &str) -> Result<Vec<isize>, <isize as FromStr>::Err> {
    line.trim()
        .split_whitespace()
        .map(|x| str::parse::<isize>(x))
        .collect()
}

#[derive(Debug)]
enum HeaderParseError {
    MissingHeader,
    NegativeNumber(String),
    NotANumber,
}

fn parse_header(line: String) -> Result<Header, HeaderParseError> {
    if !line.starts_with("p cnf") {
        return Err(HeaderParseError::MissingHeader);
    }
    let nums = match parse_numbers(&line["p cnf".len()..]) {
        Ok(x) => x,
        Err(_) => return Err(HeaderParseError::NotANumber),
    };
    if nums.iter().any(|&x| x < 0) {
        return Err(HeaderParseError::NegativeNumber(line));
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
        match parse_header(e) {
            Ok(x) => {
                h = Some(x);
                break;
            }
            Err(x) => return Ok(println!("{:?}", x)),
        }
    }

    if let Some(header) = h {
        let mut solver = Solver::new(header.vrs, header.cls);

        while solver.need_to_add() {
            let mut literals = Vec::new();
            for line in io::stdin().lines() {
                let e = line?;
                if e.is_empty() {
                    return Ok(println!("Empty lines are disallowed."));
                }
                if let Ok(mut v) = parse_numbers(&e) {
                    if v[v.len() - 1] == 0 {
                        v.pop();
                        literals.extend(v);
                        break;
                    } else {
                        literals.extend(v);
                    }
                } else {
                    return Ok(println!("Incorrect clause formulation."));
                }
            }

            match solver.add_clause(literals) {
                Err(x) => return Ok(println!("{:?}", x)),
                _ => (),
            }
        }
        let start = Instant::now();
        println!("Solving problem...");
        println!("Solution is {:?}", solver.solve());
        println!("Time spent is {}ms", start.elapsed().as_millis());
        return Ok(println!("Bye."));
    }
    Ok(println!("Abort? Ok..."))
}

struct Header {
    vrs: usize,
    cls: usize,
}
