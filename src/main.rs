use sat_solver::solver::Solver;
use std::io;
use std::time::Instant;

fn parse_numbers(line: &str) -> Result<Vec<isize>, String> {
    line.trim()
        .split_whitespace()
        .map(|x| match str::parse::<isize>(x) {
            Ok(x) => Ok(x),
            _ => Err(x.to_string()),
        })
        .collect()
}

enum HeaderParseError {
    MissingHeader,
    NegativeNumber(isize),
    NotANumber(String),
}

fn parse_header(line: String) -> Result<Header, HeaderParseError> {
    if !line.starts_with("p cnf") {
        return Err(HeaderParseError::MissingHeader);
    }
    let nums = match parse_numbers(&line["p cnf".len()..]) {
        Ok(x) => x,
        Err(x) => return Err(HeaderParseError::NotANumber(x)),
    };

    if let Some(&x) = nums.iter().find(|&&x| x < 0) {
        return Err(HeaderParseError::NegativeNumber(x));
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
            Err(HeaderParseError::MissingHeader) => {
                return Ok(println!("Input must start with a header."));
            }
            Err(HeaderParseError::NegativeNumber(x)) => {
                return Ok(println!(
                    "Number({x}) of variables and clauses must not be negative."
                ));
            }
            Err(HeaderParseError::NotANumber(x)) => {
                return Ok(println!("Input of '{}' is no integer.", x));
            }
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
