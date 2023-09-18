//! Simple command that prints one or '-n count' UUIDv7 strings

use std::{env, io, io::Write, process::ExitCode};

fn main() -> io::Result<ExitCode> {
    let count = {
        let mut args = env::args();
        let program = args.next();
        match parse_args(args) {
            Ok(opt) => opt.unwrap_or(1),
            Err(message) => {
                eprintln!("Error: {}", message);
                eprintln!(
                    "Usage: {} [-n count]",
                    program.as_deref().unwrap_or("uuid7")
                );
                return Ok(ExitCode::FAILURE);
            }
        }
    };

    let mut buf = io::BufWriter::new(io::stdout());
    for _ in 0..count {
        writeln!(buf, "{}", uuid7::uuid7())?;
    }

    Ok(ExitCode::SUCCESS)
}

fn parse_args(mut args: impl Iterator<Item = String>) -> Result<Option<usize>, String> {
    let mut count = None;
    while let Some(arg) = args.next() {
        if arg != "-n" {
            return Err(format!("unrecognized argument '{}'", arg));
        }
        if count.is_some() {
            return Err("option 'n' given more than once".to_owned());
        }
        let Some(n_arg) = args.next() else {
            return Err("argument to option 'n' missing".to_owned());
        };
        let Ok(c) = n_arg.parse() else {
            return Err(format!("invalid argument to option 'n': '{}'", n_arg));
        };
        count.replace(c);
    }
    Ok(count)
}
