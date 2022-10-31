//! Simple command that prints one or '-n count' UUIDv7 strings

use std::{env, io, io::Write, process};

fn main() -> io::Result<()> {
    let count = match parse_args() {
        Ok(count) => count.unwrap_or(1),
        Err(message) => {
            eprintln!("Error: {}", message);
            eprintln!("Usage: uuid7 [-n count]");
            process::exit(1)
        }
    };

    let mut buf = io::BufWriter::new(io::stdout());
    for _ in 0..count {
        writeln!(buf, "{}", uuid7::uuid7())?;
    }

    Ok(())
}

fn parse_args() -> Result<Option<usize>, String> {
    let mut count = None;

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        if arg != "-n" {
            return Err(format!("unrecognized argument '{}'", arg));
        }
        if count.is_some() {
            return Err("option 'n' given more than once".to_owned());
        }
        if let Some(n_arg) = args.next() {
            if let Ok(c) = n_arg.parse() {
                count.replace(c);
            } else {
                return Err(format!("invalid argument to option 'n': '{}'", n_arg));
            }
        } else {
            return Err("argument to option 'n' missing".to_owned());
        }
    }

    Ok(count)
}
