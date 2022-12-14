use rustyline::{Editor, Result};
use rustyline::validate::MatchingBracketValidator;
use rustyline_derive::{Completer, Helper, Highlighter, Hinter, Validator};
use crate::eval::Evaluator;

pub mod builtins;
pub mod eval;
pub mod memory;
pub mod reader;
pub mod value;

#[derive(Completer, Helper, Highlighter, Hinter, Validator)]
struct InputValidator {
    #[rustyline(Validator)]
    brackets: MatchingBracketValidator,
}

fn main() -> Result<()> {
    println!("Welcome to Scheme (sort of)");
    let mut editor = Editor::new()?;
    let helper = InputValidator {
        brackets: MatchingBracketValidator::new()
    };
    editor.set_helper(Some(helper));
    let mut scheme = Evaluator::new();
    loop {
        let result = editor.readline("> ");
        match result {
            Ok(line) => {
                editor.add_history_entry(&line);
                match reader::read(&line, &mut scheme.memory) {
                    Err(err) => {
                        println!("{}", err)
                    }
                    Ok(expr) => {
                        match scheme.evaluate(&expr) {
                            Ok(value) => println!("{}", value),
                            Err(err) => println!("{}", err)
                        }
                    }
                }
            }
            _ => break
        }
    }
    println!("Bye.");
    Ok(())
}
