//! `slop fmt`: lays out SlopLang source the way std and the examples are written, changing only
//! whitespace outside strings and comments.
//!
//! - A line is indented four spaces for each earlier line that opened a bracket still open (so
//!   `f(a, |x| {` opens one level, not two), and a line that starts by closing brackets lines up
//!   with the line that opened them.
//! - A line continuing a condition (starting with `&&` or `||`) is one level deeper.
//! - Tabs become spaces, trailing whitespace goes, blank lines collapse to one, and the file ends
//!   with one newline.
//!
//! What is inside a string, including one spanning lines, and what follows `//` is left as it is.
//! [`format_checked`] also lexes both versions and refuses a result whose tokens differ, so a
//! mistake here cannot change what a program means.

use crate::frontend::SurfaceLexer;

/// `src` laid out; see the module documentation.
pub fn format_source(src: &str) -> String {
    let mut out: Vec<String> = Vec::new();
    // The line each open bracket was opened on, innermost last, and each line's indent level.
    let mut open: Vec<usize> = Vec::new();
    let mut indent_of: Vec<usize> = Vec::new();
    let mut in_str = false;
    let mut blank_run = 0;
    for (li, raw) in src.split('\n').enumerate() {
        let starts_in_str = in_str;
        let mut level = 0;
        if starts_in_str {
            // Inside a string: the line is part of its value.
            out.push(raw.to_string());
        } else {
            let line = raw.replace('\t', "    ");
            let body = line.trim();
            if body.is_empty() {
                blank_run += 1;
                if blank_run == 1 {
                    out.push(String::new());
                }
            } else {
                blank_run = 0;
                let closers = body.chars().take_while(|c| matches!(c, ')' | ']' | '}')).count();
                level = if closers > 0 && closers <= open.len() {
                    indent_of[open[open.len() - closers]]
                } else {
                    let mut lines: Vec<usize> = open.clone();
                    lines.dedup();
                    lines.len()
                };
                // A continued condition is one deeper, but what it opens closes at its statement.
                let shown = level + usize::from(closers == 0 && (body.starts_with("&&") || body.starts_with("||")));
                out.push(format!("{}{body}", "    ".repeat(shown)));
            }
        }
        indent_of.push(level);
        scan_brackets(raw, li, &mut open, &mut in_str);
    }
    while out.last().is_some_and(String::is_empty) {
        out.pop();
    }
    let mut text = out.join("\n");
    text.push('\n');
    text
}

/// Follows `line`'s brackets, strings, runes, and comments, updating `open` and `in_str`.
fn scan_brackets(line: &str, li: usize, open: &mut Vec<usize>, in_str: &mut bool) {
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if *in_str {
            match c {
                '\\' => i += 1,
                '"' => *in_str = false,
                _ => {}
            }
            i += 1;
            continue;
        }
        match c {
            '/' if chars.get(i + 1) == Some(&'/') => return,
            '"' => *in_str = true,
            // A rune literal: `'{'`, `'\''`, `'\u{7b}'`.
            '\'' => {
                let mut j = i + 1;
                if chars.get(j) == Some(&'\\') {
                    j += 2;
                    while j < chars.len() && chars[j] != '\'' {
                        j += 1;
                    }
                } else {
                    j += 1;
                }
                if chars.get(j) == Some(&'\'') {
                    i = j;
                }
            }
            '(' | '[' | '{' => open.push(li),
            ')' | ']' | '}' => {
                open.pop();
            }
            _ => {}
        }
        i += 1;
    }
}

/// [`format_source`], refused if the result does not lex to the same tokens as `src` (or if
/// `src` does not lex at all).
pub fn format_checked(src: &str) -> Result<String, String> {
    let formatted = format_source(src);
    let kinds = |s: &str| -> Result<Vec<String>, String> {
        Ok(SurfaceLexer::new(s).tokenize()?.into_iter().map(|t| format!("{:?}", t.kind)).collect())
    };
    if kinds(src)? != kinds(&formatted)? {
        return Err("formatting would change the program's tokens, so it was not done; this is a bug in 'slop fmt'".to_string());
    }
    Ok(formatted)
}

#[test]
fn std_and_the_examples_are_formatted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    for dir in ["lib/core", "lib/std", "examples", "examples/ledger/src"] {
        for entry in std::fs::read_dir(root.join(dir)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|e| e == "slop") {
                files.push(path);
            }
        }
    }
    assert!(files.len() > 20, "{files:?}");
    for path in files {
        let src = std::fs::read_to_string(&path).unwrap();
        let formatted = format_checked(&src).unwrap();
        assert!(formatted == src, "{} is not formatted; run 'slop fmt' on it", path.display());
        assert_eq!(format_source(&formatted), formatted, "{} formats differently twice", path.display());
    }
}

#[test]
fn messy_source_is_laid_out() {
    let messy = "fn f() -> i32 {\nlet x = g(1,\n2);\n      if x > 0\n&& x < 9 {\n\t\treturn 1;   \n}\n\n\n\n  let s = \"a {\n   b\";\n  return h(fn(k: i32) {\n  return k;\n}, '{');\n}\n\n\n";
    let want = "fn f() -> i32 {\n    let x = g(1,\n        2);\n    if x > 0\n        && x < 9 {\n        return 1;\n    }\n\n    let s = \"a {\n   b\";\n    return h(fn(k: i32) {\n        return k;\n    }, '{');\n}\n";
    assert_eq!(format_checked(messy).unwrap(), want);
    assert_eq!(format_source(want), want);
}
