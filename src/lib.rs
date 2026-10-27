pub mod ast;
pub mod borrowck;
pub mod c_abi;
pub mod drop;
pub mod frontend;
pub mod ir;
pub mod lexer;
pub mod llvm;
pub mod lower;
pub mod parser;
pub mod stdlib;
pub mod vm;
pub mod wide;

#[cfg(test)]
mod tests;
