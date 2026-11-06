pub mod ast;
pub mod borrowck;
pub mod c_abi;
pub mod cli;
pub mod drop;
pub mod fasthash;
pub mod fmt;
pub mod frontend;
pub mod ir;
pub mod lexer;
pub mod llvm;
pub mod lower;
pub mod packages;
pub mod parser;
pub mod sha256;
pub mod stdlib;
pub mod testing;
pub mod vm;
pub mod wide;

#[cfg(test)]
mod tests;
