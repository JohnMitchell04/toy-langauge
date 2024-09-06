# C-Like Language Compiler (WIP)

This project is an educational endeavor to build a compiler for a C-like language, targeting LLVM Intermediate Representation (IR). The goal is to generate LLVM IR code that can be linked and compiled using tools like Clang. While still a work in progress, some sample code can be found within the test cases. Once the compiler reaches a more stable state, a dedicated folder of examples will be provided.

## Project Structure

The compiler is currently divided into four core modules:

1. **Lexer**: Breaks down the input source code into a sequence of tokens, each representing meaningful components like keywords, operators, and identifiers
2. **Parser**: Takes the tokens from the lexer and produces an abstract syntax tree (AST) by adhering to the language's grammar. The grammar is explained within the function-level documentation.
3. **Resolver**: Ensures all variable declarations and accesses are valid. When types are fully implemented, the resolver will also enforce type correctness.
4. **Compiler**: Utilizes [Inkwell](https://thedan64.github.io/inkwell/inkwell/index.html), a Rust-based LLVM binding, to produce efficient LLVM IR, which can be further processed by LLVM-based tools like Clang.

In addition, the project includes a `main` file that leverages [Clap](https://docs.rs/clap/latest/clap/) to offer a high-quality, interactive command-line interface (CLI).

## Roadmap

- **Standard library**: A standard library allowing simple input and output.
- **Type System**: Future updates will focus on expanding the resolver to include type inference and checking.
- **Examples**: Once the compiler stabilizes, a collection of example programs will be included.
- **Arrays**: Simple static arrays that the user can leverage.
- **Structs**: As well as dynamically sized types like arrays.
- **Optimization**: As the project matures, optimization passes may be added to improve the efficiency of the generated LLVM IR.
