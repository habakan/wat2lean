# wat2lean

`wat2lean` is a Rust command-line tool that parses a WebAssembly text module and emits one function as Lean source.

```sh
cargo run -- module.wat 37 functionName
```

The function index is zero-based among the module's defined function bodies, matching the code-section index accepted by `WasmCode.codeBody`. Optional `line:name` arguments name a block, loop, or if-then body. Line numbers start at one on the first line after the function header.

The current output targets the `WasmCode` Lean API and expects `open Instr`. Lean checks the generated function term against the function decoded from the original WebAssembly bytes; this equality check is the correctness boundary.

The translator reports an error for instructions and block types outside the current `WasmCode.Syntax` subset. It supports structured control flow, branches, calls, locals and globals, selected i32/i64 arithmetic, memory operations, and conversions represented by `WasmCode.Instr`.
