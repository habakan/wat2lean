# wat2lean

`wat2lean` is a Rust command-line tool that parses a WebAssembly text module and emits one function as Lean source.

```sh
cargo run -- module.wat 37 functionName
```

The function index is zero-based among the module's defined function bodies, matching the code-section index accepted by `WasmCode.codeBody`. Optional `line:name` arguments name a block, loop, or if-then body. Line numbers start at one on the first line after the function header.

The translator reports an error for instructions and block types outside the current `WasmCode.Syntax` subset. It supports structured control flow, branches, calls, locals and globals, selected i32/i64 arithmetic, memory operations, and conversions represented by `WasmCode.Instr`.

## Lean verification library

The repository root is also a Lake package. It provides the binary reader and function-body decoder (`WasmShape.Binary`, `WasmCode.Syntax`), an executable instruction model (`WasmCode.Semantics`), and a stateful runner for memory, globals and calls (`WasmCode.Machine`).

```sh
lake build
```

Generated function definitions use the `WasmCode.Func` API. A verification file can start with:

```lean
import WasmCode.Machine
open WasmCode WasmCode.Instr
```

Then connect a generated definition to the shipped binary with a theorem such as `codeBody bytes index = some function`. Prove the specification against the library's execution model.

The model covers an explicit subset of WebAssembly instructions; unsupported instructions fail to decode or trap in the runner. A theorem establishes behavior relative to this model. It does not by itself establish that the model matches every rule in the WebAssembly specification.

## Example

```lean
import WasmCode.Wipe
```

This module contains the `wipeCode` loop and proves `WasmCode.Examples.wipe_call`: for a valid memory range and sufficient fuel, the function zeroes the requested bytes and preserves the rest of the store. A generated function can use this contract after its body is identified with `wipeCode` and matched to the module bytes.
