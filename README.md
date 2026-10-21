# wat2lean

`wat2lean` parses a WebAssembly text module (WAT) and emits a selected function body as Lean source. The translator is written in Rust; the repository also contains a Lean library for decoding and executing the supported instruction subset and proving properties about it.

## Requirements

- Rust and Cargo
- Lean 4 and Lake, using the version in `lean-toolchain`

## Translate a function

From the repository root, translate the first defined function in the example module:

```sh
cargo run -- examples/wipe.wat 0 generatedWipeCode
```

The command writes a Lean `def` to standard output. The function index is zero-based among defined function bodies; imported functions are not counted. The third argument is the name to use for the generated definition.

For nested `block` and `loop` bodies, or the then branch of an `if`, you can optionally provide `line:name` arguments to emit those bodies as separate `List Instr` definitions. Line numbers start at one on the first line after the function header. For example:

```sh
cargo run -- module.wat 3 generatedFunction 4 loopBody 9 thenBody
```

The translator reports an error when a function uses instructions or block types outside the current `WasmCode.Syntax` subset. It parses and resolves the WAT module, but emits only the selected function body; it does not generate imports, module metadata, or a specification theorem.

## Check generated Lean code

The example below translates `examples/wipe.wat`, then asks Lean to type-check the result and prove that it is the same function used by the existing wipe specification theorem:

```sh
{
  printf '%s\n' 'import WasmCode.Wipe' 'open WasmCode WasmCode.Instr'
  cargo run -- examples/wipe.wat 0 generatedWipeCode
  printf '%s\n' 'example : generatedWipeCode = WasmCode.Examples.wipeCode := by rfl'
} > /tmp/GeneratedWipe.lean
lake env lean /tmp/GeneratedWipe.lean
```

`lake env lean` should finish without errors. The equality connects the translated function to `WasmCode.Examples.wipeCode`; its behavior is covered by `WasmCode.Examples.wipe_call` in `WasmCode/Wipe.lean`. For example, the theorem states that the function zeroes a valid memory range and preserves the rest of the store. The theorem's assumptions and conclusion are defined in that Lean file.

To build the Lean library and its bundled examples:

```sh
lake build
```

The library contains the binary reader and function-body decoder (`WasmShape.Binary`, `WasmCode.Syntax`), an executable instruction model (`WasmCode.Semantics`), and a stateful runner for memory, globals, and calls (`WasmCode.Machine`).

The model covers an explicit subset of WebAssembly instructions; unsupported instructions fail to decode or trap in the runner. A theorem establishes behavior relative to this model. It does not by itself establish that the model matches every rule in the WebAssembly specification.
