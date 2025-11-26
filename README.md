# verus-test

Experiment project to test runtime testing of Verus-verified code.

## Key Discovery

Code wrapped in `verus!` macros **can compile and test with standard cargo** by adding these dependencies from a local Verus installation:

```toml
[dependencies]
verus_builtin_macros = { path = "/home/milnes/projects/verus-lang/source/builtin_macros" }
verus_builtin = { path = "/home/milnes/projects/verus-lang/source/builtin" }
vstd = { path = "/home/milnes/projects/verus-lang/source/vstd", default-features = false }
```

## How It Works

The `verus_builtin_macros` crate provides the `verus!` macro. When compiled without Verus verification (i.e., with standard `cargo`), the macro:
- Passes through executable Rust code
- Strips out spec-only constructs (`requires`, `ensures`, `invariant`, `decreases`, etc.)

This means the same code can:
1. **Verify with Verus**: `verus --crate-type=lib src/lib.rs`
2. **Compile with cargo**: `cargo build`
3. **Test with cargo**: `cargo test`

## Example

```rust
use vstd::prelude::*;

verus! {
    fn insSort(slice: &mut [T]) {
        for i in 1..slice.len() {
            let key = slice[i].clone();
            let mut j = i;
            while j > 0 && slice[j - 1] > key
                invariant j <= i,
                decreases j,
            {
                slice[j] = slice[j - 1].clone();
                j -= 1;
            }
            slice[j] = key;
        }
    }
}
```

The `invariant` and `decreases` clauses are used by Verus for verification but stripped out by `cargo`.

## Notes

- Verus verification may require additional invariants/proofs that cargo ignores
- Some Verus features (like `#[verifier::...]` attributes) may still need conditional compilation
- The `vstd` import (`use vstd::prelude::*`) works because `vstd` is a dependency
