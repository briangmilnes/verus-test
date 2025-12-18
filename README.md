# ⚠️ OBSOLETE — See New Project

This project has been superseded by **[verus-proof-time-testing](https://github.com/briangmilnes/verus-proof-time-testing)**.

The new project provides:
- A cleaner setup for Verus proof-time testing using `test_verify_one_file!` macro
- Both runtime tests (`cargo test`) and proof tests (Verus verification)
- Better documentation and a script to run all steps
- Example modules: `minmax.rs` and `set_x.rs` with iterators and macros

## Migration

```bash
git clone https://github.com/briangmilnes/verus-proof-time-testing.git
cd verus-proof-time-testing
./scripts/walkthesteps.sh
```

---

# verus-test (ARCHIVED)

<details>
<summary>Original README (click to expand)</summary>

Experiment project to test runtime testing of Verus-verified code.

## Key Discovery

Code wrapped in `verus!` macros **can compile and test with standard cargo** by:

1. Adding dependencies from a local Verus installation
2. Setting `RUSTC_BOOTSTRAP=1` to enable unstable Rust features
3. Using `#[cfg(verus_keep_ghost)]` for Verus-specific code

## Dependencies

```toml
[dependencies]
verus_builtin_macros = { path = "/home/milnes/projects/verus-lang/source/builtin_macros" }
verus_builtin = { path = "/home/milnes/projects/verus-lang/source/builtin" }
vstd = { path = "/home/milnes/projects/verus-lang/source/vstd", features = ["alloc", "std"] }

[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ['cfg(verus_keep_ghost)'] }
```

## RUSTC_BOOTSTRAP=1

As noted by Travis Hance (Verus developer):

> Verus should automatically opt you into unstable features (i.e., when you invoke the verus binary). 
> If you need to run cargo or rustc without Verus, you can set the environment variable `RUSTC_BOOTSTRAP=1` 
> (this is like a secret flag that mostly exists for rustc internal processes, but it's also what Verus uses 
> to enable unstable features).

This allows the same code to:
1. **Verify with Verus**: `verus --crate-type=lib src/lib.rs`
2. **Compile with cargo**: `RUSTC_BOOTSTRAP=1 cargo build`
3. **Test with cargo**: `RUSTC_BOOTSTRAP=1 cargo test`

## Conditional Compilation Patterns

### Pattern 1: Verus-specific imports

Some `vstd` modules are only available during Verus verification:

```rust
#[cfg(verus_keep_ghost)]
use vstd::std_specs::clone::*;

#[cfg(verus_keep_ghost)]
use vstd::pervasive::strictly_cloned;

#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;
```

### Pattern 2: Verus-specific attributes

Use `cfg_attr` for attributes that only exist in Verus:

```rust
// This attribute only applies during Verus verification
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
while condition {
    // loop body
}
```

### Pattern 3: Module-level conditional compilation

For modules with heavy Verus-specific code, wrap the entire module:

```rust
#[cfg(verus_keep_ghost)]
pub mod feq {
    use vstd::prelude::*;
    use vstd::std_specs::cmp::PartialEqSpec;
    use core::marker::PointeeSized;

    verus! {
        // Full Verus implementation with specs
        pub fn feq<T: Eq + View>(x: &T, y: &T) -> (eq: bool)
            requires obeys_feq_full::<T>(),
            ensures eq <==> x@ == y@,
        { *x == *y }
    }
}

#[cfg(not(verus_keep_ghost))]
pub mod feq {
    // Stub for standard Rust compilation
    pub fn feq<T: Eq>(x: &T, y: &T) -> bool { *x == *y }
}
```

### Pattern 4: Iterator implementations

Verus uses custom iterator patterns. Add standard `Iterator` impls for cargo tests:

```rust
// Inside verus! block - custom iterator struct
pub struct SetStEphIter<'a, T> {
    inner: std::collections::hash_set::Iter<'a, T>,
}

// Outside verus! block - standard Iterator impl for cargo
impl<'a, T: StT + Hash> std::iter::Iterator for SetStEphIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}
```

## Running

```bash
# Verify with Verus
cd ~/projects/verus-test
~/projects/verus-lang/source/target-verus/release/verus --crate-type=lib src/lib.rs

# Build with cargo
RUSTC_BOOTSTRAP=1 cargo build

# Test with cargo
RUSTC_BOOTSTRAP=1 cargo test
```

</details>
