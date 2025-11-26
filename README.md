# verus-test

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

## Example: Verified Insertion Sort

```rust
use vstd::prelude::*;

verus! {

pub mod InsertionSortStEph {
    pub trait InsertionSortStTrait<T: Ord + Clone> {
        fn insSort(slice: &mut [T]);
    }

    impl<T: Ord + Clone> InsertionSortStTrait<T> for T {
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
}

} // verus!
```

The `invariant` and `decreases` clauses are used by Verus for verification but stripped out by cargo.

## Example: Testing Verified Code

```rust
use verus_test::Chap03::InsertionSortStEph::InsertionSortStEph::*;

#[test]
fn insertion_sort_reverse_order() {
    let mut data = vec![5, 4, 3, 2, 1];
    i32::insSort(&mut data);
    assert_eq!(data, vec![1, 2, 3, 4, 5]);
}

#[test]
fn insertion_sort_large_input_stress_test() {
    let mut data = (0..10_000).rev().collect::<Vec<i32>>();
    let mut expected = data.clone();
    expected.sort();
    
    i32::insSort(&mut data);
    assert_eq!(data, expected);
}
```

## Example: Verified Set with Macros

```rust
use verus_test::Chap05::SetStEph::SetStEph::*;
use verus_test::{SetLit, PairLit};
use verus_test::Types::Types::*;

#[test]
fn test_set_operations() {
    let s1 = SetLit![1, 2, 3];
    let s2 = SetLit![2, 3, 4];
    
    let union = s1.union(&s2);
    assert_eq!(union.size(), 4);
    
    let intersection = s1.intersection(&s2);
    assert_eq!(intersection.size(), 2);
    assert!(intersection.mem(&2));
    assert!(intersection.mem(&3));
}

#[test]
fn test_cartesian_product() {
    let a = SetLit![1, 2];
    let b = SetLit!["x", "y"];
    
    let product = a.cartesian_product(&b);
    assert_eq!(product.size(), 4);
    assert!(product.mem(&PairLit!(1, "x")));
    assert!(product.mem(&PairLit!(2, "y")));
}
```

## Example: Verified Mapping

```rust
use verus_test::Chap05::MappingStEph::MappingStEph::*;
use verus_test::{MappingLit, PairLit};
use verus_test::Types::Types::*;

#[test]
fn test_mapping_basic() {
    let m = MappingLit![(1, "one"), (2, "two"), (3, "three")];
    
    assert_eq!(m.size(), 3);
    assert!(m.mem(&Pair(1, "one")));
    assert!(m.mem(&Pair(2, "two")));
    assert!(!m.mem(&Pair(1, "wrong")));
}

#[test]
fn test_mapping_domain_range() {
    let m = MappingLit![("a", 1), ("b", 2), ("c", 1)];
    
    let domain = m.domain();
    assert_eq!(domain.size(), 3);
    assert!(domain.mem(&"a"));
    
    let range = m.range();
    assert_eq!(range.size(), 2);  // 1 and 2 (duplicates removed)
    assert!(range.mem(&1));
    assert!(range.mem(&2));
}

#[test]
#[should_panic(expected = "MappingLit!: duplicate domain element")]
fn test_mapping_rejects_duplicates() {
    // Mappings are functions - no duplicate keys allowed
    let _m = MappingLit![(1, "first"), (2, "two"), (1, "second")];
}
```

## Project Structure

```
verus-test/
├── src/
│   ├── lib.rs
│   ├── Types.rs              # Common types (Pair, StT trait)
│   ├── Chap03/
│   │   └── InsertionSortStEph.rs
│   ├── Chap05/
│   │   ├── SetStEph.rs       # Verified ephemeral set
│   │   ├── RelationStEph.rs  # Verified ephemeral relation
│   │   └── MappingStEph.rs   # Verified ephemeral mapping (function)
│   └── vstdplus/             # Extensions to vstd
│       ├── feq.rs            # Full equality specs
│       ├── seq_set.rs        # Sequence/set utilities
│       └── ...
├── tests/
│   ├── Chap03/
│   │   └── TestInsertionSortStEph.rs
│   └── Chap05/
│       ├── TestSetStEph.rs
│       ├── TestRelationStEph.rs
│       └── TestMappingStEph.rs
└── Cargo.toml
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

# Test with nextest (faster)
RUSTC_BOOTSTRAP=1 cargo nextest run
```

## Current Test Results

```
running 73 tests
- Chap03: 7 tests (InsertionSort)
- Chap05: 66 tests (SetStEph, RelationStEph, MappingStEph)

test result: ok. 73 passed; 0 failed
```

## Notes

- Verus verification may require additional invariants/proofs that cargo ignores
- The `vstd` crate requires `features = ["alloc", "std"]` for hash set support
- Use `check-cfg` in `Cargo.toml` to silence warnings about `verus_keep_ghost`
- For complex Verus-specific code, prefer module-level `#[cfg(verus_keep_ghost)]` wrapping
