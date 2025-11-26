//! Copyright (C) 2025 Acar, Blelloch and Milnes from 'Algorithms Parallel and Sequential'.
//! Chapter 3 insertion sort over mutable slices.

use vstd::prelude::*;

verus! {

pub mod InsertionSortStEph {
    use verus_builtin::SpecOrd;
    pub type T<S> = [S];

    pub trait InsertionSortStTrait<T: Ord + Clone> {
        /// APAS: Work O(n²), Span O(n log n)
        fn insSort(slice: &mut [T]);
    }

    impl<T: Ord + Clone> InsertionSortStTrait<T> for T {
        fn insSort(slice: &mut [T]) {
            for i in 1..slice.len() {
                let key = slice[i].clone();
                let mut j = i;
                while j > 0 && slice[j - 1] > key
                    invariant
                        j <= i,
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

