# Lean FinMap

A Lean 4 library providing efficient finite maps with algebraic operations, built on top of tree-based data structures.

## Overview

`FinMap` provides a sparse representation of finite maps from keys to values, where only non-zero values are stored. This makes it particularly useful for representing sparse data structures like sparse polynomials, sparse matrices, or any mapping where most values are zero.

## Features

- **Sparse Storage**: Only non-zero values are stored in memory.
- **Algebraic Operations**: Support for pointwise algebraic operations, currently onl additive operations.
- **Efficient Access**: O(log n) lookup and update operations.

## Basic Usage

```lean
import FinMap

-- Create an empty map
def empty : FinMap Nat Int := ∅

-- Create a single key-value pair
def single : FinMap Nat Int := FinMap.single 1 2

-- Update a map
def updated : FinMap Nat Int := empty.update 1 2

-- Access values (returns 0 for missing keys)
#eval updated[1]  -- 2
#eval updated[5]  -- 0

-- Algebraic operations
def map1 : FinMap Nat Int := (∅ : FinMap Nat Int).update 1 3
def map2 : FinMap Nat Int := (∅ : FinMap Nat Int).update 1 2

#eval (map1 + map2)[1]  -- 5
#eval (map1 - map2)[1]  -- 1
#eval (-map1)[1]        -- -3
```

## Structure

- `FinMap/Basic.lean` - Core definitions and basic operations
- `FinMap/Algebra.lean` - Algebraic operations (add, sub, neg, smul)
- `FinMap/Support.lean` - The support of a `FinMap`, and related operations
- `FinMap/TreeMapD.lean` - Underlying "tree map with default" implementation
- `FinMap/Std/ExtTreeMap.lean` - Additional functions on the standard library's `ExtTreeMap`

## Building

```bash
lake build
```

## Testing

```bash
lake test
```

## License

Released under Apache 2.0 license as described in the file LICENSE.
