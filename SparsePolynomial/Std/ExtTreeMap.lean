/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Std.Data.ExtTreeMap
import SparsePolynomial.Std.TreeMap

/-! # Std.ExtTreeMap.mergeWithAll -/

open Std

namespace Std.ExtTreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp]

/--
Combines two extensional tree maps, using a function `f : α → Option β → Option β → Option β` to combine the values.

The function `f` is used to combine the values of the two tree maps.
For each key present in either map, `f` is called with the key, and the values, if present, from both maps.
If `f` returns `some b`, then `b` is inserted into the result.

**Implementation note**: this is an inefficient implementation: a good implementation will be possible once we have iterators for maps.
-/
def mergeWithAll (m₁ m₂ : ExtTreeMap α β cmp) (f : α → Option β → Option β → Option β) : ExtTreeMap α β cmp := Id.run do
  let mut r := ∅
  for (a, b₁) in m₁ do
    if let some b := f a (some b₁) m₂[a]? then
      r := r.insert a b
  for (a, b₂) in m₂ do
    if a ∉ m₁ then
      if let some b := f a none (some b₂) then
        r := r.insert a b
  return r

@[grind =] theorem mem_mergeWithAll {m₁ m₂ : ExtTreeMap α β cmp} {f : α → Option β → Option β → Option β} {a : α} :
    a ∈ mergeWithAll m₁ m₂ f ↔ (a ∈ m₁ ∨ a ∈ m₂) ∧ (f a m₁[a]? m₂[a]?).isSome :=
  sorry

@[grind =] theorem getElem?_mergeWithAll {m₁ m₂ : ExtTreeMap α β cmp} {f : α → Option β → Option β → Option β} :
    (mergeWithAll m₁ m₂ f)[a]? = if a ∈ m₁ ∨ a ∈ m₂ then f a m₁[a]? m₂[a]? else none :=
  sorry

@[grind =] theorem getElem_mergeWithAll {m₁ m₂ : ExtTreeMap α β cmp} {f : α → Option β → Option β → Option β} {a : α} {h} :
    (mergeWithAll m₁ m₂ f)[a] = (f a m₁[a]? m₂[a]?).get (by grind) :=
  sorry

end Std.ExtTreeMap
