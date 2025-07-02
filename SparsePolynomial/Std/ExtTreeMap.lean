/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Std.Data.ExtTreeMap
import SparsePolynomial.Std.TreeMap

/-! # Std.ExtTreeMap.mergeWithAll -/

open Std

namespace List

theorem foldr_iff {xs : List α} {f : α → δ → δ} {init : δ} (p : δ → Prop)
    (w : ∀ (a : α) (_ : a ∈ xs) (r : δ), p (f a r) ↔ p r) :
    p (xs.foldr f init) ↔ p init := by
  induction xs with grind

theorem foldr_of_exists {xs : List α} {f : α → δ → δ} {init : δ} (p : δ → Prop)
    (w : ∀ (a : α) (_ : a ∈ xs) (r : δ), p r → p (f a r))
    (h : ∃ (a : α) (_ : a ∈ xs), ∀ (r : δ), p (f a r)) :
    p (xs.foldr f init) := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [foldr_cons]
    obtain ⟨a, h₁, h₂⟩ := h
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₂)
    · apply h₂
    · apply w
      simp only [mem_cons, true_or]
      apply ih <;> grind

end List

namespace Std.ExtTreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp]

theorem foldr_iff {m : ExtTreeMap α β cmp} {f : α → β → δ → δ} {init : δ} (p : δ → Prop)
    (w : ∀ (a : α) (h : a ∈ m) (r : δ), p (f a m[a] r) ↔ p r) :
    p (m.foldr f init) ↔ p init := by
  rw [foldr_eq_foldr_toList]
  apply List.foldr_iff
  rintro ⟨a, b⟩ h r
  simp only [mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some] at h
  specialize w a (by grind) r
  grind

theorem foldr_of_exists [LawfulEqCmp cmp] {m : ExtTreeMap α β cmp} {f : α → β → δ → δ} {init : δ} (p : δ → Prop)
    (w : ∀ (a : α) (h : a ∈ m) (r : δ), p r → p (f a m[a] r))
    (h : ∃ (a : α) (h : a ∈ m), ∀ (r : δ), p (f a m[a] r)) :
    p (m.foldr f init) := by
  rw [foldr_eq_foldr_toList]
  apply List.foldr_of_exists
  · rintro ⟨a, b⟩ h r
    simp only [mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some] at h
    specialize w a (by grind) r
    grind
  · obtain ⟨a, h₁, h₂⟩ := h
    exact ⟨(a, m[a]), by simp, by grind⟩

/--
Combines two extensional tree maps, using a function `f : α → Option β → Option β → Option β` to combine the values.

The function `f` is used to combine the values of the two tree maps.
For each key present in either map, `f` is called with the key, and the values, if present, from both maps.
If `f` returns `some b`, then `b` is inserted into the result.

**Implementation note**: this is an inefficient implementation: a good implementation will be possible once we have iterators for maps.
-/
def mergeWithAll (m₁ m₂ : ExtTreeMap α β cmp) (f : α → Option β → Option β → Option β) : ExtTreeMap α β cmp :=
  m₂.foldr (fun a b₂ r => if a ∈ m₁ then r else if let some b := f a none (some b₂) then r.insert a b else r)
    (m₁.foldr (fun a b₁ r => if let some b := f a (some b₁) m₂[a]? then r.insert a b else r) ∅)
  -- We could write this using `do` notation, but it's painful to reason about, or even to prove is equal to the `foldr` version:
  -- Id.run do
  --   let mut r := ∅
  --   for (a, b₁) in m₁ do
  --     if let some b := f a (some b₁) m₂[a]? then
  --       r := r.insert a b
  --   for (a, b₂) in m₂ do
  --     if a ∉ m₁ then
  --       if let some b := f a none (some b₂) then
  --         r := r.insert a b
  --   return r

@[grind =] theorem mem_mergeWithAll [LawfulEqCmp cmp] {m₁ m₂ : ExtTreeMap α β cmp} {f : α → Option β → Option β → Option β} {a : α} :
    a ∈ mergeWithAll m₁ m₂ f ↔ (a ∈ m₁ ∨ a ∈ m₂) ∧ (f a m₁[a]? m₂[a]?).isSome := by
  unfold mergeWithAll
  by_cases h₁ : a ∈ m₁
  · simp only [h₁, true_or, getElem?_pos, true_and]
    rw [foldr_iff (a ∈ ·)]
    · match h : f a (some m₁[a]) m₂[a]? with
      | none => rw [foldr_iff (a ∈ ·)] <;> grind
      | some b =>
        simp only [Option.isSome_some, iff_true]
        apply foldr_of_exists (a ∈ ·)
        · grind
        · refine ⟨a, h₁, fun r =>?_⟩
          simp only [h, mem_insert]
          -- Annoying to automate because `grind` can't use `ReflCmp.compare_self`.
          have := ReflCmp.compare_self (cmp := cmp) (a := a)
          grind
    · grind
  · by_cases h₂ : a ∈ m₂
    · simp [h₂]
      match h : f a m₁[a]? (some m₂[a]) with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
        rw [foldr_iff (a ∉ ·), foldr_iff (a ∉ ·)] <;> grind
      | some b =>
        simp only [Option.isSome_some, iff_true]
        apply foldr_of_exists (a ∈ ·)
        · grind
        · refine ⟨a, h₂, fun r => ?_⟩
          split
          · grind
          · split <;> rename_i h₃ b? h₄
            · -- Annoying to automate because `grind` can't use `ReflCmp.compare_self`.
              have := ReflCmp.compare_self (cmp := cmp) (a := a)
              grind
            · exfalso
              apply h₄
              have : m₁[a]? = none := by grind
              rw [this] at h
              exact h
    · simp [h₁, h₂]
      rw [foldr_iff (a ∈ ·), foldr_iff (a ∉ ·)] <;> grind

@[grind =] theorem mem_mergeWithAll' [Ord α] [TransOrd α] [LawfulEqOrd α] {m₁ m₂ : ExtTreeMap α β compare} {f : α → Option β → Option β → Option β} {a : α} :
    a ∈ mergeWithAll m₁ m₂ f ↔ (a ∈ m₁ ∨ a ∈ m₂) ∧ (f a m₁[a]? m₂[a]?).isSome := by
  unfold mergeWithAll
  by_cases h₁ : a ∈ m₁
  · simp only [h₁, true_or, getElem?_pos, true_and]
    rw [foldr_iff (a ∈ ·)]
    · match h : f a (some m₁[a]) m₂[a]? with
      | none => rw [foldr_iff (a ∈ ·)] <;> grind
      | some b =>
        simp only [Option.isSome_some, iff_true]
        apply foldr_of_exists (a ∈ ·) <;> grind
    · grind
  · by_cases h₂ : a ∈ m₂
    · simp [h₂]
      match h : f a m₁[a]? (some m₂[a]) with
      | none =>
        rw [foldr_iff (a ∈ ·), foldr_iff (a ∈ ·)] <;> grind
      | some b =>
        simp only [Option.isSome_some, iff_true]
        apply foldr_of_exists (a ∈ ·)
        · grind
        · exact ⟨a, h₂, fun r => by grind⟩
    · rw [foldr_iff (a ∈ ·), foldr_iff (a ∈ ·)] <;> grind

@[grind =] theorem getElem?_mergeWithAll [Ord α] [TransOrd α] [LawfulEqOrd α] {m₁ m₂ : ExtTreeMap α β compare} {f : α → Option β → Option β → Option β} {a : α} :
    (mergeWithAll m₁ m₂ f)[a]? = if a ∈ m₁ ∨ a ∈ m₂ then f a m₁[a]? m₂[a]? else none := by
  unfold mergeWithAll
  by_cases h₁ : a ∈ m₁
  · simp only [h₁, true_or, ↓reduceIte, getElem?_pos]
    rw [foldr_iff (·[a]? = f a (some m₁[a]) m₂[a]?)]
    · match h : f a (some m₁[a]) m₂[a]? with
      | none => rw [foldr_iff (·[a]? = none)] <;> grind
      | some b =>
        apply foldr_of_exists (·[a]? = some b)
        · intro a' h₁ r h₂
          split
          · rw [getElem?_insert] -- TODO: why can't `grind` do this?
            grind
          · grind
        · refine ⟨a, h₁, fun r => ?_⟩
          split <;> rename_i h₁
          · grind [compare_self, getElem_insert_self] -- TODO: annotate these?
          · specialize h₁ b
            grind
    · grind
  · by_cases h₂ : a ∈ m₂
    · simp [h₂]
      match h : f a m₁[a]? (some m₂[a]) with
      | none =>
        rw [foldr_iff (·[a]? = none), foldr_iff (·[a]? = none)] <;> grind
      | some b =>
        apply foldr_of_exists (·[a]? = some b)
        · grind
        · exact ⟨a, h₂, fun r => by grind⟩
    · simp only [h₁, h₂, or_self, ↓reduceIte, getElem?_eq_none_iff]
      rw [foldr_iff (a ∈ ·), foldr_iff (a ∈ ·)] <;> grind

@[grind =] theorem getElem_mergeWithAll [Ord α] [TransOrd α] [LawfulEqOrd α]
    {m₁ m₂ : ExtTreeMap α β compare} {f : α → Option β → Option β → Option β} {a : α} {h} :
    (mergeWithAll m₁ m₂ f)[a] = (f a m₁[a]? m₂[a]?).get (by grind) := by
  apply Option.some_inj.mp
  rw [← getElem?_eq_some_getElem]
  grind

end Std.ExtTreeMap
