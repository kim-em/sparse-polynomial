/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import SparsePolynomial.FinMap.Basic

open Std

namespace FinMap

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v} [Zero β]

section support

/-- The list of keys with non-zero values in a `FinMap`. -/
def support (m : FinMap α β) : List α := m.values.toExtTreeMap.keys

variable [LawfulEqOrd α]

@[simp, grind =]
theorem mem_support (m : FinMap α β) (a : α) : a ∈ m.support ↔ m[a] ≠ 0 := by
  grind [support]

@[simp]
theorem support_eq_nil_iff (m : FinMap α β) : m.support = [] ↔ m = ∅ := by
  sorry

theorem nodup_support {m : FinMap α β} : m.support.Nodup := sorry

variable [BEq α] [DecidableEq β]

@[grind =]
theorem support_update {m : FinMap α β} {a : α} {b : β} :
    (m.update a b).support = if b = 0 then m.support.erase a else a :: m.support :=
  -- This is false, we need to either use a permutation, or orderedInsert
  sorry

@[simp]
theorem support_update_zero {m : FinMap α β} {a : α} :
    (m.update a 0).support = m.support.erase a := sorry

end support

section toList

/-- Convert a `FinMap` to a list of key-value pairs, returning only the keys with non-zero values. -/
def toList (m : FinMap α β) : List (α × β) := m.values.toExtTreeMap.toList

variable [LawfulEqOrd α]

@[simp, grind =]
theorem toList_eq_map_support (m : FinMap α β) :
    m.toList = m.support.map fun a => (a, m[a]) := by
  rw [toList, support]
  rw [ExtTreeMap.toList_eq_keys_attach_map]
  simp

variable [DecidableEq β]

theorem ofList_toList {m : FinMap α β} : ofList m.toList = m := sorry

end toList

section

variable [DecidableEq β]

variable [DecidableEq α] [LawfulEqOrd α] -- Doesn't DecidableEq follow from LawfulEqOrd?

private def recursion_aux {C : FinMap α β → Sort _}
    (empty : C ∅) (update : (m : FinMap α β) → (a : α) → (b : β) → m[a] = 0 → C m → C (m.update a b))
    (m : FinMap α β) : (l : List α) → m.support = l → C m
  | List.nil, h => by
    have : m = ∅ := by simpa using h
    subst this
    exact empty
  | List.cons a as, h => by
    have : m = (m.update a 0).update a m[a] := by grind
    rw [this]
    apply update
    · simp
    · exact recursion_aux empty update _ as (by grind)

def recursion {C : FinMap α β → Sort _}
    (empty : C ∅) (update : (m : FinMap α β) → (a : α) → (b : β) → m[a] = 0 → C m → C (m.update a b))
    (m : FinMap α β) : C m :=
  recursion_aux empty update m _ rfl

end

section foldr

/-- Fold a function over the keys and non-zero values of a `FinMap`. -/
def foldr (m : FinMap α β) (f : α → β → δ → δ) (init : δ) : δ :=
  m.values.foldr (fun a b acc => f a b acc) init

variable [LawfulEqOrd α]

@[simp, grind =]
theorem foldr_toList (m : FinMap α β) (f : α × β → δ → δ) (init : δ) :
    m.toList.foldr f init = m.foldr (fun a b acc => f (a, b) acc) init := by
  rw [toList_eq_map_support, support, foldr, List.foldr_map,
    ← TreeMapD.foldr_toExtTreeMap, ExtTreeMap.foldr_eq_foldr_attach_keys]
  simp

theorem fold_eq_foldr_toList {m : FinMap α β} {f : α → β → δ → δ} {init : δ} :
    m.foldr f init = m.toList.foldr (fun (a, b) acc => f a b acc) init := by
  rw [foldr_toList]

theorem foldr_eq_foldr_support (m : FinMap α β) (f : α → β → δ → δ) (init : δ) :
    m.foldr f init = m.support.foldr (fun a acc => f a m[a] acc) init := by
  rw [fold_eq_foldr_toList, toList_eq_map_support, List.foldr_map]

end foldr

end FinMap
