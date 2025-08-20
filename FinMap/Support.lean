/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import FinMap.Basic

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
  rw [support]
  simp

theorem nodup_support {m : FinMap α β} : m.support.Nodup := by
  rw [support]
  exact ExtTreeMap.nodup_keys

end support

instance [LawfulEqOrd α] [DecidableEq β] : DecidableEq (FinMap α β) :=
  fun p₁ p₂ => decidable_of_iff (∀ a, a ∈ p₁.support ++ p₂.support → p₁[a] = p₂[a]) (by grind)

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

variable [DecidableEq α] [DecidableEq β]

theorem ofList_toList {m : FinMap α β} : ofList m.toList = m := by
  ext a
  simp only [toList_eq_map_support, getElem_ofList, List.findRev?_eq_find?_reverse]
  by_cases h : m[a] = 0
  · rw [List.find?_eq_none.mpr ?_] <;> grind
  · rw [(List.find?_eq_some_iff_append (b := (a, m[a]))).mpr ?_]
    · grind
    · have := m.nodup_support
      have h₁ : a ∈ m.support := by grind
      obtain ⟨as, bs, h₂, h₃⟩ := List.eq_append_cons_of_mem h₁
      -- TODO: why do we need these rewrites? Why can't grind see them?
      rw [h₂, List.map_append, List.map_cons, List.reverse_append,
        List.reverse_cons, List.append_assoc, List.cons_append]
      grind

end toList

section

variable [DecidableEq β]

variable [DecidableEq α] [LawfulEqOrd α]

private def recursion_aux {C : FinMap α β → Sort _}
    (empty : C ∅) (update : (m : FinMap α β) → (a : α) → (b : β) → m[a] = 0 → C m → C (m.update a b))
    (m : FinMap α β) : (l : List α) → m.support ⊆ l → C m
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

/-- Construct a value (or prove a predicate) for a `FinMap` by recursively adding new key value pairs. -/
def recursion {C : FinMap α β → Sort _}
    (empty : C ∅) (update : (m : FinMap α β) → (a : α) → (b : β) → m[a] = 0 → C m → C (m.update a b))
    (m : FinMap α β) : C m :=
  recursion_aux empty update m _ (List.Subset.refl _)

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
