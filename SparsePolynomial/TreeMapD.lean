/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Std.Data.ExtTreeMap
import SparsePolynomial.Std.ExtTreeMap

open Std

/--
An extensional tree map with a default value.

To preserve extensionality, we require that the default value is not present in the tree.
-/
structure TreeMapD (α : Type u) [Ord α] [TransOrd α] (β : Type v) (d : β) where
  private tree : ExtTreeMap α β compare
  private no_default : ∀ a : α, tree[a]? ≠ some d := by grind

namespace TreeMapD

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v} {d : β}

instance : GetElem (TreeMapD α β d) α β (fun _ _ => True) where
  getElem := fun m a _ => m.tree[a]?.getD d

@[local simp, local grind =]
private theorem getElem_mk
    (tree : ExtTreeMap α β compare) (no_default : ∀ a : α, tree[a]? ≠ some d) (a : α) :
    (TreeMapD.mk tree no_default)[a] = tree[a]?.getD d := rfl

@[local simp, local grind =]
private theorem getElem?_tree [DecidableEq β] (m : TreeMapD α β d) (a : α) :
    m.tree[a]? = if m[a] = d then none else some m[a] := by
  grind [cases TreeMapD]

@[local simp, local grind =]
private theorem mem_tree (m : TreeMapD α β d) (a : α) :
    a ∈ m.tree ↔ m[a] ≠ d := by
  grind [cases TreeMapD]

@[ext, grind ext]
theorem ext [LawfulEqOrd α] {m₁ m₂ : TreeMapD α β d} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rcases m₁ with ⟨tree₁, no_default₁⟩
  rcases m₂ with ⟨tree₂, no_default₂⟩
  congr
  ext a b
  specialize h a
  grind

def toExtTreeMap (m : TreeMapD α β d) : ExtTreeMap α β compare := m.tree

section toExtTreeMap

@[simp, grind =]
theorem mem_toExtTreeMap (m : TreeMapD α β d) (a : α) : a ∈ m.toExtTreeMap ↔ m[a] ≠ d := by
  grind [toExtTreeMap]

@[simp, grind =]
theorem getElem_toExtTreeMap (m : TreeMapD α β d) (a : α) (h : a ∈ m.toExtTreeMap) :
    m.toExtTreeMap[a] = m[a] := by
  rcases m with ⟨m⟩
  simp [toExtTreeMap] at h ⊢
  grind

end toExtTreeMap

def empty : TreeMapD α β d where
  tree := ∅

instance : EmptyCollection (TreeMapD α β d) :=
  ⟨empty⟩

@[simp, grind =] theorem empty_eq_emptyc : (empty : TreeMapD α β d) = ∅ := rfl

instance : Inhabited (TreeMapD α β d) :=
  ⟨empty⟩

@[simp, grind =] theorem getElem_empty (a : α) : (∅ : TreeMapD α β d)[a] = d := rfl

section

variable [DecidableEq β]

def insert (m : TreeMapD α β d) (a : α) (b : β) : TreeMapD α β d where
  tree := if b = d then m.tree.erase a else m.tree.insert a b
  no_default := by
    -- `grind` can't do this split because of the dependent typing in the `xs[i]?` notation.
    split <;> grind

@[grind =] theorem getElem_insert [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a : α) (b : β) :
    (m.insert a b)[k] = if k = a then b else m[k] := by
  grind [insert]

@[simp]
theorem getElem_insert_self [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a : α) (b : β) :
    (m.insert a b)[a] = b := by
  grind

@[simp]
theorem getElem_insert_ne [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a : α) (b : β) (k : α) (h : k ≠ a) :
    (m.insert a b)[k] = m[k] := by
  grind

def erase (m : TreeMapD α β d) (a : α) : TreeMapD α β d where
  tree := m.tree.erase a

@[grind =] theorem getElem_erase [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a k : α) :
    (m.erase a)[k] = if k = a then d else m[k] := by
  grind [erase]

@[simp]
theorem getElem_erase_self [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a : α) :
    (m.erase a)[a] = d := by
  grind

@[simp]
theorem getElem_erase_ne [DecidableEq α] [LawfulEqOrd α] (m : TreeMapD α β d) (a : α) (k : α) (h : k ≠ a) :
    (m.erase a)[k] = m[k] := by
  grind

def mergeWithAll [LawfulEqOrd α] (m₁ m₂ : TreeMapD α β d) (f : α → β → β → β) : TreeMapD α β d where
  tree := m₁.tree.mergeWithAll m₂.tree fun a b₁? b₂? => Option.guard (· ≠ d) (f a (b₁?.getD d) (b₂?.getD d))

@[simp, grind =] theorem getElem_mergeWithAll [LawfulEqOrd α]
    (m₁ m₂ : TreeMapD α β d) (f : α → β → β → β) (w : ∀ a, f a d d = d) (a : α) :
    (m₁.mergeWithAll m₂ f)[a] = f a m₁[a] m₂[a] := by
  change (TreeMapD.mk _ _)[a] = _
  grind

end

section map

variable [DecidableEq γ]

/--
Apply a function to all non-default values in a `TreeMapD`,
removing all default values from the results.
-/
def map (m : TreeMapD α β d) (d' : γ) (f : α → β → γ) : TreeMapD α γ d' where
  tree := m.tree.filterMap (fun a b => Option.guard (· ≠ d') (f a b))

@[grind =]
theorem getElem_map [DecidableEq β] {m : TreeMapD α β d} {d' : γ} {f : α → β → γ} {a : α} :
    (m.map d' f)[a] = if m[a] = d then d' else f a m[a] := by
  grind [map]

end map

section foldr

def foldr (m : TreeMapD α β d) (f : α → β → δ → δ) (init : δ) : δ :=
  m.tree.foldr (fun a b acc => f a b acc) init

@[simp, grind =]
theorem foldr_toExtTreeMap (m : TreeMapD α β d) (f : α → β → δ → δ) (init : δ) :
    m.toExtTreeMap.foldr f init = m.foldr f init := rfl

end foldr

end TreeMapD
