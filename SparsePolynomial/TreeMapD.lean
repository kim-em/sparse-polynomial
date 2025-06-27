import Std.Data.ExtTreeMap
import SparsePolynomial.Std.ExtTreeMap

open Std

/--
An extensional tree map with a default value.

To preserve extensionality, we require that the default value is not present in the tree.
-/
structure TreeMapD (α : Type u) (β : Type v) (cmp : α → α → Ordering) [TransCmp cmp] (d : β) where
  tree : ExtTreeMap α β cmp
  no_default : ∀ a : α, tree[a]? ≠ some d := by grind

namespace TreeMapD

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} [TransCmp cmp] {d : β}

instance : GetElem (TreeMapD α β cmp d) α β (fun _ _ => True) where
  getElem := fun m a _ => m.tree[a]?.getD d

@[ext]
theorem ext {m₁ m₂ : TreeMapD α β cmp d} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := sorry

def empty : TreeMapD α β cmp d where
  tree := ExtTreeMap.empty
  no_default := sorry

instance : EmptyCollection (TreeMapD α β cmp d) :=
  ⟨empty⟩

@[grind =] theorem empty_eq_emptyc : (empty : TreeMapD α β cmp d) = ∅ := rfl

instance : Inhabited (TreeMapD α β cmp d) :=
  ⟨empty⟩

@[grind =] theorem getElem_empty (a : α) : (∅ : TreeMapD α β cmp d)[a] = d := rfl

variable [DecidableEq β]

def insert (m : TreeMapD α β cmp d) (a : α) (b : β) : TreeMapD α β cmp d where
  tree := if b = d then m.tree.erase a else m.tree.insert a b
  no_default := sorry

@[grind =] theorem getElem_insert [DecidableEq α] (m : TreeMapD α β cmp d) (a : α) (b : β) :
    (m.insert a b)[k] = if k = a then b else m[k] := by
  sorry

def erase (m : TreeMapD α β cmp d) (a : α) : TreeMapD α β cmp d where
  tree := m.tree.erase a
  no_default := sorry

def mergeWithAll (m₁ m₂ : TreeMapD α β cmp d) (f : α → Option β → Option β → β) : TreeMapD α β cmp d where
  tree := m₁.tree.mergeWithAll m₂.tree fun a b₁? b₂? =>
      let r := f a b₁? b₂?
      if r = d then none else some r
  no_default := sorry

def foldr (m : TreeMapD α β cmp d) (f : α → β → δ → δ) (init : δ) : δ :=
  m.tree.foldr (fun a b acc => f a b acc) init

end TreeMapD
