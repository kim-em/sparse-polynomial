import Std.Data.ExtTreeMap
import SparsePolynomial.Std.ExtTreeMap

open Std

namespace Option

@[grind =] theorem getD_guard : (guard p a).getD b = if p a then a else b := by
  simp only [guard]
  split <;> simp

end Option

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

@[local grind] private theorem getElem_mk
    (tree : ExtTreeMap α β cmp) (no_default : ∀ a : α, tree[a]? ≠ some d) (a : α) :
    (TreeMapD.mk tree no_default)[a] = tree[a]?.getD d := rfl

@[local grind] private theorem getElem?_tree [DecidableEq β] (m : TreeMapD α β cmp d) (a : α) :
    m.tree[a]? = if m[a] = d then none else some m[a] := by
  grind [cases TreeMapD]

@[local grind] private theorem mem_tree (m : TreeMapD α β cmp d) (a : α) :
    a ∈ m.tree ↔ m[a] ≠ d := by
  grind [cases TreeMapD]

@[ext, grind ext]
theorem ext [LawfulEqCmp cmp]  {m₁ m₂ : TreeMapD α β cmp d} (h : ∀ a : α, m₁[a] = m₂[a]) : m₁ = m₂ := by
  rcases m₁ with ⟨tree₁, no_default₁⟩
  rcases m₂ with ⟨tree₂, no_default₂⟩
  congr
  ext a b
  specialize h a
  grind

def empty : TreeMapD α β cmp d where
  tree := ExtTreeMap.empty
  no_default := sorry -- by grind -- needs `grind` annotations on ExtTreeMap.

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

def mergeWithAll (m₁ m₂ : TreeMapD α β cmp d) (f : α → β → β → β) : TreeMapD α β cmp d where
  tree := m₁.tree.mergeWithAll m₂.tree fun a b₁? b₂? => Option.guard (· ≠ d) (f a (b₁?.getD d) (b₂?.getD d))
  no_default := by grind

@[grind =] theorem getElem_mergeWithAll
    (m₁ m₂ : TreeMapD α β cmp d) (f : α → β → β → β) (w : ∀ a, f a d d = d) (a : α) :
    (m₁.mergeWithAll m₂ f)[a] = f a m₁[a] m₂[a] := by
  change (TreeMapD.mk _ _)[a] = _
  grind

def foldr (m : TreeMapD α β cmp d) (f : α → β → δ → δ) (init : δ) : δ :=
  m.tree.foldr (fun a b acc => f a b acc) init

end TreeMapD
