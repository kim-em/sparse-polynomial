import SparsePolynomial.TreeMapD

open Std

structure FinMap (α : Type u) [Ord α] [TransOrd α] (β : Type v) [Zero β] where
  private values : TreeMapD α β 0

namespace FinMap

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v} [Zero β]

instance : GetElem (FinMap α β) α β (fun _ _ => True) where
  getElem := fun m a _ => m.values[a]

@[local grind] private theorem getElem_mk (m : TreeMapD α β 0) (a : α) :
    (FinMap.mk m)[a] = m[a] := rfl

@[local grind] private theorem getElem_values (m : FinMap α β) (a : α) :
    m.values[a] = m[a] := rfl

@[ext, grind ext]
theorem ext [LawfulEqOrd α] {p₁ p₂ : FinMap α β} (h : ∀ a : α, p₁[a] = p₂[a]) : p₁ = p₂ := by
  cases p₁; cases p₂; congr
  ext
  apply h

def foldr (m : FinMap α β) (f : α → β → δ → δ) (init : δ) : δ :=
  m.values.foldr (fun a b acc => f a b acc) init

protected def zero : FinMap α β where
  values := .empty

instance : Zero (FinMap α β) := ⟨.zero⟩

instance : Inhabited (FinMap α β) := ⟨0⟩

theorem getElem_zero (a : α) : (0 : FinMap α β)[a] = 0 := rfl

variable [DecidableEq β] [LawfulEqOrd α]

protected def singleton (a : α) (b : β) : FinMap α β where
  values := TreeMapD.empty.insert a b

@[grind =]
theorem getElem_singleton [DecidableEq α] (a : α) (b : β) (k : α) :
    (FinMap.singleton a b)[k] = if k = a then b else 0 := by
  grind [FinMap.singleton]

@[simp]
theorem getElem_singleton_self [DecidableEq α] (a : α) (b : β) :
    (FinMap.singleton a b)[a] = b := by grind

@[simp]
theorem getElem_singleton_ne [DecidableEq α] (a : α) (b : β) (c : α) (h : c ≠ a) :
    (FinMap.singleton a b)[c] = 0 := by grind

section add

variable [Add β]

protected def add (p₁ p₂ : FinMap α β) : FinMap α β where
  values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ + b₂

instance : Add (FinMap α β) := ⟨FinMap.add⟩

@[grind =] theorem getElem_add (p₁ p₂ : FinMap α β) (a : α) :
    (p₁ + p₂)[a] = p₁[a] + p₂[a] := by
  sorry

theorem add_zero (p : FinMap α β) : p + 0 = p := by
  sorry

theorem zero_add (p : FinMap α β) : 0 + p = p := sorry

theorem add_comm (h : ∀ x y : β, x + y = y + x) (p₁ p₂ : FinMap α β) :
    p₁ + p₂ = p₂ + p₁ := sorry
theorem add_assoc (h : ∀ x y z : β, x + (y + z) = (x + y) + z) (p₁ p₂ p₃ : FinMap α β) :
    p₁ + (p₂ + p₃) = (p₁ + p₂) + p₃ := sorry

end add

end FinMap
