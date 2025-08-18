import SparsePolynomial.TreeMapD

open Std

structure FinMap (α : Type u) [Ord α] [TransOrd α] (β : Type v) [Zero β] where
  private values : TreeMapD α β 0

namespace FinMap

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v}

section

variable [Zero β]

instance : GetElem (FinMap α β) α β (fun _ _ => True) where
  getElem := fun m a _ => m.values[a]

@[local grind, local simp]
private theorem getElem_mk (m : TreeMapD α β 0) (a : α) :
    (FinMap.mk m)[a] = m[a] := rfl

@[local grind, local simp]
private theorem getElem_values (m : FinMap α β) (a : α) :
    m.values[a] = m[a] := rfl

@[ext, grind ext]
theorem ext [LawfulEqOrd α] {p₁ p₂ : FinMap α β} (h : ∀ a : α, p₁[a] = p₂[a]) : p₁ = p₂ := by
  cases p₁; cases p₂; congr
  ext
  apply h

section empty

def empty : FinMap α β where
  values := ∅

instance : EmptyCollection (FinMap α β) :=
  ⟨empty⟩

@[simp, grind =] theorem empty_eq_emptyc : (empty : FinMap α β) = ∅ := rfl

instance : Inhabited (FinMap α β) :=
  ⟨empty⟩

@[simp, grind =] theorem getElem_empty (a : α) : (∅ : FinMap α β)[a] = 0 := rfl

end empty

section singleton

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

end singleton

section update

variable [DecidableEq β]

def update (m : FinMap α β) (a : α) (b : β) : FinMap α β where
  values := m.values.insert a b

variable [DecidableEq α] [LawfulEqOrd α]

@[grind =]
theorem getElem_update (m : FinMap α β) (a k : α) (b : β) :
    (m.update a b)[k] = if k = a then b else m[k] := by
  grind [update]

@[simp]
theorem getElem_update_self (m : FinMap α β) (a : α) (b : β) :
    (m.update a b)[a] = b := by
  grind

@[simp]
theorem getElem_update_ne (m : FinMap α β) (a : α) (b : β) (c : α) (h : c ≠ a) :
    (m.update a b)[c] = m[c] := by
  grind

end update

section support

def support (m : FinMap α β) : List α := m.values.toExtTreeMap.keys

variable [LawfulEqOrd α]

@[simp, grind =]
theorem mem_support (m : FinMap α β) (a : α) : a ∈ m.support ↔ m[a] ≠ 0 := by
  grind [support]

end support

section toList

def toList (m : FinMap α β) : List (α × β) := m.values.toExtTreeMap.toList

@[simp, grind =]
theorem toList_eq_map_support (m : FinMap α β) : m.toList = m.support.map fun a => (a, m[a]) := by
  rw [toList]
  sorry

end toList

section foldr

def foldr (m : FinMap α β) (f : α → β → δ → δ) (init : δ) : δ :=
  m.values.foldr (fun a b acc => f a b acc) init

@[simp]
theorem foldr_toList (m : FinMap α β) (f : α × β → δ → δ) (init : δ) :
    m.toList.foldr f init = m.foldr (fun a b acc => f (a, b) acc) init := by
  rw [toList_eq_map_support]
  rw [support]
  rw [foldr]
  rw [List.foldr_map]
  rw [← TreeMapD.foldr_toExtTreeMap]
  sorry

theorem foldr_eq_foldr_support (m : FinMap α β) (f : α → β → δ → δ) (init : δ) :
    m.foldr f init = m.support.foldr (fun a acc => f a m[a] acc) init := by
  sorry

end foldr

section zero

protected def zero : FinMap α β where
  values := .empty

instance : Zero (FinMap α β) := ⟨.zero⟩

instance : Inhabited (FinMap α β) := ⟨0⟩

@[simp, grind =]
theorem getElem_zero (a : α) : (0 : FinMap α β)[a] = 0 := rfl

end zero

section add

variable [DecidableEq β] [LawfulEqOrd α]
variable [Add β]

protected def add (p₁ p₂ : FinMap α β) : FinMap α β where
  values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ + b₂

instance : Add (FinMap α β) := ⟨FinMap.add⟩

theorem add_def (p₁ p₂ : FinMap α β) :
    p₁ + p₂ = { values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ + b₂ } :=
  rfl

@[simp, grind =] theorem getElem_add (zero_add_zero : (0 : β) + 0 = 0) (p₁ p₂ : FinMap α β) (a : α) :
    (p₁ + p₂)[a] = p₁[a] + p₂[a] := by
  rw [add_def]
  grind

theorem add_zero (h : ∀ x : β, x + 0 = x) (p : FinMap α β) : p + 0 = p := by grind

theorem zero_add (h : ∀ x : β, 0 + x = x) (p : FinMap α β) : 0 + p = p := by grind

theorem add_comm
    (zero_add_zero : (0 : β) + 0 = 0)
    (add_comm : ∀ x y : β, x + y = y + x)
    (p₁ p₂ : FinMap α β) : p₁ + p₂ = p₂ + p₁ := by grind

theorem add_assoc
    (zero_add_zero : (0 : β) + 0 = 0)
    (add_assoc : ∀ x y z : β, (x + y) + z = x + (y + z))
    (p₁ p₂ p₃ : FinMap α β) : (p₁ + p₂) + p₃ = p₁ + (p₂ + p₃) := by grind

end add

end

section grind_instances

open Lean.Grind

variable [DecidableEq β] [AddCommMonoid β]  [LawfulEqOrd α]

attribute [local simp] AddCommMonoid.add_zero

instance [AddRightCancel β] : AddRightCancel (FinMap α β) where
  add_right_cancel x y z w := by
    ext a
    replace w := congrArg (·[a]) w
    simp at w
    exact AddRightCancel.add_right_cancel x[a] y[a] z[a] w

instance : AddCommMonoid (FinMap α β) where
  add_zero x := add_zero AddCommMonoid.add_zero x
  add_comm x y := add_comm (by simp) AddCommMonoid.add_comm x y
  add_assoc x y z := add_assoc (by simp) AddCommMonoid.add_assoc x y z

end grind_instances

end FinMap
