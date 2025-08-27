/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import FinMap.Support

open Std

namespace FinMap

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v} [Zero β]

section zero

protected def zero : FinMap α β where
  values := .empty

instance : Zero (FinMap α β) := ⟨.zero⟩

instance : Inhabited (FinMap α β) := ⟨0⟩

@[simp, grind =]
theorem getElem_zero (a : α) : (0 : FinMap α β)[a] = 0 := rfl

@[simp, grind =]
theorem foldr_zero (f : α → β → δ → δ) (init : δ) : (0 : FinMap α β).foldr f init = init :=
  foldr_empty f init

end zero

section add

variable [DecidableEq β] [LawfulEqOrd α]
variable [Add β]

protected def add (p₁ p₂ : FinMap α β) : FinMap α β where
  values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ + b₂

instance : Add (FinMap α β) := ⟨FinMap.add⟩

private theorem add_def (p₁ p₂ : FinMap α β) :
    p₁ + p₂ = { values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ + b₂ } :=
  rfl

@[simp, grind =]
theorem getElem_add (zero_add_zero : (0 : β) + 0 = 0) (p₁ p₂ : FinMap α β) (a : α) :
    (p₁ + p₂)[a] = p₁[a] + p₂[a] := by
  rw [add_def]
  grind

theorem add_zero (add_zero : ∀ x : β, x + 0 = x) (p : FinMap α β) : p + 0 = p := by grind

theorem zero_add (zero_add : ∀ x : β, 0 + x = x) (p : FinMap α β) : 0 + p = p := by grind

theorem add_comm
    (zero_add_zero : (0 : β) + 0 = 0)
    (add_comm : ∀ x y : β, x + y = y + x)
    (p₁ p₂ : FinMap α β) : p₁ + p₂ = p₂ + p₁ := by grind

theorem add_assoc
    (zero_add_zero : (0 : β) + 0 = 0)
    (add_assoc : ∀ x y z : β, (x + y) + z = x + (y + z))
    (p₁ p₂ p₃ : FinMap α β) : (p₁ + p₂) + p₃ = p₁ + (p₂ + p₃) := by grind

end add

section neg

variable [LawfulEqOrd α] [DecidableEq β] [Neg β]

protected def neg (p : FinMap α β) : FinMap α β where
  values := p.values.map 0 (fun _ b => -b)

instance : Neg (FinMap α β) := ⟨FinMap.neg⟩

private theorem neg_def (p : FinMap α β) : -p = { values := p.values.map 0 (fun _ b => -b) } := rfl

@[simp, grind =]
theorem getElem_neg (neg_zero : -(0 : β) = 0) (p : FinMap α β) (a : α) : (-p)[a] = -p[a] := by
  grind [neg_def]

theorem neg_add_cancel [Add β]
    (neg_zero : -(0 : β) = 0)
    (zero_add_zero : (0 : β) + 0 = 0)
    (neg_add_cancel : ∀ x : β, -x + x = 0)
    (p : FinMap α β) : -p + p = 0 := by grind

end neg

section sub

variable [DecidableEq β] [LawfulEqOrd α]
variable [Sub β]

protected def sub (p₁ p₂ : FinMap α β) : FinMap α β where
  values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ - b₂

instance : Sub (FinMap α β) := ⟨FinMap.sub⟩

private theorem sub_def (p₁ p₂ : FinMap α β) :
    p₁ - p₂ = { values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ - b₂ } := rfl

@[simp, grind =]
theorem getElem_sub (zero_sub_zero : (0 : β) - 0 = 0)
    (p₁ p₂ : FinMap α β) (a : α) : (p₁ - p₂)[a] = p₁[a] - p₂[a] := by
  rw [sub_def]
  grind

variable [Add β] [Neg β]

theorem sub_eq_add_neg
    (zero_sub_zero : (0 : β) - 0 = 0)
    (neg_zero : -(0 : β) = 0)
    (sub_eq_add_neg : ∀ x y : β, x - y = x + -y)
    (p₁ p₂ : FinMap α β) : p₁ - p₂ = p₁ + -p₂ := by
  grind

end sub


section mul

variable [DecidableEq β] [LawfulEqOrd α]
variable [Mul β]

-- This implementation could be changes to use `mergeWith` rather than `mergeWithAll`
protected def mul (p₁ p₂ : FinMap α β) : FinMap α β where
  values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ * b₂

instance : Mul (FinMap α β) := ⟨FinMap.mul⟩

private theorem mul_def (p₁ p₂ : FinMap α β) :
    p₁ * p₂ = { values := p₁.values.mergeWithAll p₂.values fun _ b₁ b₂ => b₁ * b₂ } :=
  rfl

@[simp, grind =]
theorem getElem_mul (zero_mul_zero : (0 : β) * 0 = 0) (p₁ p₂ : FinMap α β) (a : α) :
    (p₁ * p₂)[a] = p₁[a] * p₂[a] := by
  rw [mul_def]
  grind

theorem mul_zero (mul_zero : ∀ x : β, x * 0 = 0) (p : FinMap α β) : p * 0 = 0 := by grind

theorem zero_mul (zero_mul : ∀ x : β, 0 * x = 0) (p : FinMap α β) : 0 * p = 0 := by grind

theorem mul_comm
    (zero_mul_zero : (0 : β) * 0 = 0)
    (mul_comm : ∀ x y : β, x * y = y * x)
    (p₁ p₂ : FinMap α β) : p₁ * p₂ = p₂ * p₁ := by grind

theorem mul_assoc
    (zero_mul_zero : (0 : β) * 0 = 0)
    (mul_assoc : ∀ x y z : β, (x * y) * z = x * (y * z))
    (p₁ p₂ p₃ : FinMap α β) : (p₁ * p₂) * p₃ = p₁ * (p₂ * p₃) := by grind

end mul

section distrib

variable [DecidableEq β] [LawfulEqOrd α]
variable [Add β] [Mul β]

theorem left_distrib
    (zero_add_zero : (0 : β) + 0 = 0)
    (zero_mul_zero : (0 : β) * 0 = 0)
    (left_distrib : ∀ x y z : β, x * (y + z) = x * y + x * z)
    (p₁ p₂ p₃ : FinMap α β) : p₁ * (p₂ + p₃) = p₁ * p₂ + p₁ * p₃ := by grind

theorem right_distrib
    (zero_add_zero : (0 : β) + 0 = 0)
    (zero_mul_zero : (0 : β) * 0 = 0)
    (right_distrib : ∀ x y z : β, (x + y) * z = x * z + y * z)
    (p₁ p₂ p₃ : FinMap α β) : (p₁ + p₂) * p₃ = p₁ * p₃ + p₂ * p₃ := by grind

end distrib

end FinMap
