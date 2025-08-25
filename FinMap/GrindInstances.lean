/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import FinMap.Algebra

open Std
open Lean.Grind

namespace FinMap

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v}

variable [DecidableEq β] [LawfulEqOrd α]

attribute [local simp] AddCommMonoid.add_zero

section AddCommMonoid

variable [AddCommMonoid β]

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

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup β]

instance : AddCommGroup (FinMap α β) where
  neg_add_cancel x :=
    neg_add_cancel AddCommGroup.neg_zero (by simp) AddCommGroup.neg_add_cancel x
  sub_eq_add_neg x y :=
    sub_eq_add_neg (by rw [AddCommGroup.sub_eq_add_neg, AddCommGroup.neg_zero, AddCommMonoid.add_zero])
      AddCommGroup.neg_zero AddCommGroup.sub_eq_add_neg x y

end AddCommGroup

end FinMap
