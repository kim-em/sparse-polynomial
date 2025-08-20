/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import FinMap.TreeMapD

open Std

structure FinMap (α : Type u) [Ord α] [TransOrd α] (β : Type v) [Zero β] where
  values : TreeMapD α β 0

namespace FinMap

variable {α : Type u} [Ord α] [TransOrd α] {β : Type v} [Zero β]

instance : GetElem (FinMap α β) α β (fun _ _ => True) where
  getElem := fun m a _ => m.values[a]

@[grind, simp]
theorem getElem_mk (m : TreeMapD α β 0) (a : α) :
    (FinMap.mk m)[a] = m[a] := rfl

@[grind, simp]
theorem getElem_values (m : FinMap α β) (a : α) :
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

@[simp] theorem values_eq_empty_iff [LawfulEqOrd α] (m : FinMap α β) :
    m.values = ∅ ↔ m = ∅ := by
  constructor <;>
  · intro h
    ext a
    replace h := congrArg (·[a]) h
    simp_all

end empty

variable [DecidableEq β]

section single

variable [LawfulEqOrd α]

/-- The single `FinMap` containing a single key-value pair. -/
protected def single (a : α) (b : β) : FinMap α β where
  values := TreeMapD.empty.insert a b

@[grind =]
theorem getElem_single [DecidableEq α] (a : α) (b : β) (k : α) :
    (FinMap.single a b)[k] = if k = a then b else 0 := by
  grind [FinMap.single]

@[simp]
theorem getElem_single_self [DecidableEq α] (a : α) (b : β) :
    (FinMap.single a b)[a] = b := by grind

@[simp]
theorem getElem_single_ne [DecidableEq α] (a : α) (b : β) (c : α) (h : c ≠ a) :
    (FinMap.single a b)[c] = 0 := by grind

end single

section update

/-- Update the value of a key in a `FinMap`. -/
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

attribute [grind =] List.findRev?_eq_find?_reverse -- missing the library

section updateMany

/-- Update the values of a list of keys in a `FinMap`. -/
def updateMany (m : FinMap α β) (l : List (α × β)) : FinMap α β :=
  l.foldl (fun m (a, b) => m.update a b) m

@[simp, grind =]
theorem updateMany_nil (m : FinMap α β) :
    m.updateMany [] = m := by
  simp [updateMany]

@[simp, grind =]
theorem updateMany_cons (m : FinMap α β) (p : α × β) (l : List (α × β)) :
    m.updateMany (p :: l) = (m.update p.1 p.2).updateMany l := by
  simp [updateMany]

@[simp, grind =]
theorem updateMany_append (m : FinMap α β) (l₁ l₂ : List (α × β)) :
    m.updateMany (l₁ ++ l₂) = (m.updateMany l₁).updateMany l₂ := by
  simp [updateMany]

variable [DecidableEq α] [LawfulEqOrd α]

@[simp, grind =]
theorem getElem_updateMany {m : FinMap α β} {l : List (α × β)} (a : α) :
    (m.updateMany l)[a] = ((l.findRev? (·.1 = a)).map (·.2)).getD m[a] := by
  induction l generalizing m with grind

end updateMany

section ofList

/--
Construct a `FinMap` from a list of key-value pairs.

When there are duplicate keys, the last value is used.
-/
def ofList (l : List (α × β)) : FinMap α β := (∅ : FinMap α β).updateMany l

variable [DecidableEq α] [LawfulEqOrd α]

@[simp, grind =]
theorem getElem_ofList {l : List (α × β)} (a : α) :
    (ofList l)[a] = ((l.findRev? (·.1 = a)).map (·.2)).getD 0 := by
  grind [ofList]


end ofList

end FinMap
