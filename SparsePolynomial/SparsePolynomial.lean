import SparsePolynomial.FinMap

structure SparsePolynomial (β : Type v) [Zero β] where
  private coeffs : FinMap Nat β

namespace SparsePolynomial

variable {β : Type v} [Zero β]

instance : GetElem (SparsePolynomial β) Nat β (fun _ _ => True) where
  getElem := fun p a _ => p.coeffs[a]

@[local grind] private theorem getElem_mk (coeffs : FinMap Nat β) (a : Nat) :
    (SparsePolynomial.mk coeffs)[a] = coeffs[a] := rfl

@[local grind] private theorem getElem_coeffs (p : SparsePolynomial β) (a : Nat) :
    p.coeffs[a] = p[a] := rfl

@[ext, grind ext]
theorem ext {p₁ p₂ : SparsePolynomial β} (h : ∀ a : Nat, p₁[a] = p₂[a]) : p₁ = p₂ := by
  cases p₁; cases p₂; congr
  ext
  apply h

protected def zero : SparsePolynomial β where
  coeffs := .zero

instance : Zero (SparsePolynomial β) := ⟨.zero⟩

@[simp, grind =] theorem getElem_zero (a : Nat) : (0 : SparsePolynomial β)[a] = 0 := rfl

instance : Inhabited (SparsePolynomial β) := ⟨0⟩

protected def one [One β] [DecidableEq β] : SparsePolynomial β where
  coeffs := .singleton 0 1

instance instOne [One β] [DecidableEq β] : One (SparsePolynomial β) := ⟨.one⟩

@[grind =] theorem getElem_one [One β] [DecidableEq β] (a : Nat) :
    (1 : SparsePolynomial β)[a] = if a = 0 then 1 else 0 := by
  change (SparsePolynomial.mk _)[a] = _
  grind

instance [OfNat β n] [DecidableEq β] : OfNat (SparsePolynomial β) n where
  ofNat := ⟨.singleton 0 (OfNat.ofNat n)⟩

@[grind =] theorem getElem_ofNat [OfNat β n] [DecidableEq β] (a : Nat) :
    (OfNat.ofNat n : SparsePolynomial β)[a] = if a = 0 then OfNat.ofNat n else 0 := by
  change (SparsePolynomial.mk _)[a] = _
  grind

def C [DecidableEq β] (b : β) : SparsePolynomial β where
  coeffs := .singleton 0 b

@[grind =] theorem getElem_C [DecidableEq β] (a : Nat) (b : β) :
    (C b : SparsePolynomial β)[a] = if a = 0 then b else 0 := by
  change (SparsePolynomial.mk _)[a] = _
  grind

def X [One β] [DecidableEq β] : SparsePolynomial β where
  coeffs := .singleton 1 1

@[grind =] theorem getElem_X [One β] [DecidableEq β] (a : Nat) :
    (X : SparsePolynomial β)[a] = if a = 1 then 1 else 0 := by
  grind [X]

def degree (p : SparsePolynomial β) : Option Nat :=
  p.coeffs.foldr (fun a _ acc => max a acc) none

def natDegree (p : SparsePolynomial β) : Nat :=
  p.degree.getD 0

section add

variable [Add β] [DecidableEq β]

instance : Add (SparsePolynomial β) := ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨m₁ + m₂⟩⟩

@[simp, grind =] theorem getElem_add (zero_add_zero : (0 : β) + 0 = 0) (p₁ p₂ : SparsePolynomial β) (a : Nat) :
    (p₁ + p₂)[a] = p₁[a] + p₂[a] := by
  change (SparsePolynomial.mk _)[a] = _
  grind

theorem add_zero (add_zero : ∀ x : β, x + 0 = x) (p : SparsePolynomial β) : p + 0 = p := by grind

theorem zero_add (zero_add : ∀ x : β, 0 + x = x) (p : SparsePolynomial β) : 0 + p = p := by grind

theorem add_comm
    (zero_add_zero : (0 : β) + 0 = 0)
    (add_comm : ∀ x y : β, x + y = y + x)
    (p₁ p₂ : SparsePolynomial β) : p₁ + p₂ = p₂ + p₁ := by grind
theorem add_assoc
    (zero_add_zero : (0 : β) + 0 = 0)
    (add_assoc : ∀ x y z : β, x + (y + z) = (x + y) + z)
    (p₁ p₂ p₃ : SparsePolynomial β) : p₁ + (p₂ + p₃) = (p₁ + p₂) + p₃ := by grind

end add

section eval

variable {γ : Type w} [Zero γ] [Add γ] [Pow γ Nat] [HMul β γ γ]

def eval (p : SparsePolynomial β) (x : γ) : γ :=
  p.coeffs.foldr (fun a b acc => b * x ^ a + acc) 0

theorem eval_spec
    (h₁ : ∀ x : γ, (0 : β) * x = 0)
    (h₂ : ∀ x : γ, 0 + x = x)
    (p : SparsePolynomial β) (x : γ) :
    p.eval x = (List.ofFn (fun i : Fin (p.natDegree + 1) => p[i] * x ^ (i : Nat))).sum := sorry

end eval

section mul

variable [Add β] [Mul β]

def mul (p₁ p₂ : SparsePolynomial β) : SparsePolynomial β where
  coeffs := sorry -- Let's do high school multiplication first.

instance : Mul (SparsePolynomial β) := ⟨mul⟩

-- This might need some additional algebra axioms to verify.
theorem mul_spec (p₁ p₂ : SparsePolynomial β) (i : Nat) :
    (p₁ * p₂)[i] = (List.ofFn (fun j : Fin (i + 1) => p₁[j] * p₂[i - j])).sum := sorry

end mul

end SparsePolynomial
