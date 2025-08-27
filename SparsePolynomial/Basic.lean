import FinMap.Algebra
import FinMap.Support

open Std

structure SparsePolynomial (β : Type v) [Zero β] where
  coeffs : FinMap Nat β

namespace SparsePolynomial

variable {β : Type v} [Zero β]

instance : GetElem (SparsePolynomial β) Nat β (fun _ _ => True) where
  getElem p n _ := p.coeffs[n]

@[ext, grind ext]
theorem ext (p₁ p₂ : SparsePolynomial β) (h : ∀ i : Nat, p₁[i] = p₂[i]) : p₁ = p₂ := by
  sorry

section zero

instance : Zero (SparsePolynomial β) where
  zero := { coeffs := 0 }

@[simp, grind =]
theorem getElem_zero (i : Nat) : (0 : SparsePolynomial β)[i] = 0 := by
  sorry

@[simp, grind =]
theorem coeffs_zero : (0 : SparsePolynomial β).coeffs = 0 := sorry

end zero

section monomial

variable [DecidableEq β]

def monomial (n : Nat) (a : β) : SparsePolynomial β where
  coeffs := FinMap.single n a

@[simp, grind =]
theorem getElem_monomial (n : Nat) (a : β) (k : Nat) :
    (monomial n a)[k] = if k = n then a else 0 := by
  sorry

end monomial

section ofNat

variable [DecidableEq β]

instance [NeZero n] [OfNat β n] : OfNat (SparsePolynomial β) n where
  ofNat := monomial 0 (OfNat.ofNat n)

@[grind =]
theorem getElem_ofNat [NeZero n] [OfNat β n] (k : Nat) :
    (OfNat.ofNat n : SparsePolynomial β)[k] = if k = 0 then OfNat.ofNat n else 0 := by
  sorry

end ofNat

section add

variable [DecidableEq β] [Add β]

instance : Add (SparsePolynomial β) where
  add p₁ p₂ := { coeffs := p₁.coeffs + p₂.coeffs }

end add

section mul

variable [DecidableEq β] [Add β] [Mul β]

def mulMonomial (n : Nat) (a : β) (p : SparsePolynomial β) : SparsePolynomial β where
  coeffs := p.coeffs.foldr (fun k b acc => acc + FinMap.single (n + k) (a * b)) 0

theorem getElem_mulMonomial (n : Nat) (a : β) (p : SparsePolynomial β) (i : Nat) :
    (mulMonomial n a p)[i] = if i < n then 0 else a * p[i - n] := by
  sorry

instance : Mul (SparsePolynomial β) where
  mul p₁ p₂ := p₁.coeffs.foldr (fun n a acc => acc + mulMonomial n a p₂) 0

-- Perhaps it would be better to have a simpler right hand side: it doesn't need to compute fast!
theorem getElem_mul (p₁ p₂ : SparsePolynomial β) (i : Nat) :
    (p₁ * p₂)[i] = p₁.coeffs.foldr (fun k a acc => if i < k then acc else acc + a * p₂[i - k]) 0 := by
  sorry

theorem zero_mul (p : SparsePolynomial β) : 0 * p = 0 := by
  ext i
  simp_all [getElem_mul]

theorem mul_zero (mul_zero : ∀ b : β, b * 0 = 0) (add_zero : ∀ b : β, b + 0 = b)
    (p : SparsePolynomial β) : p * 0 = 0 := by
  ext i
  simp_all [getElem_mul]
  -- missing theorems about foldr
  sorry

end mul

end SparsePolynomial
