import FinMap.Algebra
import FinMap.Support

open Std

structure SparsePolynomial (β : Type v) [Zero β] where
  coeffs : FinMap Nat β

namespace SparsePolynomial

variable {β : Type v} [Zero β]

instance : GetElem (SparsePolynomial β) Nat β (fun _ _ => True) where
  getElem p n _ := p.coeffs[n]

instance : Zero (SparsePolynomial β) where
  zero := { coeffs := 0 }

section monomial

variable [DecidableEq β]

def monomial (n : Nat) (a : β) : SparsePolynomial β where
  coeffs := FinMap.single n a

end monomial

section add

variable [DecidableEq β] [Add β]

instance : Add (SparsePolynomial β) where
  add p₁ p₂ := { coeffs := p₁.coeffs + p₂.coeffs }

end add

section mul

variable [DecidableEq β] [Add β] [Mul β]

def mulMonomial (n : Nat) (a : β) (p : SparsePolynomial β) : SparsePolynomial β where
  coeffs := p.coeffs.foldr (fun k b acc => acc + FinMap.single (n + k) (a * b)) 0

instance : Mul (SparsePolynomial β) where
  mul p₁ p₂ := p₁.coeffs.foldr (fun n a acc => acc + mulMonomial n a p₂) 0

end mul

end SparsePolynomial
