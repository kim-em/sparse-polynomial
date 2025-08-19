import SparsePolynomial.FinMap

def x : FinMap Nat Int := ∅
def y : FinMap Nat Int := x.update 1 2
def z : FinMap Nat Int := y.update 2 3

/-- info: 0 -/
#guard_msgs in
#eval z[37]

/-- info: 4 -/
#guard_msgs in
#eval (y + z)[1]

/-- info: -3 -/
#guard_msgs in
#eval (y - z)[2]
