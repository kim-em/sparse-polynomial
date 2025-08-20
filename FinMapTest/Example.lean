import FinMap

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

def g : FinMap Nat Int := Id.run do
  let mut m := (∅ : FinMap Nat Int)
  m := m.update 0 37
  for i in [1:1000] do
    m := m.update i (m[i - 1] * 2)
  for i in [500:600] do
    m := m.update i 0
  return m

/-- info: 900 -/
#guard_msgs in
#eval g.support.length

/-- info: 1004 -/
#guard_msgs in
#eval g[999].natAbs.log2

def h : FinMap Nat Int := Id.run do
  let mut m := (∅ : FinMap Nat Int)
  for i in [0:100000] do
    m := m.update i i
  return m

/-- info: 99999 -/
#guard_msgs in
#eval h[100000 - 1]
