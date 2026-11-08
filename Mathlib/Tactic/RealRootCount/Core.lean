/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.RealRootCount.Reflection

/-!
# Computing a Sturm sequence for a polynomial

`sturmData p` computes the `SturmData` for the polynomial represented by a coefficient list `p`.
-/

namespace Mathlib.Tactic.RealRootCount

open CoeffList

meta section

namespace CoeffList

variable {R : Type*}

/-- The sum of the polynomials that `p` and `q` represent. -/
public def add [Add R] [Zero R] (p q : List R) : List R :=
  List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p q

/-- The negation of the polynomial that `p` represents. -/
public def neg [Neg R] (p : List R) : List R := p.map (- ·)

/-- The product of the polynomial that `p` and `q` represent. -/
public def mul [Semiring R] (p : List R) (q : List R) : List R :=
  match p, q with
  | [], _ => []
  | c :: p1, q1 => add (q1.map (c * ·)) (0 :: mul p1 q1)

/-- The lcm of the denominators of `p`. -/
def lcmDen (p : List ℚ) : ℕ := p.foldl (fun d x => d.lcm x.den) 1

/-- The gcd of the numerators of `p`. -/
def gcdNum (p : List ℚ) : ℕ := p.foldl (fun g x => g.gcd x.num.natAbs) 0

/-- The least `k > 0` such that `k * p` has integer coefficients or `1` if `p` represents `0`. -/
def primitiveFactor (p : List ℚ) : ℚ :=
  let g := gcdNum p
  if g = 0 then 1 else lcmDen p / g

end CoeffList

/-- Long division over `ℚ` `of the polynomials that `p` and `q` represent. -/
def divMod (p q : List ℚ) : List ℚ × List ℚ := Id.run do
  let trim (p : List ℚ) := (p.reverse.dropWhile (· == 0)).reverse
  let q := trim q
  if q.isEmpty then return ([], trim p)
  let mut rem := trim p
  let mut quot : List ℚ := []
  for _ in [0:p.length + 1 - q.length] do
    if rem.length < q.length then break
    -- The monomial `(lead rem / lead q) * X ^ (deg rem - deg q)`
    let m := List.replicate (rem.length - q.length) 0 ++ [lead rem / lead q]
    quot := add quot m
    rem := trim (add rem (neg (mul m q)))
  return (trim quot, rem)

/-- Compute the next step in the Sturm sequence after `p` and `q`.

`r` is the primitive part of `-(p % q)` and `a, c > 0` and `b` are the smallest integers such that
`a * p + b * q + c * r = 0`. -/
def sturmStep (p q : List ℤ) : SturmStep :=
  let (quot, rem) := divMod (neg (p.map (↑))) (q.map (↑))
  let k := primitiveFactor rem
  let a : ℤ := lcmDen (k⁻¹ :: quot)
  let b := quot.map fun x : ℚ => (a * x).num
  let c := (a * k⁻¹).num
  let r := rem.map fun x => (k * x).num
  { a, b, c, r }

/-- Compute the steps of the Sturm sequence of `p` and its derivative. -/
def sturmSteps (p : List ℤ) : List SturmStep := Id.run do
  let mut p := p
  let mut q := derivative p
  let mut steps := #[]
  for _ in [0:p.length - 1] do
    let s := sturmStep p q
    steps := steps.push s
    if s.r.isEmpty then break
    p := q
    q := s.r
  steps.toList

/-- Compute a power of two value above the coefficient bound `SturmStep.bound` at every step. -/
def evalPoint (p : List ℤ) (steps : List SturmStep) : ℕ := Id.run do
  let mut p := p
  let mut p' := derivative p
  let mut bound := 0
  for s in steps do
    bound := max bound (s.bound (supNorm p) (supNorm p') (supNorm s.r))
    p := p'
    p' := s.r
  return 2 ^ (Nat.log2 bound + 1)

/-- Compute the `SturmData` for the polynomial with coefficient list `p`. -/
public def SturmData.fromCoeffList (p : List ℚ) : SturmData :=
  let k := primitiveFactor p
  -- collect the integer coefficients of `k * p`
  let s := p.map fun x => (k * x).num
  let steps := sturmSteps s
  let M := evalPoint s steps
  { k, s, steps, M }

end

end Mathlib.Tactic.RealRootCount
