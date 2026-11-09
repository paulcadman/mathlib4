/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Tactic.RealRootCount.CoeffList
public import Mathlib.Tactic.RealRootCount.SturmCount

/-!
# Checking Sturm data for `real_root_count` by reflection
-/

@[expose] public section

open Polynomial SignType Mathlib.Tactic.RealRootCount.CoeffList

namespace Mathlib.Tactic.RealRootCount

/-- An entry of the Sturm sequence stored as a list of coefficients and stored with its sup norm and
its value at a point `M`. -/
structure SturmEntry where
  coeffs : List ℤ
  value : ℤ
  supNorm : ℕ

def SturmEntry.ofList (M : ℤ) (p : List ℤ) : SturmEntry :=
  ⟨p, eval M p, CoeffList.supNorm p⟩

/-- Represents a relation between two steps in a Sturm sequence: `a * p + b * q + c * r = 0` where
`r` has lower degree than `q`. -/
structure SturmStep where
  /-- The positive integer factor of `p`. -/
  a : ℤ
  /-- The coefficients of the polynomial factor `b` of `q`. -/
  b : List ℤ
  /-- The positive integer factor fo `r`. -/
  c : ℤ
  /-- The coefficients of the remainder `r`. -/
  r : List ℤ

namespace SturmStep

/-- A bound on the absolute values of the coefficients of `a * p + b * q + c * r` where `np`, `nq`,
`nr` are the sup norms of `p`, `q` and `r`. -/
def bound (s : SturmStep) (np nq nr : ℕ) : ℕ :=
  s.a.natAbs * np + l1Norm s.b * nq + s.c.natAbs * nr

/-- The value of `a * p + b * q + c * r at `M` where `vp`, `vq`, and `vr` are the values of `p`,
`q`, and `r` at `M`. -/
def value (s : SturmStep) (M : ℕ) (vp vq vr : ℤ) : ℤ :=
  s.a * vp + eval (M : ℤ) s.b * vq + s.c * vr

/-- Check the conditions for `s` to represent a step in the Sturm sequence. -/
def check (s : SturmStep) (M : ℕ) (p q r : SturmEntry) : Bool :=
  0 < s.a &&
  0 < s.c &&
  lead q.coeffs != 0 &&
  r.coeffs.length < q.coeffs.length &&
  s.bound p.supNorm q.supNorm r.supNorm < M &&
  s.value M p.value q.value r.value == 0

end SturmStep

/-- The data of a Sturm sequence for the polynomial with coefficient list `p` -/
structure SturmData where
  /-- The positive scale with `s = k * p`. -/
  k : ℚ
  /-- The integer coefficient list `k * p`. -/
  s : List ℤ
  /-- The steps of the scaled Sturm sequence of `s` and its derivative. -/
  steps : List SturmStep
  /-- The point at which the equation of each step is checked by its value. -/
  M : ℕ

/-- The polynomials in the Sturm sequence. -/
def chain (p q : List ℤ) (steps : List SturmStep) : List (List ℤ) :=
  match q, steps with
  | [], _ => [p]
  | _, [] => [p, q]
  | _, ⟨_, _, _, r⟩ :: rest => p :: chain q r rest

def checkSteps (M : ℕ) (e₁ e₂ : SturmEntry) (steps : List SturmStep) : Bool :=
  match e₂, steps with
  | ⟨[], _, _⟩, [] => true
  | e₂, s :: ss =>
    let r := SturmEntry.ofList M s.r
    s.check M e₁ e₂ r && checkSteps M e₂ r ss
  | _, _ => false

def checkChain (M : ℕ) (p q : List ℤ) (steps : List SturmStep) : Bool :=
  lead p != 0 && checkSteps M (.ofList M p) (.ofList M q) steps

/-- Check the `SturmData` corresponds to a Sturm sequence for the polynomial with coefficients `p`.
-/
def checkSturm (p : List ℚ) (d : SturmData) : Bool :=
  0 < d.k &&
  d.s.map (↑) == p.map (d.k * ·) &&
  checkChain d.M d.s (CoeffList.derivative d.s) d.steps

/-- The number of distinct real roots of the polynomial that `p` represents. -/
def realRootCount? (p : List ℚ) (d : SturmData) : Option ℕ :=
  let sturmSeq := chain d.s (CoeffList.derivative d.s) d.steps
  let atTop := (sturmSeq.map lead).signVariations
  let atBot := (sturmSeq.map fun e => if e.length % 2 = 0 then -lead e else lead e).signVariations
  if checkSturm p d && atTop ≤ atBot then some (atBot - atTop) else none

/-- The real polynomial that `p` represents. -/
noncomputable abbrev toReal {R : Type*} [CommSemiring R] [Algebra R ℝ] (p : List R) : ℝ[X] :=
  (ofCoeffList p).map (algebraMap R ℝ)

/-! `real_root_count` rewrites with the next two lemmas to turn a coefficient list into a
polynomial expression. -/

theorem toReal_nil : toReal ([] : List ℚ) = 0 := by
  sorry

theorem toReal_cons (c : ℚ) (p : List ℚ) : toReal (c :: p) = C (c : ℝ) + X * toReal p := by
  sorry

theorem sturmCount_of_realRootCount? {p : List ℚ} {d : SturmData} {n : ℕ}
    (h : realRootCount? p d = some n) :
    SturmCount (toReal p) ((chain d.s (CoeffList.derivative d.s) d.steps).map toReal) n := by
  sorry

theorem card_rootSet_of_realRootCount? {R : Type*} [CommRing R] [Algebra R ℝ] {f : R[X]}
    {p : List ℚ} {d : SturmData} {n : ℕ} (hf : f.map (algebraMap R ℝ) = toReal p)
    (h : realRootCount? p d = some n) : Fintype.card (f.rootSet ℝ) = n := by
  have hS := sturmCount_of_realRootCount? h
  rw [← hf] at hS
  exact hS.card_rootSet

end Mathlib.Tactic.RealRootCount
