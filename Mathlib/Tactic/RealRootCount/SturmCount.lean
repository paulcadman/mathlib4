/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.SturmTarski

/-!
# Counting real roots with a scaled Sturm sequence

If `L` is the Sturm sequence of `p : ℝ[X]` and its derivative up to positive constant factors, the
number of distinct real roots of `p` is the drop in the sign variations of `L` from `-∞` to `∞`.
At `∞` an entry has the sign of its leading coefficient, and at `-∞` that sign times
`(-1) ^ natDegree`, so the count needs no bound on the roots.

## Main definitions

- `Polynomial.SturmCount p L n`: `L` is the Sturm sequence of `p` and its derivative up to positive
  constant factors, and its sign variations drop by `n` from `-∞` to `∞`.

## Main results

- `Polynomial.SturmCount.card_rootSet`: given `SturmCount (f.map (algebraMap R ℝ)) L n`, `f` has `n`
  distinct real roots.
-/

public section

open SignType

namespace Polynomial

/-- `L` is the Sturm sequence of `p` and its derivative up to positive constant factors, and its
sign variations drop by `n` from `-∞` to `∞`. Then `p` has `n` distinct real roots
(`SturmCount.card_rootSet`). -/
structure SturmCount (p : ℝ[X]) (L : List ℝ[X]) (n : ℕ) : Prop where
  /-- Each entry of `L` is a positive multiple of the matching entry of the Sturm sequence. -/
  sturmSeq_scaled :
    (sturmSeq p (derivative p)).Forall₂ (fun s t => ∃ c : ℝ, 0 < c ∧ t = c • s) L
  /-- The sign variations of `L` drop by `n` from `-∞` to `∞`. At `∞` an entry has the sign of its
  leading coefficient, and at `-∞` that sign times `(-1) ^ natDegree`. -/
  variations :
    (L.map fun s => sign ((-1) ^ s.natDegree * s.leadingCoeff)).signVariations =
      (L.map (sign ∘ leadingCoeff)).signVariations + n

/-- Given `SturmCount (f.map (algebraMap R ℝ)) L n`, `f` has `n` distinct real roots. -/
theorem SturmCount.card_rootSet {R : Type*} [CommRing R] [Algebra R ℝ] {f : R[X]}
    {L : List ℝ[X]} {n : ℕ} (hS : SturmCount (f.map (algebraMap R ℝ)) L n) :
    Fintype.card (f.rootSet ℝ) = n := by
  -- Prove using `sturm_tarski' (f.map (algebraMap R ℝ)) 1 a` with `a` below every root of every
  -- entry of `L`, where each entry has its sign at `-∞`; positive factors do not change the signs
  -- in `L`.
  sorry

end Polynomial
