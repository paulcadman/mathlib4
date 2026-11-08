module

import Mathlib.Tactic.RealRootCount

open Polynomial

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by real_root_count

example : Fintype.card ((X ^ 4 + X + 1 : ℚ[X]).rootSet ℝ) = 0 := by real_root_count

example : Fintype.card ((-2 * X ^ 3 + 8 * X : ℚ[X]).rootSet ℝ) = 3 := by real_root_count

example : Fintype.card ((6 * X - 3 : ℚ[X]).rootSet ℝ) = 1 := by real_root_count

example : Fintype.card ((X ^ 2 - C 3 : ℚ[X]).rootSet ℝ) = 2 := by real_root_count

example : Fintype.card ((X ^ 6 - 1000000 : ℚ[X]).rootSet ℝ) = 2 := by real_root_count

-- Repeated roots, rational coefficients, constants and other coefficient rings.
example : Fintype.card (((X - 1) ^ 2 * (X + 2) ^ 3 * (X ^ 2 + 1) : ℚ[X]).rootSet ℝ) = 2 := by
  real_root_count

example : Fintype.card ((X + C (1 / 2) : ℚ[X]).rootSet ℝ) = 1 := by real_root_count

example : Fintype.card ((2 : ℚ[X]).rootSet ℝ) = 0 := by real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℤ[X]).rootSet ℝ) = 2 := by real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℝ[X]).rootSet ℝ) = 2 := by real_root_count

example : Fintype.card ((X ^ 2 - C 2 : ℝ[X]).rootSet ℝ) = 2 := by real_root_count

example : Fintype.card ((X : ℚ[X]).rootSet ℝ) = 1 := by real_root_count

-- Definitions are not unfolded, so unfold them first, as for the quintic in the Abel–Ruffini
-- theorem.
noncomputable def Φ (R : Type*) [CommRing R] (a b : ℕ) : R[X] := X ^ 5 - C (a : R) * X + C (b : R)

example : Fintype.card ((Φ ℚ 4 2).rootSet ℝ) = 3 := by unfold Φ; real_root_count

-- A large degree with few terms. The proof unfolds the coefficient list one level per coefficient,
-- which needs more than the default `maxRecDepth` at degree 100.
set_option maxRecDepth 1024 in
example : Fintype.card ((X ^ 100 - 5 * X ^ 77 + 2 * X ^ 53 - 11 * X ^ 31 + 3 * X ^ 12 - X ^ 2 +
    4 * X - 1 : ℚ[X]).rootSet ℝ) = 4 := by
  real_root_count

-- The simproc rewrites a count inside a larger expression.
example : Fintype.card ((X ^ 2 - 2 : ℚ[X]).rootSet ℝ) + 1 = 3 := by simp only [norm_root_count]

-- The simproc skips what it cannot count, and traces why.
/--
error: `simp` made no progress
---
trace: [Tactic.realRootCount] real_root_count: expected a nonzero polynomial
-/
#guard_msgs in
set_option trace.Tactic.realRootCount true in
example : Fintype.card ((0 : ℚ[X]).rootSet ℝ) = 0 := by real_root_count

/--
error: `simp` made no progress
---
trace: [Tactic.realRootCount] real_root_count: cannot read
      p
    in a polynomial with rational coefficients
-/
#guard_msgs in
set_option trace.Tactic.realRootCount true in
example (p : ℚ[X]) : Fintype.card (p.rootSet ℝ) = 1 := by real_root_count

/--
error: unsolved goals
⊢ 2 = 1
-/
#guard_msgs in
example : Fintype.card ((X ^ 2 - 1 : ℚ[X]).rootSet ℝ) = 1 := by real_root_count
