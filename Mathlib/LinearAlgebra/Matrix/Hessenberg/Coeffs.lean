/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Basic
public import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# The coefficient-level mirror of the Hessenberg recurrence
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R]

/-! ## Arithmetic on coefficient lists -/

/-- `a • p`, coefficientwise. -/
def coeffScale (a : R) : List R → List R
  | [] => []
  | c :: p => a * c :: coeffScale a p

/-- `p + q` on coefficient lists of possibly different lengths. -/
def coeffAdd : List R → List R → List R
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => (x + y) :: coeffAdd p q

/-- `X * p` on coefficients. -/
def coeffShift (p : List R) : List R := 0 :: p

/-- `p - q` on coefficients. -/
def coeffSub (p q : List R) : List R := coeffAdd p (coeffScale (-1) q)

theorem ofCoeffs_coeffScale (a : R) (p : List R) :
    ofCoeffs (coeffScale a p) = C a * ofCoeffs p := by
  induction p with
  | nil => simp [coeffScale]
  | cons c p ih =>
    rw [coeffScale, ofCoeffs_cons, ofCoeffs_cons, ih, C_mul]
    ring

theorem ofCoeffs_coeffAdd (p q : List R) : ofCoeffs (coeffAdd p q) = ofCoeffs p + ofCoeffs q := by
  induction p generalizing q with
  | nil => simp [coeffAdd]
  | cons c p ih =>
    cases q with
    | nil => simp [coeffAdd]
    | cons d q =>
      rw [coeffAdd, ofCoeffs_cons, ofCoeffs_cons, ofCoeffs_cons, ih, C_add]
      ring

theorem ofCoeffs_coeffShift (p : List R) : ofCoeffs (coeffShift p) = X * ofCoeffs p := by
  rw [coeffShift, ofCoeffs_cons, map_zero, zero_add]

theorem ofCoeffs_coeffSub (p q : List R) : ofCoeffs (coeffSub p q) = ofCoeffs p - ofCoeffs q := by
  rw [coeffSub, ofCoeffs_coeffAdd, ofCoeffs_coeffScale, map_neg, map_one, neg_one_mul,
    sub_eq_add_neg]

def coeffHessSum (n : ℕ) (H : Array R) (kcol : ℕ) :
    (i : ℕ) → (beta : R) → Array (List R) → List R
  | 0, beta, ps => coeffScale (H.getD (n * 0 + kcol) 0 * beta) (ps.getD 0 [])
  | i + 1, beta, ps =>
    coeffAdd (coeffScale (H.getD (n * (i + 1) + kcol) 0 * beta) (ps.getD (i + 1) []))
      (coeffHessSum n H kcol i (beta * H.getD (n * (i + 1) + i) 0) ps)

def coeffHessStep (n : ℕ) (H : Array R) (k : ℕ) (ps : Array (List R)) : List R :=
  match k with
  | 0 => [1]
  | 1 =>
    coeffSub (coeffShift (ps.getD 0 []))
      (coeffScale (H.getD (n * 0 + 0) 0) (ps.getD 0 []))
  | k' + 2 =>
    coeffSub
      (coeffSub (coeffShift (ps.getD (k' + 1) []))
        (coeffScale (H.getD (n * (k' + 1) + (k' + 1)) 0) (ps.getD (k' + 1) [])))
      (coeffHessSum n H (k' + 1) k' (H.getD (n * (k' + 1) + k') 0) ps)

def coeffHessAux (n : ℕ) (H : Array R) : ℕ → Array (List R)
  | 0 => #[[1]]
  | k + 1 =>
    let ps := coeffHessAux n H k
    ps.push (coeffHessStep n H (k + 1) ps)

def coeffHessCharPoly (n : ℕ) (H : Array R) : List R :=
  (coeffHessAux n H n).getD n []

theorem hessCharPoly_eq_ofCoeffs (n : ℕ) (H : Array R) :
    hessCharPoly n H = ofCoeffs (coeffHessCharPoly n H) := by
  sorry

end Matrix

end
