/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Tactic.Hessenberg.Recurrence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# The coefficient-level mirror of the Hessenberg recurrence
-/

@[expose] public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

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

/-- The Array version of `hessP`. -/
def coeffHessSum (n : ℕ) (H : Array R) (kcol : ℕ) :
    (i : ℕ) → (beta : R) → Array (List R) → List R
  | 0, beta, ps => coeffScale (H.getD (n * 0 + kcol) 0 * beta) (ps.getD 0 [])
  | i + 1, beta, ps =>
    coeffAdd (coeffScale (H.getD (n * (i + 1) + kcol) 0 * beta) (ps.getD (i + 1) []))
      (coeffHessSum n H kcol i (beta * H.getD (n * (i + 1) + i) 0) ps)

/-- The Array version of one step of `hessP`. -/
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

/-- The Arrays representing the results `hessP n H 0`, ..., `hessP n H k`. -/
def coeffHessAux (n : ℕ) (H : Array R) : ℕ → Array (List R)
  | 0 => #[[1]]
  | k + 1 =>
    let ps := coeffHessAux n H k
    ps.push (coeffHessStep n H (k + 1) ps)

/-- The Array version of `hessCharPoly`. -/
def coeffHessCharPoly (n : ℕ) (H : Array R) : List R :=
  (coeffHessAux n H n).getD n []

theorem ofCoeffs_coeffHessSum (n : ℕ) (H : Array R) (kcol : ℕ) :
    ∀ (i : ℕ) (beta : R) (ps : Array (List R)),
      ofCoeffs (coeffHessSum n H kcol i beta ps) =
        ∑ t : Fin (i + 1),
          C (H.getD (n * (t : ℕ) + kcol) 0 *
              (beta * ∏ j ∈ Finset.Ico (t : ℕ) i, H.getD (n * (j + 1) + j) 0)) *
            ofCoeffs (ps.getD (t : ℕ) [])
  | 0, beta, ps => by simp [coeffHessSum, ofCoeffs_coeffScale]
  | i + 1, beta, ps => by
    rw [Fin.sum_univ_castSucc, coeffHessSum, ofCoeffs_coeffAdd, ofCoeffs_coeffScale,
      ofCoeffs_coeffHessSum, add_comm]
    simp only [Fin.val_castSucc, Fin.val_last, Finset.Ico_self, Finset.prod_empty, mul_one]
    congrm ∑ t, ?_ + _
    rw [Finset.prod_Ico_succ_top (Nat.lt_succ_iff.mp t.isLt)]
    simp only [map_mul]
    ring

theorem ofCoeffs_coeffHessStep (n : ℕ) (H : Array R) (k : ℕ) (ps : Array (List R)) :
    ofCoeffs (coeffHessStep n H (k + 1) ps) =
      (X - C (H.getD (n * k + k) 0)) * ofCoeffs (ps.getD k []) -
        ∑ t : Fin k,
          C (H.getD (n * (t : ℕ) + k) 0 * ∏ j ∈ Finset.Ico (t : ℕ) k, H.getD (n * (j + 1) + j) 0) *
            ofCoeffs (ps.getD (t : ℕ) []) := by
  cases k with
  | zero =>
    simp [coeffHessStep, ofCoeffs_coeffSub, ofCoeffs_coeffShift, ofCoeffs_coeffScale, sub_mul]
  | succ k =>
    rw [coeffHessStep, ofCoeffs_coeffSub, ofCoeffs_coeffSub, ofCoeffs_coeffShift,
      ofCoeffs_coeffScale, ofCoeffs_coeffHessSum, sub_mul]
    congrm _ - ∑ t, ?_
    rw [Finset.prod_Ico_succ_top (Nat.lt_succ_iff.mp t.isLt)]
    simp only [map_mul]
    ring

theorem coeffHessAux_size (n : ℕ) (H : Array R) : ∀ k, (coeffHessAux n H k).size = k + 1
  | 0 => rfl
  | k + 1 => by rw [coeffHessAux, Array.size_push, coeffHessAux_size n H k]

theorem ofCoeffs_coeffHessAux_getD (n : ℕ) (H : Array R) :
    ∀ k m, m ≤ k → ofCoeffs ((coeffHessAux n H k).getD m []) = hessP n H m
  | 0, m, hm => by
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    simp [coeffHessAux, ofCoeffs_cons, hessP_zero]
  | k + 1, m, hm => by
    rw [coeffHessAux, Array.getD_eq_getD_getElem?, Array.getElem?_push, coeffHessAux_size]
    split_ifs with hmk
    · subst hmk
      rw [Option.getD_some, ofCoeffs_coeffHessStep, hessP_succ]
      simp (disch := omega) only [ofCoeffs_coeffHessAux_getD n H k, ← Finset.prod_Ico_add' _ _ _ 1,
        Nat.add_sub_cancel]
    · rw [← Array.getD_eq_getD_getElem?]
      exact ofCoeffs_coeffHessAux_getD n H k m (by omega)

theorem hessCharPoly_eq_ofCoeffs (n : ℕ) (H : Array R) :
    hessCharPoly n H = ofCoeffs (coeffHessCharPoly n H) := by
  rw [hessCharPoly_eq, coeffHessCharPoly, ofCoeffs_coeffHessAux_getD n H n n le_rfl]

end Mathlib.Tactic.Hessenberg

end
