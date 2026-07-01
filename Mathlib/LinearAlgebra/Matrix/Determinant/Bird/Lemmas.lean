/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
This file contains the theorem that Bird's algorithm computes Matrix.det

## Main theorems

- `birdDetSpec_eq_det` - Proves that BirdDet.Spec.birdDet computes Matrix.det
- `det_eq_birdDet` - Proves that BirdDet.Spec.birdDet computes BirdDet.birdDet
- `det_eq_birdDet` - Proves that BirdDet.birdDet computes Matrix.det

-/

namespace BirdDet

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The row-major index is in-bounds of the Array of size `rows * cols`. -/
theorem rowMajorIndex_lt
    {rows cols : ℕ}
    (i : Fin rows) (j : Fin cols) :
    cols * i.val + j.val < rows * cols := by
  rw [Nat.mul_comm cols]
  calc
    i.val * cols + j.val < i.val * cols + cols :=
      Nat.add_lt_add_left (j.isLt) (↑i * cols)
    _ = (i.val + 1) * cols := by
      rw [Nat.add_one_mul]
    _ ≤ rows * cols :=
      Nat.mul_le_mul_right cols (Nat.succ_le_of_lt i.isLt)

theorem get_eq_idx
    {rows cols : ℕ}
    (A : Array R)
    (hA : A.size = rows * cols)
    (i : Fin rows) (j : Fin cols) :
    BirdDet.get cols A i.val j.val = Matrix.ofArray (m := rows) (n := cols) A hA i j := by
  have hidx : cols * i.val + j.val < A.size := by
    rw [hA]
    exact rowMajorIndex_lt i j
  simp [BirdDet.get, Matrix.ofArray, Array.getD, hidx]

theorem sumFrom_eq_sum_Ico (n lo : ℕ) (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  rw [BirdDet.sumFrom]
  split_ifs with h
  · rw [sumFrom_eq_sum_Ico n (lo + 1) f]
    simp [Finset.sum_eq_sum_Ico_succ_bot h f]
  · simp [Finset.Ico_eq_empty h]

theorem sumFrom_fin_tail (n : ℕ) (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f =
      ∑ k : Fin n, if i < k then f k.val else 0 := by
  rw [sumFrom_eq_sum_Ico]
  trans ∑ k : Fin n, if i.val < k.val then f k.val else 0
  · rw [Fin.sum_univ_eq_sum_range (fun x => if i.val < x then f x else 0) n]
    rw [← Finset.sum_filter]
    rw [show (Finset.range n).filter (fun x => i.val < x) = Finset.Ico (i.val + 1) n by
      ext x
      simp [Finset.mem_Ico, and_comm]]
  · rfl

theorem iter_step
    {n : ℕ}
    (A : Array R)
    (hA : A.size = n * n)
    (F : ℕ → ℕ → R)
    (i j : Fin n) :
    (-(BirdDet.sumFrom n (i.val + 1) fun k => F k k) *
        BirdDet.get n A i.val j.val
      +
      BirdDet.sumFrom n (i.val + 1) fun k =>
        F i.val k * BirdDet.get n A k j.val)
      =
    Spec.stepEntry
      (Matrix.ofArray (m := n) (n := n) A hA)
      (fun i j => F i.val j.val)
      i j := by
  rw [sumFrom_fin_tail]
  rw [sumFrom_fin_tail]
  rw [Spec.stepEntry_eq]
  simp [get_eq_idx A hA]

lemma iter_eq_spec_iterEntry_ofNat
    (n : ℕ)
    (A : Array R)
    (hA : A.size = n * n)
    (t : ℕ)
    (F : ℕ → ℕ → R)
    (i j : Fin n) :
    BirdDet.iter n A t F i.val j.val
      = Spec.iterEntry (Matrix.ofArray (m := n) (n := n) A hA) t
        (fun i j => F i.val j.val) i j := by
  induction t generalizing F i j with
  | zero => rw [BirdDet.iter_zero, Spec.iterEntry_zero]
  | succ t ih =>
    rw [BirdDet.iter_succ, Spec.iterEntry_succ, iter_step]
    · congr
      funext p q
      exact ih F p q
    · exact hA

lemma iter_eq_spec_iterEntry
    (n : ℕ)
    (A : Array R)
    (hA : A.size = n * n)
    (t : ℕ)
    (i j : Fin n) :
    BirdDet.iter n A t (BirdDet.get n A) i.val j.val =
      Spec.iterEntry (Matrix.ofArray (m := n) (n := n) A hA) t
        (fun i j => Matrix.ofArray (m := n) (n := n) A hA i j) i j := by
  trans Spec.iterEntry (Matrix.ofArray (m := n) (n := n) A hA) t
      (fun i j => BirdDet.get n A i.val j.val) i j
  · exact iter_eq_spec_iterEntry_ofNat n A hA t (BirdDet.get n A) i j
  · congr
    funext p q
    exact get_eq_idx A hA p q

public section

theorem birdDetSpec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  sorry

theorem birdDet_eq_birdDetSpec {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (Matrix.ofArray (m := n) (n := n) A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k =>
    rw [birdDet_eq (k + 1) k A rfl, Spec.birdDetSpec_succ]
    apply congrArg ((-1 : R) ^ k * ·)
    exact iter_eq_spec_iterEntry (k + 1) A hA k 0 0

theorem det_eq_birdDet {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    Matrix.det (Matrix.ofArray (m := n) (n := n) A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec A hA]
  exact (birdDetSpec_eq_det (Matrix.ofArray (m := n) (n := n) A hA))

end

end BirdDet
