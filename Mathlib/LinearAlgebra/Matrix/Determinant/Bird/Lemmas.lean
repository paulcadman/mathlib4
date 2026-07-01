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
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
This file connects the flat-array implementation of Bird's determinant
algorithm with `Matrix.det`.

## Main theorems

- `birdDet_eq_birdDetSpec` - Proves that `BirdDet.birdDet` agrees with
  `BirdDet.Spec.birdDet`.
- `det_eq_birdDet` - Proves that `BirdDet.birdDet` computes `Matrix.det`.

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

theorem sumFrom_eq_sum_Ico (n lo : ℕ) (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  rw [BirdDet.sumFrom]
  split_ifs with h
  · rw [sumFrom_eq_sum_Ico n (lo + 1) f]
    simp [Finset.sum_eq_sum_Ico_succ_bot h f]
  · simp [Finset.Ico_eq_empty h]

theorem get_eq_ofArray_apply
    {rows cols : ℕ}
    (A : Array R)
    (hA : A.size = rows * cols)
    (i : Fin rows) (j : Fin cols) :
    BirdDet.get cols A i.val j.val = Matrix.ofArray (m := rows) (n := cols) A hA i j := by
  have hidx : cols * i.val + j.val < A.size := by
    rw [hA]
    exact rowMajorIndex_lt i j
  simp [BirdDet.get, Matrix.ofArray, Array.getD, hidx]

theorem sumFrom_fin_tail (n : ℕ) (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f =
      ∑ k : Fin n, if i < k then f k.val else 0 := by
  rw [sumFrom_eq_sum_Ico]
  trans ∑ k : Fin n, if i.val < k.val then f k.val else 0
  · rw [Fin.sum_univ_eq_sum_range (fun x => if i.val < x then f x else 0) n]
    rw [← Finset.sum_filter]
    have hfilter :
        (Finset.range n).filter (fun x => i.val < x) = Finset.Ico (i.val + 1) n := by
      ext x
      simp [Finset.mem_Ico, and_comm]
    rw [hfilter]
  · rfl

theorem step_bridge_iterMatrix
    {n : ℕ}
    (A : Array R)
    (hA : A.size = n * n)
    (t : ℕ)
    (i j : Fin n)
    (ih : ∀ p q : Fin n,
      BirdDet.iter n A t (BirdDet.get n A) p.val q.val =
        Spec.iterMatrix
          (Matrix.ofArray (m := n) (n := n) A hA)
          t
          p q) :
    BirdDet.iter n A (t + 1) (BirdDet.get n A) i.val j.val =
      Spec.stepEntry
        (Matrix.ofArray (m := n) (n := n) A hA)
        (Spec.iterMatrix
          (Matrix.ofArray (m := n) (n := n) A hA)
          t)
        i j := by
  rw [BirdDet.iter_succ, stepEntry_eq, Spec.stepEntry_eq, sumFrom_fin_tail, sumFrom_fin_tail]
  simp [ih, get_eq_ofArray_apply A hA]

theorem iter_get_eq_spec_iterMatrix
    {n : ℕ}
    (A : Array R)
    (hA : A.size = n * n)
    (t : ℕ)
    (i j : Fin n) :
    BirdDet.iter n A t (BirdDet.get n A) i.val j.val =
      Spec.iterMatrix
        (Matrix.ofArray (m := n) (n := n) A hA)
        t
        i j := by
  induction t generalizing i j with
  | zero =>
    rw [BirdDet.iter_zero, Spec.iterMatrix_zero]
    exact get_eq_ofArray_apply A hA i j
  | succ t ih =>
    rw [Spec.iterMatrix_succ]
    exact step_bridge_iterMatrix A hA t i j ih

public section

theorem birdDet_eq_birdDetSpec {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (Matrix.ofArray (m := n) (n := n) A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k =>
    rw [birdDet_succ, Spec.birdDetSpec_succ_iterMatrix]
    apply congrArg ((-1 : R) ^ k * ·)
    exact iter_get_eq_spec_iterMatrix A hA k 0 0

theorem det_eq_birdDet {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    Matrix.det (Matrix.ofArray (m := n) (n := n) A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec]
  exact birdDetSpec_eq_det _

end

end BirdDet
