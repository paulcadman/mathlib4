/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs
public import Mathlib.Tactic.Hessenberg.Recurrence
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness of the Hessenberg characteristic polynomial recurrence
-/

open Polynomial Matrix

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The leading `k × k` block of the total entry function `g`. -/
def gBlock {α : Type*} (g : ℕ → ℕ → α) (k : ℕ) : Matrix (Fin k) (Fin k) α :=
  of fun i j => g i j

@[simp]
theorem gBlock_apply {α : Type*} (g : ℕ → ℕ → α) (k : ℕ) (i j : Fin k) :
    gBlock g k i j = g i j := rfl

/-! ## The last-column expansion of a Hessenberg determinant -/

/-- `Fin k`, split at `i` into `Fin i ⊕ Fin (k - i)`. -/
def finSplit (k : ℕ) (i : Fin (k + 1)) : Fin (i : ℕ) ⊕ Fin (k - i) ≃ Fin k :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.isLt)))

/-- For Hessenberg `g`, the minor of the leading `(k + 1)`-block omitting row `i` and the last
column, split at `i`, is block triangular: the leading `i`-block in the top left, and in the
bottom right the entries at rows `i + 1, …, k` and columns `i, …, k - 1`. -/
theorem submatrix_gBlock_succAbove (g : ℕ → ℕ → R) (hg : ∀ i j, j + 1 < i → g i j = 0) (k : ℕ)
    (i : Fin (k + 1)) :
    ((gBlock g (k + 1)).submatrix i.succAbove Fin.castSucc).submatrix (finSplit k i)
        (finSplit k i) =
      fromBlocks (gBlock g i) (of fun (a : Fin (i : ℕ)) (b : Fin (k - i)) => g a (i + b)) 0
        (of fun a b : Fin (k - i) => g (i + a + 1) (i + b)) := by
  ext (a | a) (b | b)
  · simp [finSplit, Fin.succAbove, Fin.lt_def]
  · simp [finSplit, Fin.succAbove, Fin.lt_def]
  · simpa [finSplit, Fin.succAbove, Fin.lt_def] using hg (i + a + 1) b (by omega)
  · simp [finSplit, Fin.succAbove, Fin.lt_def]

/-- The bottom right block of `submatrix_gBlock_succAbove` is upper triangular. -/
theorem isUpperTriangular_of_hessenberg (g : ℕ → ℕ → R) (hg : ∀ i j, j + 1 < i → g i j = 0)
    (i m : ℕ) : (of fun a b : Fin m => g (i + a + 1) (i + b)).IsUpperTriangular :=
  fun _ _ hab => hg _ _ (Nat.succ_lt_succ (Nat.add_lt_add_left hab i))

/-- The determinant of the minor of `submatrix_gBlock_succAbove`: the leading `i`-block's, times
the subdiagonal entries of `g` between rows `i + 1` and `k`. -/
theorem det_gBlock_submatrix_succAbove (g : ℕ → ℕ → R) (hg : ∀ i j, j + 1 < i → g i j = 0)
    (k : ℕ) (i : Fin (k + 1)) :
    ((gBlock g (k + 1)).submatrix i.succAbove Fin.castSucc).det =
      (gBlock g i).det * ∏ j ∈ Finset.Ico (i : ℕ) k, g (j + 1) j := by
  rw [← det_submatrix_equiv_self (finSplit k i), submatrix_gBlock_succAbove g hg,
    det_fromBlocks_zero₂₁, det_of_isUpperTriangular (isUpperTriangular_of_hessenberg g hg i _),
    Finset.prod_Ico_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
  rfl

/-- The determinant of the leading `(k + 1)`-block of a Hessenberg `g`, expanded along its last
column: row `i` contributes its last entry, times the determinant of the leading `i`-block, times
the negated subdiagonal entries below row `i`. -/
theorem det_gBlock_succ (g : ℕ → ℕ → R) (hg : ∀ i j, j + 1 < i → g i j = 0) (k : ℕ) :
    (gBlock g (k + 1)).det =
      ∑ i : Fin (k + 1), g i k *
        ((gBlock g i).det * ∏ j ∈ Finset.Ico (i : ℕ) k, -g (j + 1) j) := by
  rw [det_succ_column _ (Fin.last k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.succAbove_last, gBlock_apply, Fin.val_last, det_gBlock_submatrix_succAbove g hg,
    Finset.prod_neg, Nat.card_Ico, show (i : ℕ) + k = k - i + 2 * i by omega,
    pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  ring

/-! ## The characteristic polynomial recurrence -/

/-- The entries of the characteristic matrix of a leading block of `g`, as a total function. -/
noncomputable def charEntry (g : ℕ → ℕ → R) (i j : ℕ) : R[X] :=
  if i = j then X - C (g i j) else -C (g i j)

@[simp]
theorem charEntry_self (g : ℕ → ℕ → R) (i : ℕ) : charEntry g i i = X - C (g i i) :=
  ite_eq_left rfl

theorem charEntry_of_ne (g : ℕ → ℕ → R) {i j : ℕ} (h : i ≠ j) : charEntry g i j = -C (g i j) :=
  ite_eq_right h

theorem charEntry_hessenberg (g : ℕ → ℕ → R) (hg : ∀ i j, j + 1 < i → g i j = 0) :
    ∀ i j, j + 1 < i → charEntry g i j = 0 := fun i j h => by
  rw [charEntry_of_ne g (by omega), hg i j h, map_zero, neg_zero]

theorem charmatrix_gBlock (g : ℕ → ℕ → R) (k : ℕ) :
    (gBlock g k).charmatrix = gBlock (charEntry g) k := by
  ext i j : 2
  by_cases h : i = j
  · subst h
    simp
  · simp [charmatrix_apply_ne _ _ _ h, charEntry_of_ne g (Fin.val_ne_of_ne h)]

/-- The negated subdiagonal of the characteristic matrix is the subdiagonal of `g`, under `C`. -/
theorem prod_Ico_neg_charEntry (g : ℕ → ℕ → R) (t k : ℕ) :
    ∏ j ∈ Finset.Ico t k, -charEntry g (j + 1) j = C (∏ j ∈ Finset.Ico t k, g (j + 1) j) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [charEntry_of_ne g j.succ_ne_self, neg_neg]

/-- The Hessenberg charpoly recurrence at the matrix level: the last-column expansion of the
characteristic determinant of the `(k + 1)`-block. -/
theorem gBlock_charpoly_succ (g : ℕ → ℕ → R) (hg : ∀ i j, j + 1 < i → g i j = 0) (k : ℕ) :
    (gBlock g (k + 1)).charpoly =
      (X - C (g k k)) * (gBlock g k).charpoly -
        ∑ t : Fin k,
          C (g t k * ∏ j ∈ Finset.Ico (t : ℕ) k, g (j + 1) j) * (gBlock g t).charpoly := by
  simp only [charpoly, charmatrix_gBlock]
  rw [det_gBlock_succ _ (charEntry_hessenberg g hg) k, Fin.sum_univ_castSucc, sub_eq_add_neg,
    ← Finset.sum_neg_distrib, add_comm]
  simp only [Fin.val_castSucc, Fin.val_last, charEntry_self, prod_Ico_neg_charEntry,
    Finset.Ico_self, Finset.prod_empty, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [charEntry_of_ne g (Nat.ne_of_lt t.isLt), C_mul]
  ring

/-- The recurrence computes the charpolys of the leading blocks. -/
theorem hessP_eq_charpoly (n : ℕ) (H : Array R)
    (hg : ∀ i j : ℕ, j + 1 < i → H.getD (n * i + j) 0 = 0) (m : ℕ) :
    hessP n H m = (gBlock (fun i j => H.getD (n * i + j) 0) m).charpoly := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => rw [hessP_zero, charpoly, det_isEmpty]
    | succ k =>
      rw [hessP_succ, gBlock_charpoly_succ _ hg k, ih k (by omega)]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [ih t (by omega), ← Finset.prod_Ico_add' _ _ _ 1]
      simp only [Nat.add_sub_cancel]

/-- A row-major array of an upper Hessenberg matrix, read as a total entry function, vanishes
below the subdiagonal (and, by `getD`, outside the array). -/
theorem getD_eq_zero_of_isUpperHessenberg (Harr : Array R) (h : Harr.size = n * n)
    (hH : (Matrix.ofArray Harr h).IsUpperHessenberg) {i j : ℕ} (hij : j + 1 < i) :
    Harr.getD (n * i + j) 0 = 0 := by
  rcases Nat.lt_or_ge i n with hi | hi
  · simpa only [ofArray_eq_of_getD, of_apply] using
      isUpperHessenberg_fin_iff.mp hH ⟨i, hi⟩ ⟨j, by omega⟩ hij
  · rw [Array.getD_eq_getD_getElem?, Option.getD_eq_iff, Array.getElem?_eq_none_iff, h]
    exact .inr ⟨(Nat.mul_le_mul_left n hi).trans (Nat.le_add_right _ _), rfl⟩

/-- The characteristic polynomial of an upper Hessenberg matrix is computed by the
leading-principal-block recurrence. -/
public theorem charpoly_ofArray_eq_hessCharPoly (Harr : Array R) (h : Harr.size = n * n)
    (hH : IsUpperHessenberg (Matrix.ofArray Harr h)) :
    (Matrix.ofArray Harr h).charpoly = hessCharPoly n Harr := by
  rw [hessCharPoly_eq, ofArray_eq_of_getD,
    hessP_eq_charpoly n Harr fun _ _ hij => getD_eq_zero_of_isUpperHessenberg Harr h hH hij]
  rfl

end Mathlib.Tactic.Hessenberg
