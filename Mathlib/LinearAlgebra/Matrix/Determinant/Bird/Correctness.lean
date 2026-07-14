/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Functor

/-!
# Correctness of Bird's determinant algorithm

This file contains a proof that Bird's division-free algorithm computes
`Matrix.det`, in both its matrix form `BirdDet.Spec.birdDet`
(`birdDetSpec_eq_det`) and its flat-array form `BirdDet.birdDet`
(`det_eq_birdDet`), formalizing the combinatorial argument of

  R. S. Bird, *A simple division-free algorithm for computing determinants*,
  Information Processing Letters 111 (2011) 1072–1074.

## Correspondence with the paper

* A word of length `p` over {1 ...,n}, is a tuple `Fin p → Fin n`, NB: indices are shifted.
* `f[α, β]`, the minor on rows `α` and columns `β`, is `(A.submatrix α β).det`.
* `f[iα, jα]`, a bordered minor, is `bminor A i j α`, with the word `iα` spelled
  `Fin.cons i α`
* `f[α, α]`, a principal minor, is `pminor A α`.
* `βᵢ = [i+1, ..., n]`, the symbols greater than `i`.
* `Sₚ(βᵢ)`, the length `p` subsequences of `βᵢ`, is `S p i`.

The theorem names `paper_eq1`, ..., `paper_eq5` follow Bird's numbering.

## Main results

- `BirdDet.birdDetSpec_eq_det`: `Matrix.det` computes the same determinant as `BirdDet.Spec.birdDet`
- `BirdDet.det_eq_birdDet`: `Matrix.det` computes the same determinant as `BirdDet.birdDet`
-/

namespace BirdDet

open scoped BigOperators

-- TODO: Make A matrix a variable
-- TODO: Make Eq1 a variable - comment on use of induction hypothesis in following theorems, eq1_ih
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- `∑` over `Finset.Ioi i` as an `if`-guarded sum over all of `Fin n`. -/
theorem sum_Ioi_eq_sum_ite {M : Type*} [AddCommMonoid M] (i : Fin n) (f : Fin n → M) :
    ∑ k ∈ Finset.Ioi i, f k = ∑ k : Fin n, if i < k then f k else 0 := by
  rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- `S p i` is Bird's `Sₚ(βᵢ)`: strictly increasing words of length `p` over the
alphabet `βᵢ`. -/
abbrev S (p : ℕ) (i : Fin n) : Finset (Fin p → Fin n) :=
  {α : Fin p → Fin n | StrictMono α ∧ ∀ q, i < α q}

/-- The base case of equation (1): `S₀(α) = {ε}`, the singleton of the empty
word `ε`. -/
theorem S_zero (i : Fin n) : S 0 i = {![]} := by
  ext α
  simp [S, Subsingleton.strictMono, eq_iff_true_of_subsingleton]

/-- Bird's bordered minor `f[iα, jα]`. -/
abbrev bminor (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) {p : ℕ}
    (α : Fin p → Fin n) : R :=
  (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

/-- Bird's principal minor `f[α, α]`. -/
abbrev pminor (A : Matrix (Fin n) (Fin n) R) {p : ℕ} (α : Fin p → Fin n) : R :=
  (A.submatrix α α).det

/-- Bird's equation (1) (p. 1072): `x^(p)_ij = (-1)^p ∑ { f[iα, jα] | α ∈ S_p(βᵢ) }` -/
abbrev Eq1 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) : Prop :=
  Spec.iterMatrix A p =
    .of fun i j ↦ (-1 : R) ^ p • ∑ α ∈ S p i, bminor A i j α

/-! ## Decomposition `S_{p+1}(βᵢ) = { kα | k ∈ βᵢ, α ∈ S_p(β_k) }` -/

/-- Deleting a symbol of a word in `S (p+1) i` keeps it in `S p i`. -/
theorem removeNth_mem_S {p : ℕ} {i : Fin n} {α : Fin (p + 1) → Fin n}
    (hα : α ∈ S (p + 1) i) (t : Fin (p + 1)) :
    t.removeNth α ∈ S p i := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
  obtain ⟨hmono, hbound⟩ := hα
  constructor
  · apply hmono.comp
    exact Fin.strictMono_succAbove t
  · intro q
    apply hbound

/-- The tail of a word in `S (p+1) i` lies in `S p (α 0)`. -/
theorem tail_mem_S {p : ℕ} {i : Fin n} {α : Fin (p + 1) → Fin n}
    (hα : α ∈ S (p + 1) i) : Fin.tail α ∈ S p (α 0) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
  obtain ⟨hmono, _⟩ := hα
  constructor
  · apply hmono.comp
    exact Fin.strictMono_succ
  · intro q
    apply hmono
    exact Fin.succ_pos q

/-- `Fin.cons` of a strict lower bound onto a sorted word is sorted. -/
theorem strictMono_cons {q : ℕ} {i : Fin n} {α : Fin q → Fin n}
    (hα : StrictMono α) (hi : ∀ t, i < α t) :
    StrictMono (Fin.cons i α : Fin (q + 1) → Fin n) := by
  cases q with
  | zero => simp [Fin.strictMono_iff_lt_succ]
  | succ q => exact strictMono_vecCons.mpr ⟨hi 0, hα⟩


-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.isDefEq true in
theorem foo (p : ℕ) (i : Fin n) :
  S (p + 1) i =
    Finset.image
      (Function.uncurry Fin.cons)
      ((Finset.Ioi i ×ˢ Finset.univ).filter (Function.uncurry fun (k : Fin n) (α : Fin p → Fin n) =>
          α ∈ S p k)) := by
  sorry

-- Classical is for the Monad instance of Finset, Finset.bind needs classical
open Classical in
theorem bar (p : ℕ) (i : Fin n) :
  S (p + 1) i = do
    let k ← Finset.Ioi i
    let α ← S p k
    return Fin.cons k α := by
  sorry

theorem sum_S_succ (p : ℕ) (i : Fin n)
    (g : (Fin (p + 1) → Fin n) → R) :
    ∑ α ∈ S (p + 1) i, g α = ∑ k ∈ Finset.Ioi i, ∑ u ∈ S p k, g (Fin.cons k u) := by
  sorry

-- ⊢ (-1) ^ (p + 1) * ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p k, bminor A k k α =
--   (-1) ^ (p + 1) * ∑ x ∈ (Finset.Ioi i).sup fun k ↦ Finset.image (Fin.cons k) (S p k), pminor A x
--
--

lemma baz {γ δ : Type*} [DecidableEq δ] (s1 : Finset γ) (s2 : γ → Finset δ) (f : δ → R) :
    ∑ x ∈ s1.sup s2, f x =
      ∑ k ∈ s1, ∑ y ∈ s2 k, f y := by
  symm
  rw [Finset.sum_sigma']
  -- refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
  -- · exact fun x _ ↦ x.2
  -- · sorry
  sorry

/-! ## Equations (2) and (3): substituting the induction hypothesis -/

/-- Bird's equation (2) -/
theorem paper_eq2 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i : Fin n)
    (h1 : Eq1 A p) :
    -Spec.diagSum (Spec.iterMatrix A p) i
      = (-1 : R) ^ (p + 1) • ∑ α ∈ S (p + 1) i, pminor A α := by
  calc
    -Spec.diagSum (Spec.iterMatrix A p) i
        = (-1 : R) ^ (p + 1) • ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p k, bminor A k k α := by
          unfold Spec.diagSum
          rw [h1, ← sum_Ioi_eq_sum_ite]
          simp only [Matrix.of_apply, smul_eq_mul, ← Finset.mul_sum]
          ring
    _ = (-1 : R) ^ (p + 1) • ∑ α ∈ S (p + 1) i, pminor A α := by
          rw [bar]

          simp
          unfold bminor pminor

          -- TODO: restate bar to look like the output of simp
          -- rw [sum_S_succ]

/-- One step of Bird's scalar recurrence, split into diagonal and tail parts. -/
theorem iter_succ_entry (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i j : Fin n) :
    Spec.iterMatrix A (p + 1) i j
      = -Spec.diagSum (Spec.iterMatrix A p) i * A i j
        + ∑ k ∈ Finset.Ioi i, Spec.iterMatrix A p i k * A k j := by
  rw [sum_Ioi_eq_sum_ite]
  simp [Spec.iterMatrix, Spec.iterEntry, Spec.stepEntry, Spec.diagTerm, Spec.tailSum]

/-- Bird's equation (3) -/
theorem paper_eq3 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i j : Fin n)
    (h1 : Eq1 A p) :
    Spec.iterMatrix A (p + 1) i j
      = (-1 : R) ^ (p + 1) • (∑ α ∈ S (p + 1) i, pminor A α * A i j
        - ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j) := by
  unfold Eq1 at h1
  rw [iter_succ_entry, paper_eq2 _ _ _ h1, h1]
  simp only [smul_eq_mul, Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

/-! ## Equation (5): first-column Laplace expansion -/

lemma fin_cons_succ (p : ℕ) (α : Fin (p + 1) → Fin n) (i : Fin n) :
    α = Fin.cons i α ∘ Fin.succ :=
  List.ofFn_inj.mp rfl

lemma fin_cons_succAbove (p : ℕ) (α : Fin (p + 1) → Fin n) (i : Fin n) (s : Fin (p + 1)) :
    Fin.cons i α ∘ s.succ.succAbove = Fin.cons i (s.removeNth α) := by
  funext q
  cases q using Fin.cases with
  | zero => rfl
  | succ t =>
    simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]
    rfl

lemma fin_cons_removeWith (p : ℕ) (α : Fin (p + 1) → Fin n) (s : Fin (p + 1)) :
    -- TODO: put complicated part on the LHS (might work better with simp)
    -- TODO: Consider turning function composition into function application
    α = Fin.cons (α s) (s.removeNth α) ∘ Fin.cycleRange s := by
  simp only [Fin.cons_comp_cycleRange, Fin.insertNth_removeNth, Function.update_eq_self]
  -- rw [Fin.cons_comp_cycleRange, Fin.insertNth_self_removeNth]

/-- First-column Laplace expansion of a bordered minor -/
theorem det_bordered_expand (A : Matrix (Fin n) (Fin n) R) (p : ℕ)
    (α : Fin (p + 1) → Fin n) (i j : Fin n) :
    bminor A i j α =
      pminor A α * A i j -
      ∑ s : Fin (p + 1), bminor A i (α s) (s.removeNth α) * A (α s) j := by
  unfold pminor bminor
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    Matrix.submatrix_apply, Fin.cons_zero, one_mul, Fin.succAbove_zero, Matrix.submatrix_submatrix,
    Fin.val_succ, Fin.cons_succ, Finset.sum_neg_distrib]
  rw [← fin_cons_succ, ← fin_cons_succ]
  congr 1
  · simp only [mul_comm]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x xh
    rw [mul_right_comm, ← neg_mul]
    congr
    rw [fin_cons_succAbove]
    -- TODO: try using calc
    conv_lhs => enter [2, 1, 3]; rw [fin_cons_removeWith p α x]
    conv_lhs => enter [2, 1, 2]; rw [← Function.comp_id (Fin.cons i (x.removeNth α))]
    rw [← Matrix.submatrix_submatrix, Matrix.det_permute', Fin.sign_cycleRange]
    push_cast
    rw [← mul_assoc, ← pow_add]
    simp

/-- Bird's equation (5) -/
theorem paper_eq5 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i j : Fin n) :
    ∑ α ∈ S (p + 1) i, bminor A i j α
      = ∑ α ∈ S (p + 1) i, pminor A α * A i j
        - ∑ α ∈ S (p + 1) i, ∑ t : Fin (p + 1),
            bminor A i (α t) (t.removeNth α) * A (α t) j := by
  rw [Finset.sum_congr rfl (fun α _ => det_bordered_expand A p α i j), Finset.sum_sub_distrib]

/-! ## The exchange step: reindex by sorted insert/delete -/

theorem det_eq_zero_of_symbol {p : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (α : Fin p → Fin n) (i : Fin n) {k : Fin n} {q : Fin p} (hq : α q = k) :
    bminor A i k α = 0 := by
  refine Matrix.det_zero_of_column_eq (Fin.succ_ne_zero q).symm fun r => ?_
  simp only [Matrix.submatrix_apply, Fin.cons_zero, Fin.cons_succ]
  rw [hq]

-- lemma prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {I : Finset κ}
--     (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
--     ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
--   rw [prod_image']
--   exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm


/-- The exchange step, the off-diagonal sums of equations (3) and (5) agree -/

-- TODO: Try to remove the `A k j`, `A (α' t) j` factors to match the paper more closely
theorem exchange (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i j : Fin n) :
    ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j
      = ∑ α' ∈ S (p + 1) i, ∑ t : Fin (p + 1),
          bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  sorry

/-- Bird's equation (4) -/
theorem paper_eq4 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i j : Fin n) :
    ∑ α ∈ S (p + 1) i, pminor A α * A i j
      - ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j
      = ∑ α ∈ S (p + 1) i, bminor A i j α := by
  rw [paper_eq5 A p i j]
  congr 1

  exact exchange A p i j

/-! ## Bird's Equation (1) -/
theorem paper_eq1 (A : Matrix (Fin n) (Fin n) R) (p : ℕ) : Eq1 A p := by
  induction p with
  | zero =>
    ext i j
    simp [S_zero, bminor]
  | succ p ih =>
    ext i j
    rw [Matrix.of_apply, paper_eq3 A p i j ih, paper_eq4 A p i j]

/-! ## instantiating equation (1) to prove Theorem 1 -/

/-- A strictly monotone self-map of `Fin m` is the identity. -/
theorem strictMono_eq_id {f : Fin m → Fin m} (hf : StrictMono f) : f = id := by
  funext
  apply le_antisymm
  · exact StrictMono.apply_le hf
  · exact StrictMono.le_apply hf

theorem cons_zero_succ (k : ℕ) :
    (Fin.cons 0 Fin.succ : Fin (k + 1) → Fin (k + 1)) = id := by
  funext q
  cases q using Fin.cases with
  | zero => rfl
  | succ t => rfl

/-- The full-length bordered minor at the origin is the whole determinant:
`f[[1 .. n], [1 .. n]] = |A|` -/
theorem bminor_zero_succ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    bminor A 0 0 Fin.succ = A.det := by
  unfold bminor
  rw [cons_zero_succ, Matrix.submatrix_id_id]

theorem S_zero_full (k : ℕ) :
    S k (0 : Fin (k + 1)) = {(Fin.succ : Fin k → Fin (k + 1))} := by
  ext α
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hmono, hbound⟩
    have hid : (Fin.cons 0 α : Fin (k + 1) → Fin (k + 1)) = id :=
      strictMono_eq_id (strictMono_cons hmono hbound)
    funext q
    have hq := congrFun hid q.succ
    simpa using hq
  · rintro rfl
    exact ⟨Fin.strictMono_succ, fun q => Fin.succ_pos q⟩

/-- Bird's Theorem 1 -/
public theorem birdDetSpec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  cases n with
  | zero =>
    rw [Spec.birdDetSpec_zero]
    exact Matrix.det_fin_zero
  | succ k =>
    rw [Spec.birdDetSpec_succ_iterMatrix, paper_eq1 A k,
      Matrix.of_apply, S_zero_full k, Finset.sum_singleton,
      bminor_zero_succ A, smul_eq_mul,
      ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

/-! ## The flat-array implementation -/

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

/-- The flat-array algorithm `BirdDet.birdDet` computes the same determinant as
`BirdDet.Spec.birdDet`. -/
theorem birdDet_eq_birdDetSpec {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (Matrix.ofArray (m := n) (n := n) A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k =>
    rw [birdDet_succ, Spec.birdDetSpec_succ_iterMatrix]
    apply congrArg ((-1 : R) ^ k * ·)
    exact iter_get_eq_spec_iterMatrix A hA k 0 0

/-- **Bird's algorithm is correct.** `BirdDet.birdDet n A` computes the determinant
of the `n × n` matrix whose entries are stored in row-major order in `A`. -/
theorem det_eq_birdDet {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    Matrix.det (Matrix.ofArray (m := n) (n := n) A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec]
  exact birdDetSpec_eq_det (Matrix.ofArray A hA)

end

end BirdDet
