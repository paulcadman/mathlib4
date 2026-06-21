/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Data.Matrix.Mul

/-!
# Operations on array-backed matrix literals

This file provides simplification lemmas that keep structural and pointwise operations on
`Matrix.ofArray` values array-backed. In particular, they allow `simp` to evaluate these
operations directly on `!![...]` literals without converting them to nested vector notation.

Matrix multiplication is deliberately excluded: eagerly expanding it is liable to produce large
expressions. Use a dedicated normalization tactic or a dimension-specific theorem instead.
-/

@[expose] public section

namespace Matrix

variable {α β γ : Type*} {m n l o : ℕ}

/-- A transparent version of `Array.ofFn`, used so concrete matrix operations reduce to array
literals during simplification. -/
@[simp]
def literalArrayOfFn : (n : ℕ) → (Fin n → α) → Array α
  | 0, _ => #[]
  | n + 1, f => (literalArrayOfFn n fun i => f i.castSucc).push (f (Fin.last n))

@[simp]
theorem literalArrayOfFn_size (f : Fin n → α) : (literalArrayOfFn n f).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [literalArrayOfFn, ih]

theorem literalArrayOfFn_eq (f : Fin n → α) : literalArrayOfFn n f = Array.ofFn f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [literalArrayOfFn, ih, Array.ofFn_succ]
    exact congr_arg _ (congr_arg f (Fin.ext rfl))

/-- A transparent version of `Fin.divNat`, for reducing concrete row-major indices. -/
@[simp]
def literalDivNat {m n : ℕ} (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| Nat.mul_comm m n ▸ i.is_lt⟩

/-- A transparent version of `Fin.modNat`, for reducing concrete row-major indices. -/
@[simp]
def literalModNat {m n : ℕ} (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ <| Nat.pos_of_mul_pos_left i.pos⟩

theorem literalDivNat_eq {m n : ℕ} (i : Fin (m * n)) : literalDivNat i = i.divNat :=
  Fin.ext rfl

theorem literalModNat_eq {m n : ℕ} (i : Fin (m * n)) : literalModNat i = i.modNat :=
  Fin.ext rfl

/-- Two arrays of the prescribed size define the same matrix exactly when they are equal. -/
@[simp]
theorem ofArray_inj (A B : Array α) (hA : A.size = m * n) (hB : B.size = m * n) :
    ofArray A hA = ofArray B hB ↔ A = B := by
  constructor
  · intro h
    apply Array.ext (hA.trans hB.symm)
    intro k hkA hkB
    let k' : Fin (m * n) := ⟨k, by simpa only [hA] using hkA⟩
    have hk := congr_fun (congr_fun h k'.divNat) k'.modNat
    simpa only [ofArray_apply, Fin.getElem_fin, Fin.coe_mkDivMod,
      Fin.divNat_mkDivMod_modNat] using hk
  · exact fun h => h ▸ rfl

/-- The row-major array obtained by transposing an array-backed matrix. -/
@[simp]
def transposeArray (A : Array α) (hA : A.size = m * n) : Array α :=
  literalArrayOfFn (n * m) fun k => A[Fin.mkDivMod k.modNat k.divNat]

@[simp]
theorem transposeArray_size (A : Array α) (hA : A.size = m * n) :
    (transposeArray A hA).size = n * m :=
  literalArrayOfFn_size _

/-- Transposing an array-backed matrix produces an array-backed matrix. -/
@[simp]
theorem transpose_ofArray (A : Array α) (hA : A.size = m * n) :
    (ofArray A hA)ᵀ = ofArray (transposeArray A hA) (transposeArray_size A hA) := by
  ext i j
  simp only [transpose_apply, ofArray_apply, transposeArray, literalArrayOfFn_eq,
    Array.getElem_ofFn,
    Fin.getElem_fin, Fin.coe_mkDivMod]
  change A[Fin.mkDivMod j i] =
    A[Fin.mkDivMod (Fin.mkDivMod i j).modNat (Fin.mkDivMod i j).divNat]
  simp

/-- Mapping a function over an array-backed matrix maps it over the underlying array. -/
@[simp]
theorem map_ofArray (f : α → β) (A : Array α) (hA : A.size = m * n) :
    (ofArray A hA).map f =
      ofArray (A.map f) (by simpa only [Array.size_map] using hA) := by
  ext i j
  simp

/-- Negating an array-backed matrix negates each element of its underlying array. -/
@[simp]
theorem neg_ofArray [Neg α] (A : Array α) (hA : A.size = m * n) :
    -ofArray A hA =
      ofArray (A.map (-·)) (by simpa only [Array.size_map] using hA) := by
  ext i j
  simp

/-- Scalar multiplication of an array-backed matrix acts on its underlying array. -/
@[simp]
theorem smul_ofArray [SMul β α] (r : β) (A : Array α) (hA : A.size = m * n) :
    r • ofArray A hA =
      ofArray (A.map (r • ·)) (by simpa only [Array.size_map] using hA) := by
  ext i j
  simp

/-- Adding array-backed matrices combines their underlying arrays pointwise. -/
@[simp]
theorem add_ofArray [Add α] (A B : Array α) (hA : A.size = m * n) (hB : B.size = m * n) :
    ofArray A hA + ofArray B hB =
      ofArray (A.zipWith (· + ·) B)
        (by simp only [Array.size_zipWith, hA, hB, min_self]) := by
  ext i j
  simp

/-- Subtracting array-backed matrices combines their underlying arrays pointwise. -/
@[simp]
theorem sub_ofArray [Sub α] (A B : Array α) (hA : A.size = m * n) (hB : B.size = m * n) :
    ofArray A hA - ofArray B hB =
      ofArray (A.zipWith (· - ·) B)
        (by simp only [Array.size_zipWith, hA, hB, min_self]) := by
  ext i j
  simp

/-- The row-major array obtained by taking a submatrix of an array-backed matrix. -/
@[simp]
def submatrixArray (A : Array α) (hA : A.size = m * n) (r : Fin l → Fin m)
    (c : Fin o → Fin n) : Array α :=
  literalArrayOfFn (l * o) fun k => A[Fin.mkDivMod (r (literalDivNat k)) (c (literalModNat k))]

@[simp]
theorem submatrixArray_size (A : Array α) (hA : A.size = m * n) (r : Fin l → Fin m)
    (c : Fin o → Fin n) : (submatrixArray A hA r c).size = l * o :=
  literalArrayOfFn_size _

/-- A submatrix of an array-backed matrix is array-backed. -/
@[simp 1100]
theorem submatrix_ofArray (A : Array α) (hA : A.size = m * n) (r : Fin l → Fin m)
    (c : Fin o → Fin n) :
    (ofArray A hA).submatrix r c =
      ofArray (submatrixArray A hA r c) (submatrixArray_size A hA r c) := by
  ext i j
  simp only [submatrix_apply, ofArray_apply, submatrixArray, literalArrayOfFn_eq,
    literalDivNat_eq, literalModNat_eq, Array.getElem_ofFn,
    Fin.getElem_fin, Fin.coe_mkDivMod]
  change A[Fin.mkDivMod (r i) (c j)] =
    A[Fin.mkDivMod (r (Fin.mkDivMod i j).divNat) (c (Fin.mkDivMod i j).modNat)]
  simp

/-- A transparent finite vector tabulator. -/
@[simp]
def literalFinVec : (n : ℕ) → (Fin n → α) → Fin n → α
  | 0, _ => ![]
  | n + 1, f => vecCons (f 0) (literalFinVec n fun i => f i.succ)

theorem literalFinVec_eq (f : Fin n → α) : literalFinVec n f = f := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    ext i
    refine i.cases ?_ fun i => ?_
    · rfl
    · simpa [literalFinVec] using congr_fun (ih (fun i => f i.succ)) i

/-- Array-aware evaluation of matrix-vector multiplication.

Unlike matrix multiplication, this expands only one finite sum for each output entry.
-/
@[simp]
def mulVecArray [Mul α] [Add α] [Zero α] (A : Array α) (hA : A.size = m * n)
    (v : Fin n → α) : Fin m → α :=
  literalFinVec m fun i => FinVec.sum fun j => A[Fin.mkDivMod i j] * v j

/-- Multiplying an array-backed matrix by a vector uses the array-aware evaluator. -/
@[simp]
theorem mulVec_ofArray [NonUnitalNonAssocSemiring α] (A : Array α) (hA : A.size = m * n)
    (v : Fin n → α) : ofArray A hA *ᵥ v = mulVecArray A hA v := by
  ext i
  rw [mulVecArray, literalFinVec_eq]
  simp [mulVec, dotProduct]

end Matrix
