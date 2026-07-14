/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Lemmas for concrete matrices `Matrix (Fin m) (Fin n) α`

This file contains alternative definitions of common operators on matrices that expand
definitionally to the expected expression when evaluated on `!![]` notation.

This allows "proof by reflection", where we prove `A = !![A 0 0, A 0 1;  A 1 0, A 1 1]` by defining
`Matrix.etaExpand A` to be equal to the RHS definitionally, and then prove that
`A = eta_expand A`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `Matrix.transposeᵣ`
* `dotProductᵣ`
* `Matrix.mulᵣ`
* `Matrix.mulVecᵣ`
* `Matrix.vecMulᵣ`
* `Matrix.etaExpand`

-/

@[expose] public section


open Matrix

namespace Matrix

variable {l m n : ℕ} {α : Type*}

/-- `∀` with better defeq for `∀ x : Matrix (Fin m) (Fin n) α, P x`. -/
def Forall : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | m, n, P => FinVec.Forall fun xs : Fin (m * n) → α =>
    P (Matrix.ofArray (List.ofFn xs).toArray (by simp only [List.toArray_ofFn, Array.size_ofFn]))

/-- This can be used to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm
```
-/
theorem forall_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Forall P ↔ ∀ x, P x := by
  intro m n P
  simp only [Forall, FinVec.forall_iff]
  constructor
  · intro h A
    simpa [Matrix.ofArray_toArray_ofFn A] using
      h (fun k : Fin (m * n) => A k.divNat k.modNat)
  · intro h xs
    exact h _

example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
    (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
  (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : Matrix (Fin m) (Fin n) α, P x`. -/
def Exists : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | m, n, P => FinVec.Exists fun xs : Fin (m * n) → α =>
    P (Matrix.ofArray (List.ofFn xs).toArray (by simp only [List.toArray_ofFn, Array.size_ofFn]))

/-- This can be used to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm
```
-/
theorem exists_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Exists P ↔ ∃ x, P x := by
  intro m n P
  simp only [Exists, FinVec.exists_iff]
  constructor
  · rintro ⟨xs, hxs⟩
    exact ⟨_, hxs⟩
  · rintro ⟨A, hA⟩
    use fun k => A k.divNat k.modNat
    simpa [Matrix.ofArray_toArray_ofFn A] using hA

example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
    (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
  (exists_iff _).symm

/-- `Matrix.transpose` with better defeq for `Fin` -/
def transposeᵣ : ∀ {m n}, Matrix (Fin m) (Fin n) α → Matrix (Fin n) (Fin m) α
  | m, n, A =>
    Matrix.ofArray (List.ofFn (fun k : Fin (n * m) => A k.modNat k.divNat)).toArray
      (by simp only [List.toArray_ofFn, Array.size_ofFn])

/-- This can be used to prove
```lean
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ_eq _).symm
```
-/
@[simp]
theorem transposeᵣ_eq {m n} (A : Matrix (Fin m) (Fin n) α) : transposeᵣ A = transpose A := by
  ext i j
  simp only [transposeᵣ, Matrix.ofArray_apply, List.toArray_ofFn, Fin.getElem_fin,
    Fin.coe_mkDivMod, Array.getElem_ofFn, Matrix.transpose_apply]
  change A (Fin.mkDivMod i j).modNat (Fin.mkDivMod i j).divNat = A j i
  simp

example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] :=
  (transposeᵣ_eq _).symm

/-- `dotProduct` with better defeq for `Fin` -/
def dotProductᵣ [Mul α] [Add α] [Zero α] {m} (a b : Fin m → α) : α :=
  FinVec.sum <| FinVec.seq (FinVec.map (· * ·) a) b

/-- This can be used to prove
```lean
example (a b c d : α) [Mul α] [AddCommMonoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm
```
-/
@[simp]
theorem dotProductᵣ_eq [Mul α] [AddCommMonoid α] {m} (a b : Fin m → α) :
    dotProductᵣ a b = a ⬝ᵥ b := by
  simp_rw [dotProductᵣ, dotProduct, FinVec.sum_eq, FinVec.seq_eq, FinVec.map_eq,
      Function.comp_apply]

example (a b c d : α) [Mul α] [AddCommMonoid α] : ![a, b] ⬝ᵥ ![c, d] = a * c + b * d :=
  (dotProductᵣ_eq _ _).symm

/-- `Matrix.mul` with better defeq for `Fin` -/
def mulᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin l) (Fin n) α :=
  Matrix.ofArray (List.ofFn (fun k : Fin (l * n) =>
    dotProductᵣ (fun i : Fin m => A k.divNat i) fun i : Fin m => B i k.modNat)).toArray
      (by simp only [List.toArray_ofFn, Array.size_ofFn])

/-- This can be used to prove
```lean
example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] * !![b₁₁, b₁₂;
                    b₂₁, b₂₂] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁, a₁₁*b₁₂ + a₁₂*b₂₂;
     a₂₁*b₁₁ + a₂₂*b₂₁, a₂₁*b₁₂ + a₂₂*b₂₂] :=
(mulᵣ_eq _ _).symm
```
-/
@[simp]
theorem mulᵣ_eq [Mul α] [AddCommMonoid α] (A : Matrix (Fin l) (Fin m) α)
    (B : Matrix (Fin m) (Fin n) α) : mulᵣ A B = A * B := by
  ext i j
  simp only [mulᵣ, Matrix.ofArray_apply, List.toArray_ofFn, Fin.getElem_fin,
    Fin.coe_mkDivMod, Array.getElem_ofFn, Matrix.mul_apply', dotProductᵣ_eq]
  change ((fun i_1 => A (Fin.mkDivMod i j).divNat i_1) ⬝ᵥ
      fun i_1 => B i_1 (Fin.mkDivMod i j).modNat) =
    ((fun i_1 => A i i_1) ⬝ᵥ fun i_1 => B i_1 j)
  simp

example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  (mulᵣ_eq _ _).symm

/-- `Matrix.mulVec` with better defeq for `Fin` -/
def mulVecᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m → α) : Fin l → α :=
  FinVec.map (fun a => dotProductᵣ a v) A

/-- This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁*b₁ + a₁₂*b₂, a₂₁*b₁ + a₂₂*b₂] :=
(mulVecᵣ_eq _ _).symm
```
-/
@[simp]
theorem mulVecᵣ_eq [NonUnitalNonAssocSemiring α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m → α) :
    mulVecᵣ A v = A *ᵥ v := by
  simp [mulVecᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁ * b₁ + a₁₂ * b₂, a₂₁ * b₁ + a₂₂ * b₂] :=
  (mulVecᵣ_eq _ _).symm

/-- `Matrix.vecMul` with better defeq for `Fin` -/
def vecMulᵣ [Mul α] [Add α] [Zero α] (v : Fin l → α) (A : Matrix (Fin l) (Fin m) α) : Fin m → α :=
  FinVec.map (fun a => dotProductᵣ v a) Aᵀ

/-- This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  ![b₁, b₂] ᵥ* !![a₁₁, a₁₂;
                       a₂₁, a₂₂] = ![b₁*a₁₁ + b₂*a₂₁, b₁*a₁₂ + b₂*a₂₂] :=
(vecMulᵣ_eq _ _).symm
```
-/
@[simp]
theorem vecMulᵣ_eq [NonUnitalNonAssocSemiring α] (v : Fin l → α) (A : Matrix (Fin l) (Fin m) α) :
    vecMulᵣ v A = v ᵥ* A := by
  simp [vecMulᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    ![b₁, b₂] ᵥ* !![a₁₁, a₁₂; a₂₁, a₂₂] = ![b₁ * a₁₁ + b₂ * a₂₁, b₁ * a₁₂ + b₂ * a₂₂] :=
  (vecMulᵣ_eq _ _).symm

/-- Expand `A` to `!![A 0 0, ...; ..., A m n]` -/
def etaExpand {m n} (A : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  Matrix.ofArray (List.ofFn (fun k : Fin (m * n) => A k.divNat k.modNat)).toArray
    (by simp only [List.toArray_ofFn, Array.size_ofFn])

/-- This can be used to prove
```lean
example (A : Matrix (Fin 2) (Fin 2) α) :
  A = !![A 0 0, A 0 1;
         A 1 0, A 1 1] :=
(etaExpand_eq _).symm
```
-/
theorem etaExpand_eq {m n} (A : Matrix (Fin m) (Fin n) α) : etaExpand A = A := by
  exact Matrix.ofArray_toArray_ofFn A

example (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  (etaExpand_eq _).symm

end Matrix
