/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Matrices and vector notation

This file includes `simp` lemmas for applying matrix operations to vectors and matrices built using
`![a, b] = vecCons a (vecCons b vecEmpty)`, defined in `Data.Fin.VecNotation`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, vector notation will only appear in the output of `simp` if it already appears in
the input.
-/

@[expose] public section

namespace Matrix

universe u uₘ uₙ uₒ

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

open Matrix

@[simp]
theorem cons_val' (v : n' → α) (B : Fin m → n' → α) (i j) :
    vecCons v B i j = vecCons (v j) (fun i => B i j) i := by refine Fin.cases ?_ ?_ i <;> simp

@[simp]
theorem head_val' (B : Fin m.succ → n' → α) (j : n') : (vecHead fun i => B i j) = vecHead B j :=
  rfl

@[simp]
theorem tail_val' (B : Fin m.succ → n' → α) (j : n') :
    (vecTail fun i => B i j) = fun i => vecTail B i j := rfl

section DotProduct

variable [AddCommMonoid α] [Mul α]

@[simp]
theorem dotProduct_of_isEmpty [Fintype n'] [IsEmpty n'] (v w : n' → α) : v ⬝ᵥ w = 0 :=
  Finset.sum_of_isEmpty _

@[simp]
theorem cons_dotProduct (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

@[simp]
theorem dotProduct_cons (v : Fin n.succ → α) (x : α) (w : Fin n → α) :
    v ⬝ᵥ vecCons x w = vecHead v * x + vecTail v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ, vecHead, vecTail]

theorem cons_dotProduct_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v ⬝ᵥ vecCons y w = x * y + v ⬝ᵥ w := by simp

end DotProduct

section ColRow

variable {ι : Type*}

@[simp]
theorem replicateCol_empty (v : Fin 0 → α) : replicateCol ι v = vecEmpty :=
  empty_eq _

@[simp]
theorem replicateCol_cons (x : α) (u : Fin m → α) :
    replicateCol ι (vecCons x u) = of (vecCons (fun _ => x) (replicateCol ι u)) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp

@[simp]
theorem replicateRow_empty : replicateRow ι (vecEmpty : Fin 0 → α) = of fun _ => vecEmpty := rfl

@[simp]
theorem replicateRow_cons (x : α) (u : Fin m → α) :
    replicateRow ι (vecCons x u) = of fun _ => vecCons x u :=
  rfl

end ColRow

section Transpose

@[simp]
theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] :=
  empty_eq _

@[simp]
theorem transpose_empty_cols (A : Matrix (Fin 0) m' α) : Aᵀ = of fun _ => ![] :=
  funext fun _ => empty_eq _

@[simp]
theorem cons_transpose (v : n' → α) (A : Matrix (Fin m) n' α) :
    (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i) := by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp

@[simp]
theorem head_transpose (A : Matrix m' (Fin n.succ) α) :
    vecHead (of.symm Aᵀ) = vecHead ∘ of.symm A :=
  rfl

@[simp]
theorem tail_transpose (A : Matrix m' (Fin n.succ) α) : vecTail (of.symm Aᵀ) = (vecTail ∘ A)ᵀ := by
  ext i j
  rfl

end Transpose

section Mul

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : Matrix n' o' α) : A * B = of ![] :=
  empty_eq _

@[simp]
theorem empty_mul_empty (A : Matrix m' (Fin 0) α) (B : Matrix (Fin 0) o' α) : A * B = 0 :=
  rfl

@[simp]
theorem mul_empty [Fintype n'] (A : Matrix m' n' α) (B : Matrix n' (Fin 0) α) :
    A * B = of fun _ => ![] :=
  funext fun _ => empty_eq _

theorem mul_val_succ [Fintype n'] (A : Matrix (Fin m.succ) n' α) (B : Matrix n' o' α) (i : Fin m)
    (j : o') : (A * B) i.succ j = (of (vecTail (of.symm A)) * B) i j :=
  rfl

@[simp]
theorem cons_mul [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (B : Matrix n' o' α) :
    of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm (of A * B))) := by
  ext i j
  refine Fin.cases ?_ ?_ i
  · rfl
  simp [mul_val_succ]

end Mul

section VecMul

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_vecMul (v : Fin 0 → α) (B : Matrix (Fin 0) o' α) : v ᵥ* B = 0 :=
  rfl

@[simp]
theorem vecMul_empty [Fintype n'] (v : n' → α) (B : Matrix n' (Fin 0) α) : v ᵥ* B = ![] :=
  empty_eq _

@[simp]
theorem cons_vecMul (x : α) (v : Fin n → α) (B : Fin n.succ → o' → α) :
    vecCons x v ᵥ* of B = x • vecHead B + v ᵥ* of (vecTail B) := by
  ext i
  simp [vecMul]

@[simp]
theorem vecMul_cons (v : Fin n.succ → α) (w : o' → α) (B : Fin n → o' → α) :
    v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B := by
  ext i
  simp [vecMul]

theorem cons_vecMul_cons (x : α) (v : Fin n → α) (w : o' → α) (B : Fin n → o' → α) :
    vecCons x v ᵥ* of (vecCons w B) = x • w + v ᵥ* of B := by simp

end VecMul

section MulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_mulVec [Fintype n'] (A : Matrix (Fin 0) n' α) (v : n' → α) : A *ᵥ v = ![] :=
  empty_eq _

@[simp]
theorem mulVec_empty (A : Matrix m' (Fin 0) α) (v : Fin 0 → α) : A *ᵥ v = 0 :=
  rfl

@[simp]
theorem cons_mulVec [Fintype n'] (v : n' → α) (A : Fin m → n' → α) (w : n' → α) :
    (of <| vecCons v A) *ᵥ w = vecCons (v ⬝ᵥ w) (of A *ᵥ w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [mulVec]

@[simp]
theorem mulVec_cons {α} [NonUnitalCommSemiring α] (A : m' → Fin n.succ → α) (x : α)
    (v : Fin n → α) : (of A) *ᵥ (vecCons x v) = x • vecHead ∘ A + (of (vecTail ∘ A)) *ᵥ v := by
  ext i
  simp [mulVec, mul_comm]

end MulVec

section VecMulVec

variable [NonUnitalNonAssocSemiring α]

@[simp]
theorem empty_vecMulVec (v : Fin 0 → α) (w : n' → α) : vecMulVec v w = ![] :=
  empty_eq _

@[simp]
theorem vecMulVec_empty (v : m' → α) (w : Fin 0 → α) : vecMulVec v w = of fun _ => ![] :=
  funext fun _ => empty_eq _

@[simp]
theorem cons_vecMulVec (x : α) (v : Fin m → α) (w : n' → α) :
    vecMulVec (vecCons x v) w = vecCons (x • w) (vecMulVec v w) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [vecMulVec]

@[simp]
theorem vecMulVec_cons (v : m' → α) (x : α) (w : Fin n → α) :
    vecMulVec v (vecCons x w) = of fun i => v i • vecCons x w := rfl

end VecMulVec

section SMul

variable [NonUnitalNonAssocSemiring α]

theorem smul_mat_empty {m' : Type*} (x : α) (A : Fin 0 → m' → α) : x • A = ![] :=
  empty_eq _

end SMul

section Submatrix

@[simp]
theorem submatrix_empty (A : Matrix m' n' α) (row : Fin 0 → m') (col : o' → n') :
    submatrix A row col = ![] :=
  empty_eq _

@[simp]
theorem submatrix_cons_row (A : Matrix m' n' α) (i : m') (row : Fin m → m') (col : o' → n') :
    submatrix A (vecCons i row) col = vecCons (fun j => A i (col j)) (submatrix A row col) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp [submatrix]

/-- Updating a row then removing it is the same as removing it. -/
@[simp]
theorem submatrix_updateRow_succAbove (A : Matrix (Fin m.succ) n' α) (v : n' → α) (f : o' → n')
    (i : Fin m.succ) : (A.updateRow i v).submatrix i.succAbove f = A.submatrix i.succAbove f :=
  ext fun r s => (congr_fun (updateRow_ne (Fin.succAbove_ne i r) : _ = A _) (f s) :)

/-- Updating a column then removing it is the same as removing it. -/
@[simp]
theorem submatrix_updateCol_succAbove (A : Matrix m' (Fin n.succ) α) (v : m' → α) (f : o' → m')
    (i : Fin n.succ) : (A.updateCol i v).submatrix f i.succAbove = A.submatrix f i.succAbove :=
  ext fun _r s => updateCol_ne (Fin.succAbove_ne i s)

end Submatrix

section SmallVectors

theorem vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) : ![a₀, a₁] = ![b₀, b₁] := by
  simp [h₀, h₁]

theorem vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    ![a₀, a₁, a₂] = ![b₀, b₁, b₂] := by
  simp [h₀, h₁, h₂]

theorem vec2_add [Add α] (a₀ a₁ b₀ b₁ : α) : ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] := by
  simp

theorem vec3_add [Add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
    ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] := by
  simp

theorem smul_vec2 {R : Type*} [SMul R α] (x : R) (a₀ a₁ : α) :
    x • ![a₀, a₁] = ![x • a₀, x • a₁] := by
  simp

theorem smul_vec3 {R : Type*} [SMul R α] (x : R) (a₀ a₁ a₂ : α) :
    x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] := by
  simp

variable [AddCommMonoid α] [Mul α]

theorem vec2_dotProduct' {a₀ a₁ b₀ b₁ : α} : ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ := by
  simp

@[simp]
theorem vec2_dotProduct (v w : Fin 2 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
  vec2_dotProduct'

theorem vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  simp [add_assoc]

-- This is not tagged `@[simp]` because it does not mesh well with simp lemmas for
-- dot and cross products in dimension 3.
theorem vec3_dotProduct (v w : Fin 3 → α) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
  vec3_dotProduct'

end SmallVectors

end Matrix

@[simp]
lemma injective_pair_iff_ne {α : Type*} {x y : α} :
    Function.Injective ![x, y] ↔ x ≠ y := by
  refine ⟨fun h ↦ ?_, fun h a b h' ↦ ?_⟩
  · simpa using h.ne Fin.zero_ne_one
  · fin_cases a <;> fin_cases b <;> aesop
