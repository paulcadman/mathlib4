/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation.Operations
public import Mathlib.LinearAlgebra.Matrix.VecNotation -- shake: keep

/-!
# Matrix notation

This is the compatibility entry point for finite matrix notation. It provides the array-backed
`!![...]` notation and operation simp lemmas, the legacy vector-notation simp API, and lemmas for
small matrix literals.
-/

@[expose] public section

namespace Matrix

universe u

variable {α : Type u}

section Diagonal

variable [Zero α]

theorem diagonal_fin_one (d : Fin 1 → α) : diagonal d = !![d 0] := by
  simp [← Matrix.ext_iff]

theorem diagonal_vec1 (a : α) : diagonal ![a] = !![a] :=
  diagonal_fin_one ![a]

theorem diagonal_fin_two (d : Fin 2 → α) : diagonal d = !![d 0, 0; 0, d 1] := by
  simp [← Matrix.ext_iff]

theorem diagonal_vec2 (a b : α) : diagonal ![a, b] = !![a, 0; 0, b] :=
  diagonal_fin_two ![a, b]

theorem diagonal_fin_three (d : Fin 3 → α) :
    diagonal d = !![d 0, 0, 0; 0, d 1, 0; 0, 0, d 2] := by
  simp [← Matrix.ext_iff, Fin.forall_fin_succ]

theorem diagonal_vec3 (a b c : α) :
    diagonal ![a, b, c] = !![a, 0, 0; 0, b, 0; 0, 0, c] :=
  diagonal_fin_three ![a, b, c]

end Diagonal

section SmallMatrices

section One

variable [Zero α] [One α]

theorem one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem one_fin_three : (1 : Matrix (Fin 3) (Fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end One

section AddMonoidWithOne

variable [AddMonoidWithOne α]

theorem natCast_fin_two (n : ℕ) : (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem natCast_fin_three (n : ℕ) :
    (n : Matrix (Fin 3) (Fin 3) α) = !![↑n, 0, 0; 0, ↑n, 0; 0, 0, ↑n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem ofNat_fin_two (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 2) (Fin 2) α) = !![ofNat(n), 0; 0, ofNat(n)] :=
  natCast_fin_two _

theorem ofNat_fin_three (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 3) (Fin 3) α) =
      !![ofNat(n), 0, 0; 0, ofNat(n), 0; 0, 0, ofNat(n)] :=
  natCast_fin_three _

end AddMonoidWithOne

theorem eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eta_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    A = !![A 0 0, A 0 1, A 0 2;
           A 1 0, A 1 1, A 1 2;
           A 2 0, A 2 1, A 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂;
       a₂₁, a₂₂] * !![b₁₁, b₁₂;
                      b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                     a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

set_option linter.style.whitespace false in -- Preserve the formatting of the matrices.
theorem mul_fin_three [AddCommMonoid α] [Mul α]
    (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
    !![a₁₁, a₁₂, a₁₃;
       a₂₁, a₂₂, a₂₃;
       a₃₁, a₃₂, a₃₃] * !![b₁₁, b₁₂, b₁₃;
                           b₂₁, b₂₂, b₂₃;
                           b₃₁, b₃₂, b₃₃] =
    !![a₁₁*b₁₁ + a₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃;
       a₂₁*b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃₃;
       a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ + a₃₃*b₃₃] := by
  ext i j
  fin_cases i <;> fin_cases j
    <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, ← add_assoc]

end SmallMatrices

end Matrix
