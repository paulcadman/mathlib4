/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Upper Hessenberg matrices

## Main definitions

- `Matrix.IsUpperHessenberg`

-/

public section

namespace Matrix

-- TODO: Upstream this to Data.Fin.SuccPredOder?
theorem fin_orderSucc_lt_iff : ∀ {n : ℕ} {i j : Fin n}, Order.succ j < i ↔ j.val + 1 <  i.val
  | n + 1, i, j => by
    induction j using Fin.lastCases with
    | last => rw [Fin.orderSucc_last]; grind
    | cast j' => rw [@Fin.orderSucc_castSucc]; grind

variable {R m : Type*} [Zero R] [Preorder m] [SuccOrder m]

@[expose] def IsUpperHessenberg (M : Matrix m m R) : Prop :=
  ∀ ⦃i j⦄, Order.succ j < i → M i j = 0

instance decidableIsUpperHessenberg [DecidableEq R] [Fintype m] [DecidableLT m]
    (M : Matrix m m R) : Decidable M.IsUpperHessenberg :=
  decidable_of_iff (∀ ij : m × m, Order.succ ij.2 < ij.1 → M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

theorem IsUpperTriangular.isUpperHessenberg {M : Matrix m m R} (h : M.IsUpperTriangular) :
    M.IsUpperHessenberg :=
  fun _ j hij => h ((Order.le_succ j).trans_lt hij)

theorem isUpperHessenberg_fin_iff {n : ℕ} {M : Matrix (Fin n) (Fin n) R} :
    M.IsUpperHessenberg ↔ ∀ i j : Fin n, (j : ℕ) + 1 < i → M i j = 0 := by
  simp only [IsUpperHessenberg, fin_orderSucc_lt_iff]

end Matrix

end
