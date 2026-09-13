/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Basic
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Correctness of the Hessenberg characteristic polynomial recurrence
-/

namespace Matrix

open Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

public theorem charpoly_eq_hessCharPoly (Harr : Array R) (h : Harr.size = n * n)
    (hH : IsUpperHessenberg (Matrix.ofArray Harr h)) :
    (Matrix.ofArray Harr h).charpoly = hessCharPoly n Harr := by
  sorry

end Matrix
