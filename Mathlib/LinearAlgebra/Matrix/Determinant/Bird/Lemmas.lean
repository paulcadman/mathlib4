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

/-!
This file contains the theorem that Bird's algorithm computes Matrix.det

## Main theorems

- `birdDetSpec_eq_det` - Proves that BirdDet.Spec.birdDet computes Matrix.det
- `det_eq_birdDet` - Proves that BirdDet.Spec.birdDet computes BirdDet.birdDet
- `det_eq_birdDet` - Proves that BirdDet.birdDet computes Matrix.det

-/

@[expose] public section

namespace BirdDet

variable {R : Type*} [CommRing R]

theorem birdDetSpec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  sorry

theorem birdDet_eq_birdDetSpec {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (Matrix.ofArray (m := n) (n := n) A hA) := by
  sorry

theorem det_eq_birdDet {n : ℕ} (A : Array R) (hA : A.size = n * n) :
    Matrix.det (Matrix.ofArray (m := n) (n := n) A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec A hA]
  exact (birdDetSpec_eq_det (Matrix.ofArray (m := n) (n := n) A hA))

end BirdDet

end
