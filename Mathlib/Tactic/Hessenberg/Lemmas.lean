/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity
public import Mathlib.Tactic.Hessenberg.CharPoly
public import Mathlib.Tactic.Hessenberg.Coeffs

/-!
# The Hessenberg recurrence on similarity certificates

The characteristic polynomial of a matrix from a `Hessenberg.Similarity` certificate, by the
recurrence on the Hessenberg form that the certificate carries.
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}

theorem charpoly_eq_hessCharPoly (cert : Hessenberg.Similarity A) :
    A.charpoly = hessCharPoly n cert.Harr :=
  cert.charpoly_eq.trans (charpoly_ofArray_eq_hessCharPoly cert.Harr cert.size_eq cert.hessenberg)

theorem charpoly_eq_ofCoeffs (cert : Hessenberg.Similarity A) :
    A.charpoly = ofCoeffs (coeffHessCharPoly n cert.Harr) :=
  (charpoly_eq_hessCharPoly cert).trans (hessCharPoly_eq_ofCoeffs n cert.Harr)

theorem charpoly_eq_ofCoeffs_of_eq (cert : Hessenberg.Similarity A) {cs : List R}
    (h : coeffHessCharPoly n cert.Harr = cs) : A.charpoly = ofCoeffs cs :=
  (charpoly_eq_ofCoeffs cert).trans (congrArg _ h)

end Mathlib.Tactic.Hessenberg

end
