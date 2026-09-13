module

meta import Mathlib.LinearAlgebra.Matrix.Hessenberg.Coeffs
import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity
import Mathlib.LinearAlgebra.Matrix.Notation

open Polynomial

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 0;
          1, 3, 0;
          0, 3, 1]
    M.IsUpperHessenberg := by decide

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 0;
          0, 3, 0;
          1, 0, 1]
    ¬ M.IsUpperHessenberg := by decide

def certId :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 3;
          4, 5, 6;
          0, 7, 8]
    Hessenberg.Similarity M where
      σ := 1
      L := 1
      Harr := #[1, 2, 3, 4, 5, 6, 0, 7, 8]
      size_eq := rfl
      similarity := by decide +kernel
      L_lowerTriangular := by decide
      L_diag_ne_zero := by decide
      hessenberg := by decide

def certShear :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 3;
          1, 1, 1;
          2, 0, 1]
    Hessenberg.Similarity M where
      σ := 1
      L := !![1, 0, 0; 0, 1, 0; 0, 2, 1]
      Harr := #[1, 8, 3, 1, 3, 1, 0, -4, -1]
      size_eq := rfl
      similarity := by decide +kernel
      L_lowerTriangular := by decide
      L_diag_ne_zero := by decide
      hessenberg := by decide

example :
    let M : Matrix (Fin 3) (Fin 3) ℚ :=
      !![ 1, 2, 3;
          1, 1, 1;
          2, 0, 1]
    let Harr := #[1, 8, 3, 1, 3, 1, 0, -4, -1]
    let H : Matrix (Fin 3) (Fin 3) ℚ := Matrix.ofArray Harr rfl
    M.charpoly = H.charpoly := certShear.charpoly_eq

#guard Matrix.coeffHessCharPoly 0 (#[] : Array ℚ) = [1]
example : Matrix.coeffHessCharPoly 0 (#[] : Array ℚ) = [1] := by decide +kernel

#guard Matrix.coeffHessCharPoly 1 (#[5] : Array ℚ) = [-5, 1]
example : Matrix.coeffHessCharPoly 1 (#[5] : Array ℚ) = [-5, 1] := by decide +kernel

#guard Matrix.coeffHessCharPoly 2 (#[1, 2, 3, 4] : Array ℚ) = [-2, -5, 1]
example : Matrix.coeffHessCharPoly 2 (#[1, 2, 3, 4] : Array ℚ) = [-2, -5, 1] := by decide +kernel

#guard Matrix.coeffHessCharPoly 2 (#[1/2, 1, 1, 2] : Array ℚ) = [0, -5/2, 1]
example : Matrix.coeffHessCharPoly 2 (#[1/2, 1, 1, 2] : Array ℚ) = [0, -5/2, 1] := by
  decide +kernel
