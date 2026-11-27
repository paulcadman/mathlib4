module

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

macro "eval_posDef" : tactic => `(tactic| fail "eval_posDef is not implemented")

example : (!![] : Matrix (Fin 0) (Fin 0) ℚ).PosDef := by
  eval_posDef

example : (!![1] : Matrix (Fin 1) (Fin 1) ℤ).PosDef := by
  eval_posDef

example : (!![2, -1, 0; -1, 2, -1; 0, -1, 2] : Matrix (Fin 3) (Fin 3) ℤ).PosDef := by
  eval_posDef

example : (!![2, -1, 0; -1, 2, -1; 0, -1, 2] : Matrix (Fin 3) (Fin 3) ℚ).PosDef := by
  eval_posDef

example : (!![2, -1, 0; -1, 2, -1; 0, -1, 2] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  eval_posDef

example : (!![  1, 1/2, 1/3, 1/4, 1/5;
              1/2, 1/3, 1/4, 1/5, 1/6;
              1/3, 1/4, 1/5, 1/6, 1/7;
              1/4, 1/5, 1/6, 1/7, 1/8;
              1/5, 1/6, 1/7, 1/8, 1/9] : Matrix (Fin 5) (Fin 5) ℝ).PosDef := by
  eval_posDef

example : (!![2 ^ 2, 3 - 2; 1, 2 * 3] : Matrix (Fin 2) (Fin 2) ℤ).PosDef := by
  eval_posDef

example : (!![ 2,  0, -1,  0,  0,  0,  0,  0;
               0,  2,  0, -1,  0,  0,  0,  0;
              -1,  0,  2, -1,  0,  0,  0,  0;
               0, -1, -1,  2, -1,  0,  0,  0;
               0,  0,  0, -1,  2, -1,  0,  0;
               0,  0,  0,  0, -1,  2, -1,  0;
               0,  0,  0,  0,  0, -1,  2, -1;
               0,  0,  0,  0,  0,  0, -1,  2] : Matrix (Fin 8) (Fin 8) ℤ).PosDef := by
  eval_posDef

section Complex

open ComplexOrder Complex

example : (!![2, -1, 0; -1, 2, -1; 0, -1, 2] : Matrix (Fin 3) (Fin 3) ℂ).PosDef := by
  eval_posDef

example : (!![2, I; -I, 2] : Matrix (Fin 2) (Fin 2) ℂ).PosDef := by
  eval_posDef

end Complex
