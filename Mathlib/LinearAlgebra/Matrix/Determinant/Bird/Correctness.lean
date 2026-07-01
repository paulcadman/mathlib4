module

public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Order.Interval.Finset.Fin

namespace BirdDet

open scoped BigOperators

variable
  {R : Type*}
  [CommRing R]

abbrev Word (n m : ℕ) := List.Vector (Fin n) m

/-- Empty word. -/
def vnil {n : ℕ} : Word n 0 :=
  List.Vector.nil

/-- Prepend one index to a word. This is Bird's word `iα`. -/
def vcons {n p : ℕ} (a : Fin n) (w : Word n p) : Word n (p + 1) :=
  List.Vector.ofFn (Fin.cases a fun q => w.get q)

/-- The determinant of the submatrix of A formed by taking rows `rows` and
columns from `cols` -/
def wordDet {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) R)
    (rows cols : Word n m) : R :=
  Matrix.det fun i j => A (rows.get i) (cols.get j)

/-- `TailWords i p` is the set of subsequences of `[i+1, ..., n]` of length `p` -/
def TailWords {n : ℕ} (i : Fin n) (p : ℕ) :
    Finset (Word n p) :=
  Finset.univ.filter fun α =>
    StrictMono (fun t : Fin p => α.get t) ∧ ∀ t : Fin p, i < α.get t

theorem paper_eq1 {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (p : ℕ) (i j : Fin n) :
    Spec.iterMatrix A p i j =
      (-1 : R) ^ p * (∑ α ∈ TailWords i p, wordDet A (vcons i α) (vcons j α)) := by
  sorry

public theorem birdDetSpec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  sorry

end BirdDet
