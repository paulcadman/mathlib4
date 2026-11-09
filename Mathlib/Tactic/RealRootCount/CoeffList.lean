/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Ring.Defs

/-!
# Arithmetic on polynomials represented as lists of coefficients.
-/

public section

namespace Mathlib.Tactic.RealRootCount.CoeffList

variable {R : Type*}

/-- The derivative of the polynomial that `p` represents. -/
@[expose] def derivative [Semiring R] (p : List R) : List R :=
  (List.range (p.length - 1)).map fun i => ((i + 1 : ℕ) : R) * p.getD (i + 1) 0

/-- The value at `x` of the polynomial that `p` represents. -/
@[expose] def eval [Semiring R] (x : R) (p : List R) : R := p.foldr (fun c acc => c + x * acc) 0

/-- The last entry of a coefficient list: the leading coefficient when it is nonzero. -/
@[expose] def lead [Zero R] (l : List R) : R := l.getLastD 0

/-- The sup norm of the polynomial that `p` represents. -/
@[expose] def supNorm (l : List ℤ) : ℕ := l.foldl (fun m c => max m c.natAbs) 0

/-- The `ℓ¹` norm of the polynomial that `p` represents. -/
@[expose] def l1Norm (l : List ℤ) : ℕ := l.foldl (fun m c => m + c.natAbs) 0

end Mathlib.Tactic.RealRootCount.CoeffList
