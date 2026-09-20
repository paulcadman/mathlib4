/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.Echelon.Cert
public import Mathlib.Tactic.Echelon.Rat
public import Mathlib.Tactic.Hessenberg.Reduce
public meta import Mathlib.Tactic.Echelon.Cert
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Mathlib.Tactic.Hessenberg.Reduce

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Hessenberg

/-- A matrix is `Matrix.ofArray` of the list of its entries in row-major order. The hypothesis is
checked by one structural evaluation of `List.ofFn` against the literal `l`, with no indexed
lookups. -/
theorem eq_ofArray_of_listOfFn_eq {R : Type*} {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    {l : List R} (h : (List.ofFn fun k : Fin (m * n) ↦ A k.divNat k.modNat) = l)
    (hl : l.toArray.size = m * n) : A = Matrix.ofArray l.toArray hl := by
  subst h
  ext i j
  rw [Matrix.ofArray_apply, Fin.getElem_fin, List.getElem_toArray, List.getElem_ofFn, Fin.eta,
    Fin.divNat_mkDivMod, Fin.modNat_mkDivMod]

/-- Build the numeral of a rational in `ℚ`: an integer numeral, or `p / q` with the sign
outside the division. -/
def mkRatExpr (r : Rat) : MetaM Q(ℚ) := do
  if r.den == 1 then Echelon.mkIntNumeral q(ℚ) r.num
  else
    have p : Q(ℚ) := ← mkNumeral q(ℚ) r.num.natAbs
    have q : Q(ℚ) := ← mkNumeral q(ℚ) r.den
    return if r.num < 0 then q(-($p / $q)) else q($p / $q)

/-- The result of producing a Hessenberg similarity of `A`. -/
structure SimilarityResult {n : ℕ} (A : Q(Matrix (Fin $n) (Fin $n) ℚ)) where
  /-- The elaborated `Hessenberg.Similarity` certificate term. -/
  cert : Q(Hessenberg.Similarity $A)
  /-- The reduction data underlying the certificate. -/
  red : Reduction

/-- Produce the`Hessenberg.Similarity` certificate and corresponding `Reduction` of the `n × n`
matrix literal `A` over `ℚ` with rows of entries `entries`. -/
def mkHessenbergSimilarity (n : ℕ) (A : Q(Matrix (Fin $n) (Fin $n) ℚ))
    (entries : Array (Array Expr)) : MetaM (SimilarityResult A) := do
  let vals ← entries.mapM (·.mapM (Echelon.evalRatEntry true))
  let some red := reduce n vals
    | throwError "the Hessenberg reduction failed{indentExpr A}"
  let valExprs ← vals.mapM (·.mapM mkRatExpr)
  let σ ← Echelon.mkPerm n red.swaps
  have Aσ : Q(Matrix (Fin $n) (Fin $n) ℚ) :=
    Echelon.mkMatrixLit q(ℚ) n n (red.perm.map fun i => red.perm.map fun j => (valExprs[i]!)[j]!)
  have L : Q(Matrix (Fin $n) (Fin $n) ℚ) :=
    Echelon.mkMatrixLit q(ℚ) n n (← red.L.mapM (·.mapM mkRatExpr))
  let hExprs ← red.H.mapM (·.mapM mkRatExpr)
  have H : Q(Matrix (Fin $n) (Fin $n) ℚ) := Echelon.mkMatrixLit q(ℚ) n n hExprs
  have lH : Q(List ℚ) := ← mkListLit q(ℚ) hExprs.flatten.toList
  have Harr : Q(Array ℚ) := q(List.toArray $lH)
  let hsize : Q(($Harr).size = $n * $n) ← mkDecideProofQ q(($Harr).size = $n * $n)
  let hperm ← mkDecideProofQ q(($A).submatrix $σ $σ = $Aσ)
  let hprod ← mkDecideProofQ q($Aσ * $L = $L * $H)
  have entriesH : Q(List ℚ) := q(List.ofFn fun k : Fin ($n * $n) => $H k.divNat k.modNat)
  let hofn ← mkExpectedTypeHint (← mkEqRefl entriesH) q($entriesH = $lH)
  have hH : Q($H = Matrix.ofArray $Harr $hsize) :=
    ← mkAppM ``eq_ofArray_of_listOfFn_eq #[H, hofn, hsize]
  have hAσ : Q((($A).submatrix $σ $σ) * $L = $L * $H) := q($hperm ▸ $hprod)
  have hsim : Q((($A).submatrix $σ $σ) * $L = $L * Matrix.ofArray $Harr $hsize) :=
    q(($hAσ).trans (congrArg (HMul.hMul $L) $hH))
  let hlower ← mkDecideProofQ q(($L).IsLowerTriangular)
  let hdiag ← mkDecideProofQ q(∀ i, ($L).diag i ≠ 0)
  let hhess ← mkDecideProofQ q(($H).IsUpperHessenberg)
  have cert : Q(Hessenberg.Similarity $A) :=
    q(⟨$L, $σ, $Harr, $hsize, $hsim, $hlower, $hdiag, $hH ▸ $hhess⟩)
  return { cert, red }

end Mathlib.Tactic.Hessenberg
