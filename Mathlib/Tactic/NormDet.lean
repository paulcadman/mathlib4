/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

import Mathlib.Data.Matrix.Reflection
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Determinant.Bird.Cert

/-!
# `norm_det` tactic

The `norm_det` tactic normalizes determinants of matrices written using `!![...]` notation.
-/

variable {R : Type*}

theorem det_eq_birdDet_of_eq_ofArray {n : ℕ} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) (A : Array R) (hA : A.size = n * n)
    (h : Matrix.ofArray A hA = M) : Matrix.det M = BirdDet.birdDet n A := by
  rw [← h]
  exact BirdDet.det_eq_birdDet A hA

/-- Reconstruct a matrix from its entries in row-major order returns the original matrix. -/
theorem ofArray_toArray_ofFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    Matrix.ofArray (List.ofFn (fun k : Fin (m * n) => A k.divNat k.modNat)).toArray
      (by simp only [List.toArray_ofFn, Array.size_ofFn]) = A := by
  ext i j
  simp only [List.toArray_ofFn, Matrix.ofArray_apply, Fin.getElem_fin, Array.getElem_ofFn]
  rw [Fin.divNat_mkDivMod, Fin.modNat_mkDivMod]

public meta section

open Lean Meta Elab Tactic Simp Qq
open Mathlib.Tactic.Determinant

/-- Normalize the internal `BirdDet.birdDet` expression used by
`normalizeDetOfMatrixLiteral?`. -/
private def normalizeBirdDet (e : Expr) : MetaM Simp.Result := do
  let ⟨rα, ctx⟩ ← reifyBirdDet e
  let detNorm ← certBirdDet (rα := rα) |>.run' {} |>.run ctx |>.run .reducible
  Mathlib.Tactic.RingNF.cleanup {} {expr := detNorm.norm, proof? := some detNorm.proof}

/-- Return the dimension and row-major entries of a square `!![...]` matrix literal. -/
private def matchSquareMatrixLiteral? {u : Level} (α : Q(Type u)) (matrixExpr : Expr) :
    MetaM (Option (Nat × Array Q($α))) := do
  let .app matrixFn rows := matrixExpr | return none
  let .app _ matrixOf := matrixFn | return none
  let_expr Matrix.of rowType colType elementType := matrixOf | return none
  let_expr Fin rowDimensionExpr := rowType | return none
  let_expr Fin colDimensionExpr := colType | return none
  let some rowDimensionExpr ← checkTypeQ rowDimensionExpr q(ℕ)
    | return none
  let some colDimensionExpr ← checkTypeQ colDimensionExpr q(ℕ)
    | return none
  unless ← isDefEq rowDimensionExpr colDimensionExpr do return none
  unless ← isDefEq elementType α do return none
  let some dimension ← getNatValue? rowDimensionExpr | return none
  let (matrixRows, _, _) ← Matrix.matchVecConsPrefix rowDimensionExpr rows
  unless matrixRows.length == dimension do return none
  let mut entries : Array Q($α) := #[]
  for row in matrixRows do
    let (rowEntries, _, _) ← Matrix.matchVecConsPrefix colDimensionExpr row
    unless rowEntries.length == dimension do return none
    for entry in rowEntries do
      let some entry ← checkTypeQ entry α
        | throwError "expected matrix entry to have type {α}"
      entries := entries.push entry
  return some (dimension, entries)

/-- Rewrite a matrix literal through `BirdDet.birdDet` and normalize the resulting expression. -/
private def normalizeMatrixLiteral {u : Level} {α : Q(Type u)} (lhs : Q($α))
    (detRingInst : Q(CommRing $α)) (matrixExpr : Expr) (dimension : Nat)
    (entries : Array Q($α)) : MetaM Simp.Result := do
  have dimensionLit : Q(ℕ) := mkNatLit dimension
  let arrayExpr ← mkArrayLit α entries.toList
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected flat array to have type {q(Array $α)}"
  let expectedSizeType := q(Array.size $arrayExpr = $dimensionLit * $dimensionLit)
  let sizeProofExpr ← mkDecideProof expectedSizeType
  let some sizeProof ← checkTypeQ sizeProofExpr expectedSizeType
    | throwError "expected size proof to have type {expectedSizeType}"
  let some matrix ←
      checkTypeQ matrixExpr q(Matrix (Fin $dimensionLit) (Fin $dimensionLit) $α)
    | throwError "expected a square matrix literal of dimension {dimension}"
  let reconstructionExpr :=
    q(@ofArray_toArray_ofFn $α $dimensionLit $dimensionLit $matrix)
  let birdExpr := q(@BirdDet.birdDet $α $detRingInst $dimensionLit $arrayExpr)
  let bridge ← mkAppM ``det_eq_birdDet_of_eq_ofArray
    #[matrix, arrayExpr, sizeProof, reconstructionExpr]
  unless ← isDefEq (← inferType bridge) q($lhs = $birdExpr) do
    throwError "failed to reconstruct matrix literal as a flat array"
  let birdNorm ← normalizeBirdDet birdExpr
  let bridgeResult : Simp.Result := {
    expr := birdExpr
    proof? := some bridge
  }
  bridgeResult.mkEqTrans birdNorm

/-- Normalize a determinant whose matrix is represented by `!![...]` notation. -/
private def normalizeDetOfMatrixLiteral? (e : Expr) : MetaM (Option Simp.Result) := do
  let e ← instantiateMVars e
  let ⟨_, α, e⟩ ← inferTypeQ' e
  let_expr Matrix.det _ _ _ _ detRingInst matrixExpr := e
    | return none
  let some detRingInst ← checkTypeQ detRingInst q(CommRing $α)
    | throwError "expected determinant ring instance to have type {q(CommRing $α)}"
  let some (dimension, entries) ← matchSquareMatrixLiteral? α matrixExpr
    | return none
  let some lhs ← checkTypeQ e α
    | throwError "expected determinant expression to have type {α}"
  return some (← normalizeMatrixLiteral lhs detRingInst matrixExpr dimension entries)

/-- Normalize determinants of matrices written using `!![...]` through `BirdDet.birdDet`. -/
simproc_decl norm_det (Matrix.det _) := fun e => do
  match ← normalizeDetOfMatrixLiteral? e with
  | some result => return .done result
  | none => return .continue

/-- Normalize determinants of `!![...]` matrix literals in the target. -/
macro (name := evalDet) "eval_det" : tactic => `(tactic| simp only [norm_det])

end
