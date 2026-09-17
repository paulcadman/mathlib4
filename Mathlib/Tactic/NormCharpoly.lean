/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.Echelon.Parsing
public import Mathlib.Tactic.Hessenberg.Lemmas
public import Mathlib.Tactic.Hessenberg.Similarity
public import Mathlib.Tactic.Ring.Basic
public meta import Mathlib.Tactic.Echelon.Parsing
public meta import Mathlib.Tactic.Hessenberg.Coeffs
public meta import Mathlib.Tactic.Hessenberg.Similarity
public meta import Mathlib.Tactic.Ring.Basic

/-!
# `eval_charpoly`

This module defines the `norm_charpoly` simproc and `eval_charpoly` tactic for normalizing
characteristic polynomails of matrix literals over `ℚ` through a `Hessenberg.Similarity` certificate
checked by the kernel.
-/

public meta section

open Lean Meta Elab Qq

initialize registerTraceClass `Tactic.evalCharpoly

namespace Mathlib.Tactic.Hessenberg

def mkDisplay (cs : List Rat) : MetaM Q(Polynomial ℚ) := do
  let pow (k : ℕ) : Q(Polynomial ℚ) :=
    if k = 1 then q(Polynomial.X) else q(Polynomial.X ^ $k)
  let coeff (c : Rat) : MetaM Q(Polynomial ℚ) := do
    if c.den == 1 then
      have c : Q(Polynomial ℚ) := ← mkNumeral q(Polynomial ℚ) c.num.natAbs
      return c
    else
      let c ← mkRatExpr (if c < 0 then -c else c)
      return q(Polynomial.C $c)
  let n := cs.length - 1
  if n = 0 then return q(1)
  let mut acc := pow n
  for k in (List.range n).reverse do
    let c := cs.getD k 0
    if c == 0 then continue
    let t ←
      if k == 0 then coeff c
      else if c.num.natAbs == 1 && c.den == 1 then pure (pow k)
      else pure q($(← coeff c) * $(pow k))
    acc := if c > 0 then q($acc + $t) else q($acc - $t)
  return acc

def normalizeCharpoly (n : ℕ) (A : Q(Matrix (Fin $n) (Fin $n) ℚ))
    (entries : Array (Array Expr)) : MetaM Simp.Result := do
  let res ← mkHessenbergSimilarity n A entries
  have cert := res.cert
  let cs := coeffHessCharPoly n res.red.H.flatten
  have csE : Q(List ℚ) := ← mkListLit q(ℚ) (← cs.mapM mkRatExpr)
  let hcs ← mkDecideProofQ q(coeffHessCharPoly $n ($cert).Harr = $csE)
  have pf : Q(Matrix.charpoly $A = Polynomial.ofCoeffs $csE) :=
    q(charpoly_eq_ofCoeffs_of_eq $cert $hcs)
  let thms ← [``Polynomial.ofCoeffs_cons, ``Polynomial.ofCoeffs_nil, ``map_neg, ``map_ofNat,
    ``map_one, ``map_zero].foldlM (·.addConst ·) ({} : SimpTheorems)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (fold, _) ← Simp.main q(Polynomial.ofCoeffs $csE) ctx
    (methods := Simp.mkDefaultMethodsCore {})
  let display ← mkDisplay cs
  let g ← mkFreshExprMVar (← mkEq fold.expr display)
  AtomM.run .reducible (Ring.proveEq g.mvarId!)
  let r ← Simp.Result.mkEqTrans { expr := q(Polynomial.ofCoeffs $csE), proof? := pf } fold
  r.mkEqTrans { expr := display, proof? := g }

def normCharpolyCore : Simp.Simproc := fun e => do
  let_expr Matrix.charpoly R _ _ _ _ A := e | return .continue
  let A ← instantiateMVars A
  let some (n, _, _, entries) ← Echelon.matchMatrixLit? A
    | trace[Tactic.evalCharpoly] "{A} is not a closed matrix literal"
      return .continue
  if ← isDefEq R q(ℚ) then
    return .done (← normalizeCharpoly n A entries)
  trace[Tactic.evalCharpoly] "expected the element type to be ℚ"
  return .continue

end Mathlib.Tactic.Hessenberg

/-- The `norm_charpoly` simproc evaluates the characteristic polynomial of matrix literals over
`ℚ` or `ℤ`. Terms that it cannot evaluate are skipped. -/
simproc_decl norm_charpoly (Matrix.charpoly _) := fun e => do
  try Mathlib.Tactic.Hessenberg.normCharpolyCore e
  catch _ => return .continue

/--
`eval_charpoly` evaluates the characteristic polynomial of matrix literals over `ℚ`.

```lean
example : Matrix.charpoly (R := ℚ) !![1, 2; 3, 4] = X ^ 2 - 5 * X - 2 := by
  eval_charpoly
```
-/
elab (name := evalCharpoly) "eval_charpoly" : tactic => do
  try
    Tactic.evalTactic (← `(tactic| simp only [norm_charpoly]))
  catch _ =>
    throwError "`eval_charpoly` made no progress.\n\
      Additional information may be available using `set_option trace.Tactic.evalCharpoly true`."
  Tactic.evalTactic (← `(tactic| try ring1))

