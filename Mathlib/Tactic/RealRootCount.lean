/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Tactic.NormNum.Core
public meta import Mathlib.Tactic.Polynomial.Basic
public meta import Mathlib.Tactic.RealRootCount.Core
public meta import Mathlib.Tactic.RealRootCount.Reflection
public meta import Mathlib.Util.Qq
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.RealRootCount.Reflection

/-!
# `real_root_count`

The `norm_root_count` simproc rewrites `Fintype.card (f.rootSet ℝ)` to the number of distinct real
roots of an explicit polynomial `f` over `ℤ`, `ℚ` or `ℝ` with rational coefficients, and the
`real_root_count` tactic, `simp only [norm_root_count]`, proves `Fintype.card (f.rootSet ℝ) = n`.
-/

meta section

namespace Mathlib.Tactic.RealRootCount

open Lean Meta Elab Term Qq CoeffList

deriving instance ToExpr for SturmStep
deriving instance ToExpr for SturmData

/-- The value of a closed rational numeral `e`, by `norm_num`. -/
def ratOf (e : Expr) : MetaM ℚ := do
  let ⟨u, α, e⟩ ← inferTypeQ' e
  try
    if let some q := (← Mathlib.Meta.NormNum.derive (u := u) (α := α) e).toRat then return q
  catch _ => pure ()
  throwError "real_root_count: cannot read{indentExpr e}\nin a polynomial with rational \
    coefficients"

/-- The coefficients, constant term first, of a polynomial expression built from `X`, `C c` and
numerals by `+`, `-`, `*` and `^`, where each `c` and each exponent is a closed numeral. -/
partial def coeffsOf (e : Expr) : MetaM (List ℚ) := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ p q => return add (← coeffsOf p) (← coeffsOf q)
  | HSub.hSub _ _ _ _ p q => return add (← coeffsOf p) (neg (← coeffsOf q))
  | Neg.neg _ _ p => return neg (← coeffsOf p)
  | HMul.hMul _ _ _ _ p q => return mul (← coeffsOf p) (← coeffsOf q)
  | HPow.hPow _ _ _ _ p k =>
    return (List.replicate (← ratOf k).num.toNat (← coeffsOf p)).foldl mul [1]
  | Polynomial.X _ _ => return [0, 1]
  | DFunLike.coe _ _ _ _ f c => return [← ratOf (if f.isAppOf ``Polynomial.C then c else e)]
  | _ => return [← ratOf e]

/-! ### Building the proof -/

/-- Simp lemmas turning `f.map (algebraMap R ℝ)` into a polynomial expression over `ℝ`.
`Nat.cast_ofNat` turns a cast of a numeral, such as `((4 : ℕ) : ℚ)`, into a numeral, which the
normaliser leaves alone otherwise. -/
def mapLemmas : List Name :=
  [``Polynomial.map_add, ``Polynomial.map_sub, ``Polynomial.map_neg, ``Polynomial.map_mul,
    ``Polynomial.map_pow, ``Polynomial.map_X, ``Polynomial.map_C, ``Polynomial.map_ofNat,
    ``Polynomial.map_one, ``Polynomial.map_zero, ``Polynomial.map_natCast,
    ``Polynomial.map_intCast, ``Algebra.algebraMap_self, ``RingHom.id_apply, ``Polynomial.map_id,
    ``eq_ratCast, ``eq_intCast, ``Nat.cast_ofNat]

/-- `simp only` with the given lemmas. -/
def simpOnly (lemmas : List Name) (e : Expr) : MetaM Simp.Result := do
  let thms ← lemmas.foldlM (·.addConst ·) {}
  let ctx ← Simp.mkContext {} (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main e ctx (methods := Simp.mkDefaultMethodsCore {})).1

/-- The normal form of a real polynomial expression by the `polynomial` normaliser. The normaliser
rejects an atom such as `X`, so an atom `e` is normalised as `e + 0`. -/
def normalise (e : Q(Polynomial ℝ)) : AtomM Simp.Result := do
  try Polynomial.evalExprPoly e
  catch _ =>
    let r ← Polynomial.evalExprPoly q($e + 0)
    Simp.Result.mkEqTrans { expr := q($e + 0), proof? := q((add_zero $e).symm) } r

/-- A proof of `e = toReal p`, by rewriting `toReal p` to `C c₀ + X * (C c₁ + X * ⋯)`
(`toReal_cons`) and putting both sides in normal form with the `polynomial` normaliser. -/
def proveEqToReal (e : Q(Polynomial ℝ)) (p : Q(List ℚ)) : MetaM Expr := do
  let rp ← simpOnly mapLemmas e
  AtomM.run .reducible do
    let rp ← rp.mkEqTrans (← normalise rp.expr)
    let rq ← simpOnly [``toReal_cons, ``toReal_nil] q(toReal $p)
    let rq ← rq.mkEqTrans (← normalise rq.expr)
    unless ← isDefEq rp.expr rq.expr do
      throwError "real_root_count: could not match the polynomial with its coefficients"
    mkEqTrans (← rp.getProof) (← mkEqSymm (← rq.getProof))

/-- For `e = Fintype.card (f.rootSet ℝ)`, the number `n` of distinct real roots of `f` and a proof
of `e = n`. -/
def proveCardRootSet (e : Expr) : MetaM (Q(ℕ) × Expr) := do
  let err := m!"real_root_count: expected `Fintype.card (f.rootSet ℝ)`"
  let_expr Fintype.card α _ := e | throwError err
  let_expr Set.Elem _ s := α | throwError err
  let_expr Polynomial.rootSet R iR f S _ _ iA := s | throwError err
  unless ← isDefEq S q(ℝ) do throwError err
  let ⟨_, R⟩ ← getLevelQ' R
  have _iR : Q(CommRing $R) := iR
  have _iA : Q(Algebra $R ℝ) := iA
  have f : Q(Polynomial $R) := f
  -- the coefficients `p` of `f`, without trailing zeros
  let p := ((← coeffsOf f).reverse.dropWhile (· == 0)).reverse
  if p.isEmpty then throwError "real_root_count: expected a nonzero polynomial"
  let d := SturmData.fromCoeffList p
  let some n := realRootCount? p d
    | throwError "real_root_count: the computed Sturm sequence does not check"
  have pE : Q(List ℚ) := toExpr p
  have dE : Q(SturmData) := toExpr d
  have nE : Q(ℕ) := mkNatLit n
  have hf : Q(Polynomial.map (algebraMap $R ℝ) $f = toReal $pE) :=
    ← proveEqToReal q(Polynomial.map (algebraMap $R ℝ) $f) pE
  -- the kernel checks `h` by evaluating `realRootCount?`
  have h : Q(realRootCount? $pE $dE = some $nE) := (q(Eq.refl (some $nE)) : Expr)
  return (nE, q(card_rootSet_of_realRootCount? $hf $h))

end Mathlib.Tactic.RealRootCount

end

public meta section

open Lean Meta Mathlib.Tactic.RealRootCount

initialize registerTraceClass `Tactic.realRootCount

/-- `norm_root_count` rewrites `Fintype.card (f.rootSet ℝ)` to the number of distinct real roots of
an explicit polynomial `f` with rational coefficients, by computing its Sturm sequence and having
the kernel check it. Terms that it cannot evaluate are skipped; the reason can be viewed by using
`set_option trace.Tactic.realRootCount true`. -/
simproc_decl norm_root_count (Fintype.card _) := fun e => do
  try
    let (n, pf) ← proveCardRootSet e
    return .done { expr := n, proof? := some pf }
  catch ex =>
    trace[Tactic.realRootCount] "{ex.toMessageData}"
    return .continue

/-- `real_root_count` proves `Fintype.card (f.rootSet ℝ) = n` for an explicit polynomial `f`
with rational coefficients: it is `simp only [norm_root_count]`. The count is of distinct real
roots. -/
macro (name := realRootCount) "real_root_count" : tactic => `(tactic| simp only [norm_root_count])
