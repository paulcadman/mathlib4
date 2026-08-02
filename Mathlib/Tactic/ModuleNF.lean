/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Module
public meta import Mathlib.Tactic.Ring.RingNF

/-! # `module_nf` tactic -/

public meta section

open Lean hiding Module
open Meta Elab Tactic Qq Mathlib.Tactic List

namespace Mathlib.Tactic.ModuleNF

open Mathlib.Tactic.Module

variable {u v : Level}

/-- Ring-normalize a scalar produced by `Module.parse`. -/
def normalizeScalar (c : Expr) : AtomM Simp.Result := do
  let r₁ ← Algebra.pushCast c
  let r₂ ← try
    RingNF.cleanup {} (← RingNF.evalExpr r₁.expr)
  catch _ => pure { expr := r₁.expr }
  r₁.mkEqTrans r₂

/-- Rebuild `NF.eval l` as a readable sum `c₁ • x₁ + (... + 0)`, with normalized scalars. -/
def toPretty {M : Q(Type v)} {R : Q(Type u)} (iM : Q(AddCommMonoid $M))
    (iR : Q(Semiring $R)) (iRM : Q(Module $R $M)) :
    qNF R M → AtomM (Q($M) × Expr)
  | [] => pure ⟨q((0 : $M)), q(@NF.eval_nil $R $M $iM $iR $iRM)⟩
  | ((r, x), _) :: t => do
    let res ← normalizeScalar r
    let ⟨e, pfT⟩ ← toPretty iM iR iRM t
    have tNF : Q(NF $R $M) := qNF.toNF t
    have pfT' : Q(NF.eval $tNF = $e) := pfT
    have r' : Q($R) := res.expr
    let hrE ← res.getProof
    have hr : Q($r = $r') := hrE
    pure ⟨q($r' • $x + $e),
      q(@NF.eval_cons_eq $R $M $iM $iR $iRM $r $r' $x $tNF $e $hr $pfT')⟩

/-- Normalize an expression in an `AddCommMonoid`: the normal form, and a proof `e = _`.
Fails on atoms, so that the traversal descends into their subterms instead. -/
def evalExpr (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  guard e.isApp
  let ⟨_, M, e⟩ ← inferTypeQ' e
  let iM : Q(AddCommMonoid $M) ← synthInstanceQ q(AddCommMonoid $M)
  let ⟨_, _, iR, iRM, l, pf⟩ ← parse iM e
  if let [((_, x), _)] := l then
    if ← withReducible <| isDefEq x e then failure
  let ⟨e', pf'⟩ ← toPretty iM iR iRM l
  return { expr := e', proof? := some (← mkEqTrans pf pf') }

/-- Tidy the reconstruction: drop `1 •`, `0 •` and zeros, left-associate, `a + -b ↦ a - b`. -/
def cleanup (r : Simp.Result) : MetaM Simp.Result := do
  let thms : SimpTheorems := {}
  let thms ← [``one_smul, ``zero_smul, ``add_zero, ``zero_add, ``neg_one_smul,
    ``mul_one, ``one_mul].foldlM (·.addConst ·) thms
  let thms ← [``add_assoc, ``sub_eq_add_neg].foldlM
    (·.addConst · (post := false) (inv := true)) thms
  let ctx ← Simp.mkContext { failIfUnchanged := false }
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  r.mkEqTrans (← Simp.main r.expr ctx (methods := Simp.mkDefaultMethodsCore {})).1

elab (name := moduleNF) "module_nf" : tactic => do
  let s ← IO.mkRef {}
  let m := AtomM.recurse s {} (wellBehavedDischarge := true) evalExpr cleanup
  liftMetaTactic1 (transformAtTarget (m ·) "module_nf" .error · default)

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a b : R) (x : M) :
    a • x + b • x = (a + b) • x := by module_nf

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : M → M) (a b : R) (x : M) :
    f (a • x + b • x) = f ((a + b) • x) := by
  fail_if_success module
  module_nf

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : M → M) (c a b : R) (x : M) :
    c • f (a • x + b • x) + c • f ((a + b) • x) = (2 : ℕ) • c • f ((a + b) • x) := by
  fail_if_success module
  module_nf

example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R) (v w : M) :
    (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by module_nf

example {V : Type*} [AddCommMonoid V] (x y : V) : x + (y + x) = x + x + y := by module_nf

end Mathlib.Tactic.ModuleNF
