/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public meta import Mathlib.Data.Rat.Init

/-!
# Reduction of a rational matrix to Hessenberg form
-/

public meta section

namespace Mathlib.Tactic.Hessenberg

/-- A similarity `Aσ * L = L * H` of a rational matrix `A` to upper Hessenberg form, where
`Aσ := A.submatrix σ σ` for the arrangement `σ` of the interchanges. -/
structure Reduction where
  /-- The row and column interchanges, in order. The permutation `σ` is their product. -/
  swaps : Array (ℕ × ℕ)
  /-- The unit lower triangular transform. -/
  L : Array (Array Rat)
  /-- The upper Hessenberg form. -/
  H : Array (Array Rat)

def arrangement (n : ℕ) (swaps : Array (ℕ × ℕ)) : Array ℕ :=
  swaps.foldl (fun ord (a, b) => ord.swapIfInBounds a b) (Array.range n)

def Reduction.perm (d : Reduction) : Array ℕ := arrangement d.L.size d.swaps

def reduce (n : ℕ) (A : Array (Array Rat)) : Option Reduction := Id.run do
  let entry (M : Array (Array Rat)) (i j : ℕ) : Rat := (M.getD i #[]).getD j 0
  let shear (W : Array (Array Rat)) (k i : ℕ) (m : Rat) : Array (Array Rat) :=
    let W := W.set! i (Array.zipWith (fun a b => a - m * b) (W.getD i #[]) (W.getD (k + 1) #[]))
    W.map fun row => row.set! (k + 1) (row.getD (k + 1) 0 + m * row.getD i 0)
  let mut W := A
  let mut swaps : Array (ℕ × ℕ) := #[]
  for k in 0...(n - 2) do
    if entry W (k + 1) k == 0 then
      if let some r := (Array.range n).find? fun r => k + 1 < r && entry W r k != 0 then
        W := (W.swapIfInBounds (k + 1) r).map (·.swapIfInBounds (k + 1) r)
        swaps := swaps.push (k + 1, r)
    let pivot := entry W (k + 1) k
    if pivot != 0 then
      for i in (k + 2)...n do
        W := shear W k i (entry W i k / pivot)
  let perm := arrangement n swaps
  let Aσ := perm.map fun i => perm.map fun j => entry A i j
  let mut H := Aσ
  let mut L : Array (Array Rat) :=
    Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i == j then 1 else 0
  for k in 0...(n - 2) do
    let pivot := entry H (k + 1) k
    for i in (k + 2)...n do
      if entry H i k != 0 then
        if pivot == 0 then return none
        let m := entry H i k / pivot
        H := shear H k i m
        L := L.modify i (·.set! (k + 1) m)
  let mul (X Y : Array (Array Rat)) : Array (Array Rat) :=
    X.map fun row => Array.ofFn (n := n) fun j =>
      (Array.zipWith (· * ·) row (Y.map (·.getD j 0))).foldl (· + ·) 0
  unless mul Aσ L == mul L H do return none
  unless (Array.range n).all fun i => (Array.range n).all fun j => i ≤ j + 1 || entry H i j == 0 do
    return none
  return some { swaps, L, H }

end Mathlib.Tactic.Hessenberg

end
