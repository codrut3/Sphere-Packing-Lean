/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Positivity.Core

/-!
# `positivity` extensions for `UpperHalfPlane` and `Complex.exp`

This file registers higher-level `positivity` extensions that belong in Mathlib's
`Analysis.Complex.UpperHalfPlane.Basic` / `MoebiusAction` and `Analysis.Complex.Exponential`,
kept separate from `SpherePacking.Tactic.Positivity.Complex` to preserve Mathlib's layered
import graph.

Registered extensions:

* `UpperHalfPlane.coe` — `(z : ℂ) ≠ 0` even when `ComplexOrder` is not open (`pα? = none`),
  complementing Mathlib's `evalUpperHalfPlaneCoe`;
* `Complex.im (UpperHalfPlane.coe z)` — `0 < (z : ℂ).im`;
* `UpperHalfPlane.denom γ z` — `denom γ z ≠ 0`, enabling `field_simp` to discharge slash-action
  denominator side conditions automatically;
* `Complex.exp w` — `Complex.exp w ≠ 0` (even without `ComplexOrder`);
* `Complex.re (Complex.exp (↑x))` / `Complex.im (Complex.exp (↑x))` — `0 < (cexp ↑x).re` and
  `0 ≤ (cexp ↑x).im`.
-/

@[expose] public section

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Complex UpperHalfPlane

lemma upperHalfPlane_coe_im_pos (z : ℍ) : 0 < (z : ℂ).im :=
  UpperHalfPlane.coe_im z ▸ z.im_pos

lemma re_exp_ofReal_pos (x : ℝ) : 0 < (Complex.exp (x : ℂ)).re := by
  rw [Complex.exp_ofReal_re]; exact Real.exp_pos x

lemma im_exp_ofReal_nonneg (x : ℝ) : 0 ≤ (Complex.exp (x : ℂ)).im := by
  rw [Complex.exp_ofReal_im]

/-- Extract `w : ℂ` from `Complex.re w` or `Complex.im w`, handling both constant-application
and primitive-projection (`Expr.proj`) forms. -/
private meta def matchComplexProjAux? (e : Expr) (constName : Name) (idx : Nat) :
    MetaM (Option Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity constName 1 then
    return some e.appArg!
  match ← whnfR e with
  | .proj ``Complex i w => if i == idx then return some w else return none
  | e' =>
    if e'.isAppOfArity constName 1 then
      return some e'.appArg!
    return none

/-- Extension for the `positivity` tactic: `(z : ℂ) ≠ 0` for `z : ℍ`, even when `ComplexOrder`
is not open (`pα? = none`). -/
@[positivity UpperHalfPlane.coe _]
meta def evalUpperHalfPlaneCoeNeZero : PositivityExt where eval {u α} _zα pα? e := do
  match pα? with
  | some _ => return .none
  | none =>
    match u, α, e with
    | 0, ~q(ℂ), ~q(UpperHalfPlane.coe $z) =>
      assertInstancesCommute
      return .nonzero q(UpperHalfPlane.ne_zero $z)
    | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `UpperHalfPlane.denom γ z ≠ 0`. -/
@[positivity UpperHalfPlane.denom _ _]
meta def evalUpperHalfPlaneDenom : PositivityExt where eval {u α} _zα _ e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(UpperHalfPlane.denom $γ (UpperHalfPlane.coe $z)) =>
    assertInstancesCommute
    return .nonzero q(UpperHalfPlane.denom_ne_zero $γ $z)
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `0 < (z : ℂ).im` for `z : ℍ`, and
`0 ≤ (Complex.exp ↑x).im` for `x : ℝ`. -/
@[positivity Complex.im _]
meta def evalUpperHalfPlaneAndExpIm : PositivityExt where eval {u α} _zα pα? e := do
  match u, α with
  | 0, ~q(ℝ) =>
    let some w ← matchComplexProjAux? e ``Complex.im 1 | return .none
    have w : Q(ℂ) := w.consumeMData
    haveI' : $e =Q Complex.im $w := ⟨⟩
    assertInstancesCommute
    match w with
    | ~q(UpperHalfPlane.coe $z) =>
      match h : pα? with
      | some pα =>
        assumeInstancesCommute
        return h ▸ .positive (pα := pα) q(upperHalfPlane_coe_im_pos $z)
      | none =>
        return h ▸ .nonzero q((upperHalfPlane_coe_im_pos $z).ne')
    | ~q(Complex.exp (Complex.ofReal $x)) =>
      match h : pα? with
      | some pα =>
        assumeInstancesCommute
        return h ▸ .nonnegative (pα := pα) q(im_exp_ofReal_nonneg $x)
      | none => return .none
    | _ => return .none
  | _, _ => return .none

/-- Extension for the `positivity` tactic: `Complex.exp w ≠ 0`. -/
@[positivity Complex.exp _]
meta def evalComplexExpNeZero : PositivityExt where eval {u α} _zα _ e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.exp $w) =>
    assertInstancesCommute
    return .nonzero q(Complex.exp_ne_zero $w)
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `0 < (Complex.exp ↑x).re` for `x : ℝ`. -/
@[positivity Complex.re _]
meta def evalComplexExpRe : PositivityExt where eval {u α} _zα pα? e := do
  match u, α with
  | 0, ~q(ℝ) =>
    let some w ← matchComplexProjAux? e ``Complex.re 0 | return .none
    have w : Q(ℂ) := w.consumeMData
    haveI' : $e =Q Complex.re $w := ⟨⟩
    assertInstancesCommute
    match w with
    | ~q(Complex.exp (Complex.ofReal $x)) =>
      match h : pα? with
      | some pα =>
        assumeInstancesCommute
        return h ▸ .positive (pα := pα) q(re_exp_ofReal_pos $x)
      | none =>
        return h ▸ .nonzero q((re_exp_ofReal_pos $x).ne')
    | _ => return .none
  | _, _ => return .none

end Mathlib.Meta.Positivity
