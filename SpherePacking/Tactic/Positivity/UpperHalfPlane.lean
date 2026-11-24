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

/-- Return a `.positive` (or `.nonzero` if `pα? = none`) `Strictness` from a proof of `0 < e'`. -/
private meta def strictnessOfRealPos {α : Q(Type)} {zα : Q(Zero $α)}
    {pα? : Option Q(PartialOrder $α)} {e : Q($α)} {e' : Q(ℝ)}
    (pf : Q(0 < $e')) (_ : $α =Q ℝ := ⟨⟩) (_ : $e =Q $e' := ⟨⟩) :
    MetaM (Strictness zα e pα?) := do
  assertInstancesCommute
  match h : pα? with
  | some pα => assumeInstancesCommute; return h ▸ .positive (pα := pα) q($pf)
  | none => return h ▸ .nonzero q(($pf).ne')

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

/-- Extension for the `positivity` tactic: `0 < (z : ℂ).im` for `z : ℍ`. -/
@[positivity Complex.im (UpperHalfPlane.coe _)]
meta def evalUpperHalfPlaneCoeIm : PositivityExt where eval {u α} zα pα? e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.im (UpperHalfPlane.coe $z)) =>
    strictnessOfRealPos (zα := zα) (pα? := pα?) (e := e) q(upperHalfPlane_coe_im_pos $z)
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `Complex.exp w ≠ 0`. -/
@[positivity Complex.exp _]
meta def evalComplexExpNeZero : PositivityExt where eval {u α} _zα _ e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.exp $w) =>
    assertInstancesCommute
    return .nonzero q(Complex.exp_ne_zero $w)
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `0 < (Complex.exp ↑x).re` for `x : ℝ`. -/
@[positivity Complex.re (Complex.exp _)]
meta def evalComplexExpRe : PositivityExt where eval {u α} zα pα? e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.re (Complex.exp (Complex.ofReal $x))) =>
    strictnessOfRealPos (zα := zα) (pα? := pα?) (e := e) q(re_exp_ofReal_pos $x)
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `0 ≤ (Complex.exp ↑x).im` for `x : ℝ`. -/
@[positivity Complex.im (Complex.exp _)]
meta def evalComplexExpIm : PositivityExt where eval {u α} _zα pα? e := do
  match h : pα? with
  | none => return .none
  | some pα =>
    match u, α, e with
    | 0, ~q(ℝ), ~q(Complex.im (Complex.exp (Complex.ofReal $x))) =>
      assertInstancesCommute
      return h ▸ .nonnegative (pα := pα) q(im_exp_ofReal_nonneg $x)
    | _, _, _ => return .none

end Mathlib.Meta.Positivity
