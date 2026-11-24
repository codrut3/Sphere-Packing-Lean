/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Positivity.Core

/-!
# `positivity` extensions for `Complex`

This file provides `positivity` extensions for complex numbers, depending only on
`Mathlib.Basic.Complex.Basic` and `Mathlib.Tactic.Positivity.Core` (so that it can sit low in
Mathlib's import hierarchy, independent of `Analysis` and `UpperHalfPlane`).

Registered extensions:

* `Complex.I` — always nonzero (`Complex.I_ne_zero`), even without `ComplexOrder` open;
* `OfNat.ofNat` — nonzero numeral literals `(n : α) ≠ 0` via `NeZero` when `α` has no
  `PartialOrder` (such as `ℂ` without `ComplexOrder`);
* `Complex.ofReal` — nonzero when its real argument is nonzero, even without `ComplexOrder` open
  (complementing `Mathlib.Analysis.Complex.Order`, which requires `PartialOrder ℂ`);
* `Complex.normSq` — always nonnegative, and strictly positive whenever its argument is nonzero;
* `Complex.re` and `Complex.im` — structural recursion through `Complex.mk`, purely real
  subexpressions (`ofReal`, `Nat`/`Int`/`Rat`/`NNRat` casts, numerals, and ring/field operations
  on them), `Complex.I`, `+`, `-` (with real subtrahend for `im`), negation, conjugation (`conj` /
  `star`), scalar multiplication (`ℝ`, `ℕ`, `ℤ`, `ℚ`, `ℚ≥0`), multiplication by `I` / `-I` or a
  real expression, division by a real expression, inversion (`z⁻¹.re`, `(-z)⁻¹.im`, `(-z⁻¹).im`),
  and real-numerator quotients (`(c / z).re`, `(-c / z).im`, `(-(c / z)).im`, `(c / -z).im`).

Higher-level extensions (such as `UpperHalfPlane.coe`, `UpperHalfPlane.denom`, and `Complex.exp`)
live in `SpherePacking.Tactic.Positivity.UpperHalfPlane` and compose automatically via
`Positivity.core`.
-/

@[expose] public section

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Complex
open ComplexConjugate
open scoped Complex.SMul

/-! ### Support lemmas -/

section Lemmas

lemma re_of_eq_ofReal {w : ℂ} {r : ℝ} (h : w = (r : ℂ)) : w.re = r := by rw [h, ofReal_re]
lemma im_of_eq_ofReal_nonneg {w : ℂ} {r : ℝ} (h : w = (r : ℂ)) : 0 ≤ w.im := by rw [h, ofReal_im]

lemma eq_ofReal_add {u v : ℂ} {a b : ℝ} (hu : u = (a : ℂ)) (hv : v = (b : ℂ)) :
    u + v = ((a + b : ℝ) : ℂ) := by rw [hu, hv, ofReal_add]
lemma eq_ofReal_sub {u v : ℂ} {a b : ℝ} (hu : u = (a : ℂ)) (hv : v = (b : ℂ)) :
    u - v = ((a - b : ℝ) : ℂ) := by rw [hu, hv, ofReal_sub]
lemma eq_ofReal_neg {u : ℂ} {a : ℝ} (hu : u = (a : ℂ)) :
    -u = ((-a : ℝ) : ℂ) := by rw [hu, ofReal_neg]
lemma eq_ofReal_mul {u v : ℂ} {a b : ℝ} (hu : u = (a : ℂ)) (hv : v = (b : ℂ)) :
    u * v = ((a * b : ℝ) : ℂ) := by rw [hu, hv, ofReal_mul]
lemma eq_ofReal_inv {u : ℂ} {a : ℝ} (hu : u = (a : ℂ)) :
    u⁻¹ = ((a⁻¹ : ℝ) : ℂ) := by rw [hu, ofReal_inv]
lemma eq_ofReal_div {u v : ℂ} {a b : ℝ} (hu : u = (a : ℂ)) (hv : v = (b : ℂ)) :
    u / v = ((a / b : ℝ) : ℂ) := by rw [hu, hv, ofReal_div]
lemma eq_ofReal_pow {u : ℂ} {a : ℝ} (hu : u = (a : ℂ)) (n : ℕ) :
    u ^ n = ((a ^ n : ℝ) : ℂ) := by rw [hu, ofReal_pow]
lemma eq_ofReal_zpow {u : ℂ} {a : ℝ} (hu : u = (a : ℂ)) (k : ℤ) :
    u ^ k = ((a ^ k : ℝ) : ℂ) := by rw [hu, ofReal_zpow]

lemma re_I_nonneg : 0 ≤ I.re := by simp
lemma im_I_pos : 0 < I.im := by simp

lemma eq_imag_I : I = Complex.mk 0 1 := rfl
lemma eq_imag_mul_left {c w : ℂ} {r b : ℝ} (hc : c = (r : ℂ)) (hw : w = Complex.mk 0 b) :
    c * w = Complex.mk 0 (r * b) := by
  rw [hc, hw]; exact Complex.ext (by simp) (by simp)
lemma eq_imag_mul_right {w c : ℂ} {b r : ℝ} (hw : w = Complex.mk 0 b) (hc : c = (r : ℂ)) :
    w * c = Complex.mk 0 (b * r) := by
  rw [hw, hc]; exact Complex.ext (by simp) (by simp)
lemma eq_imag_div {w c : ℂ} {b r : ℝ} (hw : w = Complex.mk 0 b) (hc : c = (r : ℂ)) :
    w / c = Complex.mk 0 (b / r) := by
  rw [hw, hc, div_ofReal]; simp

lemma re_neg_mul_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (-(a * b)).re = r * b.im := by simp [ha]
lemma re_neg_mul_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (-(a * b)).re = a.im * r := by simp [hb]
lemma re_mul_of_eq_imag_left_ne_zero {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r)
    (hr : r ≠ 0) (hb : b.im ≠ 0) : (a * b).re ≠ 0 := by
  rw [ha]; simp [mul_ne_zero hr hb]
lemma re_mul_of_eq_imag_right_ne_zero {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r)
    (ha : a.im ≠ 0) (hr : r ≠ 0) : (a * b).re ≠ 0 := by
  rw [hb]; simp [mul_ne_zero ha hr]
lemma im_mul_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (a * b).im = r * b.re := by simp [ha]
lemma im_mul_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (a * b).im = a.re * r := by simp [hb]

lemma re_neg_I_mul (w : ℂ) : (-(I * w)).re = w.im := by simp
lemma re_neg_mul_I (w : ℂ) : (-(w * I)).re = w.im := by simp
lemma re_negI_mul (w : ℂ) : (-I * w).re = w.im := by simp
lemma re_mul_negI (w : ℂ) : (w * -I).re = w.im := by simp
lemma re_I_mul_neg (w : ℂ) : (I * -w).re = w.im := by simp
lemma re_neg_mul_I' (w : ℂ) : (-w * I).re = w.im := by simp

lemma re_neg_ne_zero {w : ℂ} (hw : w.re ≠ 0) : (-w).re ≠ 0 := by simpa using hw
lemma im_neg_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (-w).im ≠ 0 := by simpa using hw
lemma re_I_mul_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (I * w).re ≠ 0 := by simpa using hw
lemma re_mul_I_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (w * I).re ≠ 0 := by simpa using hw
lemma im_conj_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (conj w).im ≠ 0 := by simpa using hw
lemma im_star_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (star w).im ≠ 0 := by simpa using hw
lemma re_star (w : ℂ) : (star w).re = w.re := by simp

lemma im_sub_of_eq_ofReal {u v : ℂ} {r : ℝ} (hv : v = (r : ℂ)) : (u - v).im = u.im := by
  simp [hv]

lemma re_mul_of_eq_ofReal_left {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c * w).re = r * w.re := by simp [hc]
lemma re_mul_of_eq_ofReal_right {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (w * c).re = w.re * r := by simp [hc]
lemma im_mul_of_eq_ofReal_left {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c * w).im = r * w.im := by simp [hc]
lemma im_mul_of_eq_ofReal_right {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (w * c).im = w.im * r := by simp [hc]

lemma re_div_of_eq_ofReal {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (w / c).re = w.re / r := by simp [hc]
lemma im_div_of_eq_ofReal {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (w / c).im = w.im / r := by simp [hc]

lemma re_ofReal_div {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c / w).re = r * w.re / normSq w := by
  simp [hc, div_re]

lemma im_neg_ofReal_div {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (-c / w).im = r * w.im / normSq w := by
  simp [hc, div_im, neg_div]

lemma im_neg_div_of_eq_ofReal {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (-(c / w)).im = r * w.im / normSq w := by
  rw [← neg_div, im_neg_ofReal_div hc]

lemma im_ofReal_div_neg {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c / -w).im = r * w.im / normSq w := by
  rw [div_neg, im_neg_div_of_eq_ofReal hc]

lemma im_neg_inv_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-w⁻¹).im := by
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_pos hw (normSq_pos.mpr fun h => by simp [h] at hw)

lemma im_neg_inv_nonneg {w : ℂ} (hw : 0 ≤ w.im) : 0 ≤ (-w⁻¹).im := by
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_nonneg hw (normSq_nonneg w)

lemma im_neg_inv_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (-w⁻¹).im ≠ 0 := by
  rw [neg_im, inv_im, neg_div, neg_neg]
  exact div_ne_zero hw (normSq_pos.mpr fun h => hw (by simp [h])).ne'

lemma re_inv_pos {w : ℂ} (hw : 0 < w.re) : 0 < w⁻¹.re := by
  rw [inv_re]
  exact div_pos hw (normSq_pos.mpr fun h => by simp [h] at hw)

lemma re_inv_nonneg {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ w⁻¹.re := by
  rw [inv_re]; exact div_nonneg hw (normSq_nonneg w)

lemma re_inv_ne_zero {w : ℂ} (hw : w.re ≠ 0) : w⁻¹.re ≠ 0 := by
  rw [inv_re]
  exact div_ne_zero hw (normSq_pos.mpr fun h => hw (by simp [h])).ne'

lemma im_inv_neg_pos {w : ℂ} (hw : 0 < w.im) : 0 < (-w)⁻¹.im := by
  rw [inv_im, neg_im, neg_neg, normSq_neg]
  exact div_pos hw (normSq_pos.mpr fun h => by simp [h] at hw)

lemma im_inv_neg_nonneg {w : ℂ} (hw : 0 ≤ w.im) : 0 ≤ (-w)⁻¹.im := by
  rw [inv_im, neg_im, neg_neg, normSq_neg]
  exact div_nonneg hw (normSq_nonneg w)

lemma im_inv_neg_ne_zero {w : ℂ} (hw : w.im ≠ 0) : (-w)⁻¹.im ≠ 0 := by
  rw [inv_im, neg_im, neg_neg, normSq_neg]
  exact div_ne_zero hw (normSq_pos.mpr fun h => hw (by simp [h])).ne'

lemma im_inv_ne_zero {w : ℂ} (hw : w.im ≠ 0) : w⁻¹.im ≠ 0 := by
  rw [inv_im]
  exact div_ne_zero (neg_ne_zero.mpr hw) (normSq_pos.mpr fun h => hw (by simp [h])).ne'

lemma normSq_pos_of_ne_zero {w : ℂ} (hw : w ≠ 0) : 0 < normSq w := normSq_pos.mpr hw
lemma normSq_pos_of_re_ne_zero {w : ℂ} (hw : w.re ≠ 0) : 0 < normSq w :=
  normSq_pos.mpr fun h => hw (by simp [h])
lemma normSq_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < normSq w :=
  normSq_pos.mpr fun h => hw (by simp [h])

lemma mul_pos_of_eq {e a b : ℝ} (h : e = a * b) (ha : 0 < a) (hb : 0 < b) : 0 < e :=
  h ▸ mul_pos ha hb
lemma mul_nonneg_of_eq {e a b : ℝ} (h : e = a * b) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ e :=
  h ▸ mul_nonneg ha hb
lemma mul_ne_zero_of_eq {e a b : ℝ} (h : e = a * b) (ha : a ≠ 0) (hb : b ≠ 0) : e ≠ 0 :=
  h ▸ mul_ne_zero ha hb

lemma div_pos_of_eq {e a b : ℝ} (h : e = a / b) (ha : 0 < a) (hb : 0 < b) : 0 < e :=
  h ▸ div_pos ha hb
lemma div_nonneg_of_eq {e a b : ℝ} (h : e = a / b) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ e :=
  h ▸ div_nonneg ha hb
lemma div_ne_zero_of_eq {e a b : ℝ} (h : e = a / b) (ha : a ≠ 0) (hb : b ≠ 0) : e ≠ 0 :=
  h ▸ div_ne_zero ha hb

lemma add_pos_of_eq {e a b : ℝ} (h : e = a + b) (ha : 0 < a) (hb : 0 < b) : 0 < e :=
  h ▸ add_pos ha hb
lemma add_pos_of_pos_of_nonneg_of_eq {e a b : ℝ} (h : e = a + b) (ha : 0 < a) (hb : 0 ≤ b) :
    0 < e :=
  h ▸ add_pos_of_pos_of_nonneg ha hb
lemma add_pos_of_nonneg_of_pos_of_eq {e a b : ℝ} (h : e = a + b) (ha : 0 ≤ a) (hb : 0 < b) :
    0 < e :=
  h ▸ add_pos_of_nonneg_of_pos ha hb
lemma add_nonneg_of_eq {e a b : ℝ} (h : e = a + b) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ e :=
  h ▸ add_nonneg ha hb

lemma pos_of_eq_real {e r : ℝ} (h : e = r) (hr : 0 < r) : 0 < e := h ▸ hr
lemma nonneg_of_eq_real {e r : ℝ} (h : e = r) (hr : 0 ≤ r) : 0 ≤ e := h ▸ hr
lemma ne_zero_of_eq_real {e r : ℝ} (h : e = r) (hr : r ≠ 0) : e ≠ 0 := h ▸ hr

lemma smul_re_nat (n : ℕ) (w : ℂ) : (n • w).re = (n : ℝ) * w.re := by simp [nsmul_eq_mul]
lemma smul_im_nat (n : ℕ) (w : ℂ) : (n • w).im = (n : ℝ) * w.im := by simp [nsmul_eq_mul]
lemma smul_re_int (n : ℤ) (w : ℂ) : (n • w).re = (n : ℝ) * w.re := by simp [zsmul_eq_mul]
lemma smul_im_int (n : ℤ) (w : ℂ) : (n • w).im = (n : ℝ) * w.im := by simp [zsmul_eq_mul]
lemma smul_re_rat (q : ℚ) (w : ℂ) : (q • w).re = (q : ℝ) * w.re := by simp [Rat.smul_def]
lemma smul_im_rat (q : ℚ) (w : ℂ) : (q • w).im = (q : ℝ) * w.im := by simp [Rat.smul_def]
lemma smul_re_nnrat (q : ℚ≥0) (w : ℂ) : (q • w).re = (q : ℝ) * w.re := by simp [NNRat.smul_def]
lemma smul_im_nnrat (q : ℚ≥0) (w : ℂ) : (q • w).im = (q : ℝ) * w.im := by simp [NNRat.smul_def]
lemma smul_re_real (r : ℝ) (w : ℂ) : (r • w).re = r * w.re := by simp
lemma smul_im_real (r : ℝ) (w : ℂ) : (r • w).im = r * w.im := by simp

end Lemmas

/-! ### Meta helpers -/

/-- Standard `ℝ` strictness result (always computed with `PartialOrder ℝ`). -/
private meta abbrev RealStrictness (e : Q(ℝ)) :=
  Strictness (q(inferInstance) : Q(Zero ℝ)) e (some q(inferInstance))

/-- Adapt a `RealStrictness e'` into `Strictness zα e pα?` given `$α =Q ℝ` and `$e =Q $e'`. -/
private meta def adaptRealStrictness {α : Q(Type)} {zα : Q(Zero $α)}
    {pα? : Option Q(PartialOrder $α)} {e : Q($α)} {e' : Q(ℝ)}
    (res : RealStrictness e') (_ : $α =Q ℝ := ⟨⟩) (_ : $e =Q $e' := ⟨⟩) :
    MetaM (Strictness zα e pα?) := do
  assertInstancesCommute
  match h : pα?, res with
  | some pα, .positive pf =>
    assumeInstancesCommute
    return h ▸ .positive (pα := pα) q($pf)
  | some pα, .nonnegative pf =>
    assumeInstancesCommute
    return h ▸ .nonnegative (pα := pα) q($pf)
  | _, .nonzero pf =>
    return .nonzero q($pf)
  | none, .positive pf =>
    return .nonzero q(ne_of_gt $pf)
  | _, _ => return .none

/-- Extract `w : ℂ` from `Complex.re w` or `Complex.im w`, handling both constant-application
and primitive-projection (`Expr.proj`) forms. -/
private meta def matchComplexProj? (e : Expr) (constName : Name) (idx : Nat) :
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

/-- Syntactically recognize complex expressions that are coerced real numbers (including
ring/field operations and powers built solely from real coercions and numerals), returning
`⟨r, pf⟩` with `pf : c = (r : ℂ)`. Does not invoke `Positivity.core`. -/
private meta partial def extractReal? (c : Q(ℂ)) :
    MetaM (Option (Σ r : Q(ℝ), Q($c = ($r : ℂ)))) := do
  match c with
  | ~q(Complex.ofReal $r) =>
    return some ⟨r, q(rfl)⟩
  | ~q(Nat.cast $n) =>
    return some ⟨q(($n : ℝ)), q((Complex.ofReal_natCast $n).symm)⟩
  | ~q(Int.cast $n) =>
    return some ⟨q(($n : ℝ)), q((Complex.ofReal_intCast $n).symm)⟩
  | ~q(Rat.cast $r) =>
    return some ⟨q(($r : ℝ)), q((Complex.ofReal_ratCast $r).symm)⟩
  | ~q(NNRat.cast $r) =>
    return some ⟨q(($r : ℝ)), q((Complex.ofReal_nnratCast $r).symm)⟩
  | ~q(OfNat.ofNat $n (self := _)) =>
    let some n' := n.rawNatLit? | return none
    if n' == 0 then
      return some ⟨q((0 : ℝ)), (q(Complex.ofReal_zero.symm) :)⟩
    else if n' == 1 then
      return some ⟨q((1 : ℝ)), (q(Complex.ofReal_one.symm) :)⟩
    else
      let _i : Q(Nat.AtLeastTwo $n) ← synthInstanceQ q(Nat.AtLeastTwo $n)
      return some ⟨q(OfNat.ofNat $n), (q((Complex.ofReal_ofNat $n).symm) :)⟩
  | ~q(OfScientific.ofScientific $m $s $e) =>
    return some ⟨q(OfScientific.ofScientific $m $s $e),
      q((Complex.ofReal_ofScientific $m $s $e).symm)⟩
  | ~q($a + $b) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    let some ⟨rb, hb⟩ ← extractReal? b | return none
    return some ⟨q($ra + $rb), q(eq_ofReal_add $ha $hb)⟩
  | ~q($a - $b) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    let some ⟨rb, hb⟩ ← extractReal? b | return none
    return some ⟨q($ra - $rb), q(eq_ofReal_sub $ha $hb)⟩
  | ~q(-$a) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    return some ⟨q(-$ra), q(eq_ofReal_neg $ha)⟩
  | ~q($a * $b) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    let some ⟨rb, hb⟩ ← extractReal? b | return none
    return some ⟨q($ra * $rb), q(eq_ofReal_mul $ha $hb)⟩
  | ~q($a⁻¹) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    return some ⟨q($ra⁻¹), q(eq_ofReal_inv $ha)⟩
  | ~q($a / $b) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    let some ⟨rb, hb⟩ ← extractReal? b | return none
    return some ⟨q($ra / $rb), q(eq_ofReal_div $ha $hb)⟩
  | ~q(@HPow.hPow ℂ ℕ ℂ _ $a $n) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    return some ⟨q($ra ^ $n), q(eq_ofReal_pow $ha $n)⟩
  | ~q(@HPow.hPow ℂ ℤ ℂ _ $a $k) =>
    let some ⟨ra, ha⟩ ← extractReal? a | return none
    return some ⟨q($ra ^ $k), q(eq_ofReal_zpow $ha $k)⟩
  | _ => return none

/-- Syntactically recognize purely imaginary complex expressions (such as `I`, `2 * π * I`,
`I * t`, `I / t`), returning `⟨r, pf⟩` with `pf : c = Complex.mk 0 r`. Does not invoke
`Positivity.core`. -/
private meta partial def extractImag? (c : Q(ℂ)) :
    MetaM (Option (Σ r : Q(ℝ), Q($c = Complex.mk 0 $r))) := do
  match c with
  | ~q(Complex.I) =>
    return some ⟨q((1 : ℝ)), q(eq_imag_I)⟩
  | ~q($a * $b) =>
    if let some ⟨r, ha⟩ ← extractReal? a then
      if let some ⟨ib, hb⟩ ← extractImag? b then
        return some ⟨q($r * $ib), q(eq_imag_mul_left $ha $hb)⟩
    if let some ⟨ia, ha⟩ ← extractImag? a then
      if let some ⟨r, hb⟩ ← extractReal? b then
        return some ⟨q($ia * $r), q(eq_imag_mul_right $ha $hb)⟩
    return none
  | ~q($a / $b) =>
    if let some ⟨ia, ha⟩ ← extractImag? a then
      if let some ⟨r, hb⟩ ← extractReal? b then
        return some ⟨q($ia / $r), q(eq_imag_div $ha $hb)⟩
    return none
  | _ => return none

/-- Run `Positivity.core` on a real expression with standard `ℝ` instances, catching failures. -/
private meta def coreReal (r : Q(ℝ)) : MetaM (RealStrictness r) :=
  catchNone (core q(inferInstance) (some q(inferInstance)) r)

/-- Transfer a `RealStrictness` result along an equality `e = r` in `ℝ`. -/
private meta def liftEqReal {e r : Q(ℝ)} (eqPf : Q($e = $r))
    (res : RealStrictness r) : RealStrictness e :=
  match res with
  | .positive pf => .positive q(pos_of_eq_real $eqPf $pf)
  | .nonnegative pf => .nonnegative q(nonneg_of_eq_real $eqPf $pf)
  | .nonzero pf => .nonzero q(ne_zero_of_eq_real $eqPf $pf)
  | .none => .none

/-- Combine two `RealStrictness` results for `e = a + b` in `ℝ`. -/
private meta def combineAddReal {e a b : Q(ℝ)} (eqPf : Q($e = $a + $b))
    (ra : RealStrictness a) (rb : RealStrictness b) : RealStrictness e :=
  match ra, rb with
  | .positive pa, .positive pb => .positive q(add_pos_of_eq $eqPf $pa $pb)
  | .positive pa, .nonnegative pb => .positive q(add_pos_of_pos_of_nonneg_of_eq $eqPf $pa $pb)
  | .nonnegative pa, .positive pb => .positive q(add_pos_of_nonneg_of_pos_of_eq $eqPf $pa $pb)
  | .nonnegative pa, .nonnegative pb => .nonnegative q(add_nonneg_of_eq $eqPf $pa $pb)
  | _, _ => .none

/-- Combine two `RealStrictness` results for `e = a * b` in `ℝ`. -/
private meta def combineMulReal {e a b : Q(ℝ)} (eqPf : Q($e = $a * $b))
    (ra : RealStrictness a) (rb : RealStrictness b) : RealStrictness e :=
  match ra.toPositive, rb.toPositive with
  | some pa, some pb => .positive q(mul_pos_of_eq $eqPf $pa $pb)
  | _, _ =>
    match ra.toNonneg, rb.toNonneg with
    | some pa, some pb => .nonnegative q(mul_nonneg_of_eq $eqPf $pa $pb)
    | _, _ =>
      match ra.toNonzero, rb.toNonzero with
      | some pa, some pb => .nonzero q(mul_ne_zero_of_eq $eqPf $pa $pb)
      | _, _ => .none

/-- Combine two `RealStrictness` results for `e = a / b` in `ℝ`. -/
private meta def combineDivReal {e a b : Q(ℝ)} (eqPf : Q($e = $a / $b))
    (ra : RealStrictness a) (rb : RealStrictness b) : RealStrictness e :=
  match ra.toPositive, rb.toPositive with
  | some pa, some pb => .positive q(div_pos_of_eq $eqPf $pa $pb)
  | _, _ =>
    match ra.toNonneg, rb.toNonneg with
    | some pa, some pb => .nonnegative q(div_nonneg_of_eq $eqPf $pa $pb)
    | _, _ =>
      match ra.toNonzero, rb.toNonzero with
      | some pa, some pb => .nonzero q(div_ne_zero_of_eq $eqPf $pa $pb)
      | _, _ => .none

/-! ### `positivity` extensions -/

/-- Extension for the `positivity` tactic: `Complex.I` is nonzero (works without
`ComplexOrder`). -/
@[positivity Complex.I]
meta def evalComplexI : PositivityExt where eval {u α} _zα _ e := do
  match u, α, e with
  | 0, ~q(ℂ), ~q(Complex.I) =>
    assertInstancesCommute
    return .nonzero q(Complex.I_ne_zero)
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: nonzero numeral literals `(n : α) ≠ 0` via `NeZero`
when `α` has no `PartialOrder` (such as `ℂ` without `ComplexOrder`). -/
@[positivity OfNat.ofNat _]
meta def evalOfNatNeZero : PositivityExt where eval {_u _α} _zα pα? e := do
  match pα? with
  | some _ => return .none
  | none =>
    let _nz ← synthInstanceQ q(NeZero $e)
    assertInstancesCommute
    return .nonzero q(NeZero.ne $e)

/-- Extension for the `positivity` tactic: `(r : ℂ) ≠ 0` whenever `r ≠ 0`, even when
`ComplexOrder` is not open (`pα? = none`). -/
@[positivity Complex.ofReal _]
meta def evalComplexOfRealNeZero : PositivityExt where eval {u α} _zα pα? e := do
  -- When `pα? = some _`, Mathlib's `evalComplexOfReal` handles `<`/`≤`/`≠`;
  -- here we cover the `pα? = none` case (without `open scoped ComplexOrder`).
  match pα? with
  | some _ => return .none
  | none =>
    match u, α, e with
    | 0, ~q(ℂ), ~q(Complex.ofReal $r) =>
      assertInstancesCommute
      match ← coreReal r with
      | .positive pr => return .nonzero q(Complex.ofReal_ne_zero.mpr (ne_of_gt $pr))
      | .nonzero pr => return .nonzero q(Complex.ofReal_ne_zero.mpr $pr)
      | _ => return .none
    | _, _, _ => return .none

/-- Extension for the `positivity` tactic: `Complex.normSq z` is always nonnegative, and strictly
positive whenever `positivity` can show `z ≠ 0`, `z.re ≠ 0`, or `z.im ≠ 0`. -/
@[positivity Complex.normSq _]
meta def evalComplexNormSq : PositivityExt where eval {u α} zα pα? e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.normSq $w) =>
    let zℂ : Q(Zero ℂ) := q(inferInstance)
    let pℂ? ← try? <| synthInstanceQ q(PartialOrder ℂ)
    let res : RealStrictness q(Complex.normSq $w) ← do
      if let some hw := (← catchNone (core zℂ pℂ? w)).toNonzero then
        pure (.positive q(normSq_pos_of_ne_zero $hw))
      else if let some hre := (← coreReal q(Complex.re $w)).toNonzero then
        pure (.positive q(normSq_pos_of_re_ne_zero $hre))
      else if let some him := (← coreReal q(Complex.im $w)).toNonzero then
        pure (.positive q(normSq_pos_of_im_ne_zero $him))
      else
        pure (.nonnegative q(Complex.normSq_nonneg $w))
    adaptRealStrictness (zα := zα) (pα? := pα?) (e := e) res
  | _, _, _ => return .none

/-- Core structural positivity analysis for `Complex.re w`. -/
private meta def evalComplexReCore (w : Q(ℂ)) : MetaM (RealStrictness q(Complex.re $w)) := do
  -- 1. Purely real subexpressions (`ofReal`, casts, numerals, and real ring/field combinations)
  if let some ⟨r, hr⟩ ← extractReal? w then
    return liftEqReal q(re_of_eq_ofReal $hr) (← coreReal r)
  -- 2. Literal `Complex.mk a b` (checked syntactically so structure eta does not match all `w : ℂ`)
  if w.isAppOfArity ``Complex.mk 2 then
    have a : Q(ℝ) := w.appFn!.appArg!
    have b : Q(ℝ) := w.appArg!
    haveI' : $w =Q Complex.mk $a $b := ⟨⟩
    return liftEqReal q(rfl) (← coreReal a)
  -- 3. Structural recursion on complex constructors and operations
  match w with
  | ~q(Complex.I) =>
    return .nonnegative q(re_I_nonneg)
  | ~q($a + $b) =>
    return combineAddReal q(Complex.add_re $a $b)
      (← coreReal q(Complex.re $a)) (← coreReal q(Complex.re $b))
  | ~q(-(Complex.I * $v)) =>
    return liftEqReal q(re_neg_I_mul $v) (← coreReal q(Complex.im $v))
  | ~q(-($v * Complex.I)) =>
    return liftEqReal q(re_neg_mul_I $v) (← coreReal q(Complex.im $v))
  | ~q(-Complex.I * $v) =>
    return liftEqReal q(re_negI_mul $v) (← coreReal q(Complex.im $v))
  | ~q($v * -Complex.I) =>
    return liftEqReal q(re_mul_negI $v) (← coreReal q(Complex.im $v))
  | ~q(Complex.I * -$v) =>
    return liftEqReal q(re_I_mul_neg $v) (← coreReal q(Complex.im $v))
  | ~q(-$v * Complex.I) =>
    return liftEqReal q(re_neg_mul_I' $v) (← coreReal q(Complex.im $v))
  | ~q(Complex.I * $v) =>
    if let some hv := (← coreReal q(Complex.im $v)).toNonzero then
      return .nonzero q(re_I_mul_ne_zero $hv)
    return .none
  | ~q($v * Complex.I) =>
    if let some hv := (← coreReal q(Complex.im $v)).toNonzero then
      return .nonzero q(re_mul_I_ne_zero $hv)
    return .none
  | ~q(-($a * $b)) =>
    if let some ⟨r, ha⟩ ← extractImag? a then
      return combineMulReal q(re_neg_mul_of_eq_imag_left $ha)
        (← coreReal r) (← coreReal q(Complex.im $b))
    if let some ⟨r, hb⟩ ← extractImag? b then
      return combineMulReal q(re_neg_mul_of_eq_imag_right $hb)
        (← coreReal q(Complex.im $a)) (← coreReal r)
    if let some hab := (← coreReal q(Complex.re ($a * $b))).toNonzero then
      return .nonzero q(re_neg_ne_zero $hab)
    return .none
  | ~q(-$a) =>
    if let some ha := (← coreReal q(Complex.re $a)).toNonzero then
      return .nonzero q(re_neg_ne_zero $ha)
    return .none
  | ~q(conj $a) =>
    return liftEqReal q(Complex.conj_re $a) (← coreReal q(Complex.re $a))
  | ~q(Star.star $a) =>
    return liftEqReal q(re_star $a) (← coreReal q(Complex.re $a))
  | ~q(@HSMul.hSMul ℝ ℂ ℂ _ $r $v) =>
    return combineMulReal q(smul_re_real $r $v)
      (← coreReal r) (← coreReal q(Complex.re $v))
  | ~q(@HSMul.hSMul ℕ ℂ ℂ _ $n $v) =>
    return combineMulReal q(smul_re_nat $n $v)
      (← coreReal q(($n : ℝ))) (← coreReal q(Complex.re $v))
  | ~q(@HSMul.hSMul ℤ ℂ ℂ _ $n $v) =>
    return combineMulReal q(smul_re_int $n $v)
      (← coreReal q(($n : ℝ))) (← coreReal q(Complex.re $v))
  | ~q(@HSMul.hSMul ℚ ℂ ℂ _ $r $v) =>
    return combineMulReal q(smul_re_rat $r $v)
      (← coreReal q(($r : ℝ))) (← coreReal q(Complex.re $v))
  | ~q(@HSMul.hSMul ℚ≥0 ℂ ℂ _ $r $v) =>
    return combineMulReal q(smul_re_nnrat $r $v)
      (← coreReal q(($r : ℝ))) (← coreReal q(Complex.re $v))
  | ~q($a * $b) =>
    if let some ⟨r, ha⟩ ← extractReal? a then
      return combineMulReal q(re_mul_of_eq_ofReal_left $ha)
        (← coreReal r) (← coreReal q(Complex.re $b))
    if let some ⟨r, hb⟩ ← extractReal? b then
      return combineMulReal q(re_mul_of_eq_ofReal_right $hb)
        (← coreReal q(Complex.re $a)) (← coreReal r)
    return .none
  | ~q($a / $b) =>
    if let some ⟨r, hb⟩ ← extractReal? b then
      return combineDivReal q(re_div_of_eq_ofReal $hb)
        (← coreReal q(Complex.re $a)) (← coreReal r)
    if let some ⟨r, ha⟩ ← extractReal? a then
      let rRes ← coreReal r
      let bRes ← coreReal q(Complex.re $b)
      let normSqRes : RealStrictness q(Complex.normSq $b) :=
        match bRes.toNonzero with
        | some hb => .positive q(normSq_pos_of_re_ne_zero $hb)
        | none => .nonnegative q(Complex.normSq_nonneg $b)
      return combineDivReal q(re_ofReal_div $ha)
        (combineMulReal q(rfl) rRes bRes) normSqRes
    return .none
  | ~q($a⁻¹) =>
    match ← coreReal q(Complex.re $a) with
    | .positive pf => return .positive q(re_inv_pos $pf)
    | .nonnegative pf => return .nonnegative q(re_inv_nonneg $pf)
    | .nonzero pf => return .nonzero q(re_inv_ne_zero $pf)
    | .none => return .none
  | _ => return .none

/-- Extension for the `positivity` tactic: real part `Complex.re w` of a complex expression. -/
@[positivity Complex.re _]
meta def evalComplexRe : PositivityExt where eval {u α} zα pα? e := do
  match u, α with
  | 0, ~q(ℝ) =>
    let some w ← matchComplexProj? e ``Complex.re 0 | return .none
    have w : Q(ℂ) := w.consumeMData
    haveI' : $e =Q Complex.re $w := ⟨⟩
    adaptRealStrictness (zα := zα) (pα? := pα?) (e := e) (← evalComplexReCore w)
  | _, _ => return .none

/-- Core structural positivity analysis for `Complex.im w`. -/
private meta def evalComplexImCore (w : Q(ℂ)) : MetaM (RealStrictness q(Complex.im $w)) := do
  -- 1. Purely real subexpressions have imaginary part `0 ≥ 0`
  if let some ⟨_r, hr⟩ ← extractReal? w then
    return .nonnegative q(im_of_eq_ofReal_nonneg $hr)
  -- 2. Literal `Complex.mk a b` (checked syntactically so structure eta does not match all `w : ℂ`)
  if w.isAppOfArity ``Complex.mk 2 then
    have a : Q(ℝ) := w.appFn!.appArg!
    have b : Q(ℝ) := w.appArg!
    haveI' : $w =Q Complex.mk $a $b := ⟨⟩
    return liftEqReal q(rfl) (← coreReal b)
  -- 3. Structural recursion on complex constructors and operations
  match w with
  | ~q(Complex.I) =>
    return .positive q(im_I_pos)
  | ~q($a + $b) =>
    return combineAddReal q(Complex.add_im $a $b)
      (← coreReal q(Complex.im $a)) (← coreReal q(Complex.im $b))
  | ~q($a - $b) =>
    if let some ⟨_r, hb⟩ ← extractReal? b then
      return liftEqReal q(im_sub_of_eq_ofReal $hb) (← coreReal q(Complex.im $a))
    return .none
  | ~q(Complex.I * $v) =>
    return liftEqReal q(Complex.I_mul_im $v) (← coreReal q(Complex.re $v))
  | ~q($v * Complex.I) =>
    return liftEqReal q(Complex.mul_I_im $v) (← coreReal q(Complex.re $v))
  | ~q(-$a) =>
    let res : RealStrictness q(Complex.im $w) ←
      match a with
      | ~q($c / $b) =>
        if let some ⟨r, hc⟩ ← extractReal? c then
          let rRes ← coreReal r
          let bRes ← coreReal q(Complex.im $b)
          let normSqRes : RealStrictness q(Complex.normSq $b) :=
            match bRes.toNonzero with
            | some hb => .positive q(normSq_pos_of_im_ne_zero $hb)
            | none => .nonnegative q(Complex.normSq_nonneg $b)
          pure <| combineDivReal q(im_neg_div_of_eq_ofReal $hc)
            (combineMulReal q(rfl) rRes bRes) normSqRes
        else pure .none
      | ~q($b⁻¹) =>
        match ← coreReal q(Complex.im $b) with
        | .positive pf => pure (.positive q(im_neg_inv_pos $pf))
        | .nonnegative pf => pure (.nonnegative q(im_neg_inv_nonneg $pf))
        | .nonzero pf => pure (.nonzero q(im_neg_inv_ne_zero $pf))
        | .none => pure .none
      | _ => pure .none
    match res with
    | .none =>
      if let some ha := (← coreReal q(Complex.im $a)).toNonzero then
        return .nonzero q(im_neg_ne_zero $ha)
      return .none
    | _ => return res
  | ~q(conj $a) =>
    if let some ha := (← coreReal q(Complex.im $a)).toNonzero then
      return .nonzero q(im_conj_ne_zero $ha)
    return .none
  | ~q(Star.star $a) =>
    if let some ha := (← coreReal q(Complex.im $a)).toNonzero then
      return .nonzero q(im_star_ne_zero $ha)
    return .none
  | ~q(@HSMul.hSMul ℝ ℂ ℂ _ $r $v) =>
    return combineMulReal q(smul_im_real $r $v)
      (← coreReal r) (← coreReal q(Complex.im $v))
  | ~q(@HSMul.hSMul ℕ ℂ ℂ _ $n $v) =>
    return combineMulReal q(smul_im_nat $n $v)
      (← coreReal q(($n : ℝ))) (← coreReal q(Complex.im $v))
  | ~q(@HSMul.hSMul ℤ ℂ ℂ _ $n $v) =>
    return combineMulReal q(smul_im_int $n $v)
      (← coreReal q(($n : ℝ))) (← coreReal q(Complex.im $v))
  | ~q(@HSMul.hSMul ℚ ℂ ℂ _ $r $v) =>
    return combineMulReal q(smul_im_rat $r $v)
      (← coreReal q(($r : ℝ))) (← coreReal q(Complex.im $v))
  | ~q(@HSMul.hSMul ℚ≥0 ℂ ℂ _ $r $v) =>
    return combineMulReal q(smul_im_nnrat $r $v)
      (← coreReal q(($r : ℝ))) (← coreReal q(Complex.im $v))
  | ~q($a * $b) =>
    if let some ⟨r, ha⟩ ← extractReal? a then
      return combineMulReal q(im_mul_of_eq_ofReal_left $ha)
        (← coreReal r) (← coreReal q(Complex.im $b))
    if let some ⟨r, hb⟩ ← extractReal? b then
      return combineMulReal q(im_mul_of_eq_ofReal_right $hb)
        (← coreReal q(Complex.im $a)) (← coreReal r)
    if let some ⟨r, ha⟩ ← extractImag? a then
      return combineMulReal q(im_mul_of_eq_imag_left $ha)
        (← coreReal r) (← coreReal q(Complex.re $b))
    if let some ⟨r, hb⟩ ← extractImag? b then
      return combineMulReal q(im_mul_of_eq_imag_right $hb)
        (← coreReal q(Complex.re $a)) (← coreReal r)
    return .none
  | ~q($a / $b) =>
    if let some ⟨r, hb⟩ ← extractReal? b then
      return combineDivReal q(im_div_of_eq_ofReal $hb)
        (← coreReal q(Complex.im $a)) (← coreReal r)
    let res1 : RealStrictness q(Complex.im $w) ←
      match a with
      | ~q(-$a') =>
        if let some ⟨r, ha⟩ ← extractReal? a' then
          let rRes ← coreReal r
          let bRes ← coreReal q(Complex.im $b)
          let normSqRes : RealStrictness q(Complex.normSq $b) :=
            match bRes.toNonzero with
            | some hb => .positive q(normSq_pos_of_im_ne_zero $hb)
            | none => .nonnegative q(Complex.normSq_nonneg $b)
          pure <| combineDivReal q(im_neg_ofReal_div $ha)
            (combineMulReal q(rfl) rRes bRes) normSqRes
        else pure .none
      | _ => pure .none
    match res1 with
    | .none =>
      match b with
      | ~q(-$b') =>
        if let some ⟨r, ha⟩ ← extractReal? a then
          let rRes ← coreReal r
          let bRes ← coreReal q(Complex.im $b')
          let normSqRes : RealStrictness q(Complex.normSq $b') :=
            match bRes.toNonzero with
            | some hb => .positive q(normSq_pos_of_im_ne_zero $hb)
            | none => .nonnegative q(Complex.normSq_nonneg $b')
          return combineDivReal q(im_ofReal_div_neg $ha)
            (combineMulReal q(rfl) rRes bRes) normSqRes
        return .none
      | _ => return .none
    | _ => return res1
  | ~q((-$a)⁻¹) =>
    match ← coreReal q(Complex.im $a) with
    | .positive pf => return .positive q(im_inv_neg_pos $pf)
    | .nonnegative pf => return .nonnegative q(im_inv_neg_nonneg $pf)
    | .nonzero pf => return .nonzero q(im_inv_neg_ne_zero $pf)
    | .none => return .none
  | ~q($a⁻¹) =>
    if let some ha := (← coreReal q(Complex.im $a)).toNonzero then
      return .nonzero q(im_inv_ne_zero $ha)
    return .none
  | _ => return .none

/-- Extension for the `positivity` tactic: imaginary part `Complex.im w` of a complex
expression. -/
@[positivity Complex.im _]
meta def evalComplexIm : PositivityExt where eval {u α} zα pα? e := do
  match u, α with
  | 0, ~q(ℝ) =>
    let some w ← matchComplexProj? e ``Complex.im 1 | return .none
    have w : Q(ℂ) := w.consumeMData
    haveI' : $e =Q Complex.im $w := ⟨⟩
    adaptRealStrictness (zα := zα) (pα? := pα?) (e := e) (← evalComplexImCore w)
  | _, _ => return .none

end Mathlib.Meta.Positivity
