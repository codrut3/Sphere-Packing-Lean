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
* `Complex.re` and `Complex.im` — reduces complex expressions by one algebraic step to `ℝ` and
  delegates back to `Positivity.core`, handling `Complex.mk`, purely real subexpressions (`ofReal`,
  casts, numerals, and ring/field combinations), `Complex.I`, `+`, `-` (real subtrahend for `im`),
  negation, conjugation (`conj` / `star`), scalar multiplication (`ℝ`, `ℕ`, `ℤ`, `ℚ`, `ℚ≥0`),
  multiplication/division by real or purely imaginary factors, inversion (`z⁻¹`, `(-z)⁻¹`, `-z⁻¹`),
  and real-numerator quotients (`c / z`, `-c / z`, `-(c / z)`, `c / -z`).

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

lemma pos_of_eq_real {e r : ℝ} (h : e = r) (hr : 0 < r) : 0 < e := h ▸ hr
lemma nonneg_of_eq_real {e r : ℝ} (h : e = r) (hr : 0 ≤ r) : 0 ≤ e := h ▸ hr
lemma ne_zero_of_eq_real {e r : ℝ} (h : e = r) (hr : r ≠ 0) : e ≠ 0 := h ▸ hr
lemma ne_zero_of_eq_neg {e r : ℝ} (h : e = -r) (hr : r ≠ 0) : e ≠ 0 := h ▸ neg_ne_zero.mpr hr

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

lemma re_of_eq_ofReal {w : ℂ} {r : ℝ} (h : w = (r : ℂ)) : w.re = r := by rw [h, ofReal_re]
lemma im_of_eq_ofReal {w : ℂ} {r : ℝ} (h : w = (r : ℂ)) : w.im = 0 := by rw [h, ofReal_im]
lemma im_sub_of_eq_ofReal {u v : ℂ} {r : ℝ} (hv : v = (r : ℂ)) : (u - v).im = u.im := by simp [hv]

lemma re_star (w : ℂ) : (star w).re = w.re := by simp
lemma im_star (w : ℂ) : (star w).im = -w.im := by simp

lemma re_mul_of_eq_ofReal_left {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c * w).re = r * w.re := by simp [hc]
lemma re_mul_of_eq_ofReal_right {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (w * c).re = w.re * r := by simp [hc]
lemma im_mul_of_eq_ofReal_left {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c * w).im = r * w.im := by simp [hc]
lemma im_mul_of_eq_ofReal_right {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (w * c).im = w.im * r := by simp [hc]

lemma re_neg_mul_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (-(a * b)).re = r * b.im := by simp [ha]
lemma re_neg_mul_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (-(a * b)).re = a.im * r := by simp [hb]
lemma re_neg_left_mul_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (-a * b).re = r * b.im := by simp [ha]
lemma re_neg_left_mul_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (-a * b).re = a.im * r := by simp [hb]
lemma re_mul_neg_right_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (a * -b).re = r * b.im := by simp [ha]
lemma re_mul_neg_right_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (a * -b).re = a.im * r := by simp [hb]
lemma re_mul_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (a * b).re = -(r * b.im) := by simp [ha]
lemma re_mul_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (a * b).re = -(a.im * r) := by simp [hb]
lemma im_mul_of_eq_imag_left {a b : ℂ} {r : ℝ} (ha : a = Complex.mk 0 r) :
    (a * b).im = r * b.re := by simp [ha]
lemma im_mul_of_eq_imag_right {a b : ℂ} {r : ℝ} (hb : b = Complex.mk 0 r) :
    (a * b).im = a.re * r := by simp [hb]

lemma re_div_of_eq_ofReal {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) : (w / c).re = w.re / r := by
  simp [hc]
lemma im_div_of_eq_ofReal {w c : ℂ} {r : ℝ} (hc : c = (r : ℂ)) : (w / c).im = w.im / r := by
  simp [hc]
lemma re_ofReal_div {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c / w).re = r * w.re / normSq w := by simp [hc, div_re]
lemma im_neg_ofReal_div {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (-c / w).im = r * w.im / normSq w := by simp [hc, div_im, neg_div]
lemma im_neg_div_of_eq_ofReal {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (-(c / w)).im = r * w.im / normSq w := by rw [← neg_div, im_neg_ofReal_div hc]
lemma im_ofReal_div_neg {c w : ℂ} {r : ℝ} (hc : c = (r : ℂ)) :
    (c / -w).im = r * w.im / normSq w := by rw [div_neg, im_neg_div_of_eq_ofReal hc]

lemma im_inv_neg (w : ℂ) : (-w)⁻¹.im = w.im / normSq w := by simp [inv_im, neg_div]
lemma im_neg_inv (w : ℂ) : (-w⁻¹).im = w.im / normSq w := by rw [neg_im, inv_im, neg_div, neg_neg]
lemma im_inv_eq_neg (w : ℂ) : w⁻¹.im = -(w.im / normSq w) := by rw [inv_im, neg_div]

lemma normSq_pos_of_ne_zero {w : ℂ} (hw : w ≠ 0) : 0 < normSq w := normSq_pos.mpr hw
lemma normSq_pos_of_re_ne_zero {w : ℂ} (hw : w.re ≠ 0) : 0 < normSq w :=
  normSq_pos.mpr fun h => hw (by simp [h])
lemma normSq_pos_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : 0 < normSq w :=
  normSq_pos.mpr fun h => hw (by simp [h])

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

/-- Run `Positivity.core` on a real expression with standard `ℝ` instances, catching failures. -/
private meta def coreReal (r : Q(ℝ)) : MetaM (RealStrictness r) :=
  catchNone (core q(inferInstance) (some q(inferInstance)) r)

/-- Adapt a `RealStrictness e'` into `Strictness zα e pα?` given `$α =Q ℝ` and `$e =Q $e'`. -/
private meta def adaptRealStrictness {α : Q(Type)} {zα : Q(Zero $α)}
    {pα? : Option Q(PartialOrder $α)} {e : Q($α)} {e' : Q(ℝ)}
    (res : RealStrictness e') (_ : $α =Q ℝ := ⟨⟩) (_ : $e =Q $e' := ⟨⟩) :
    MetaM (Strictness zα e pα?) := do
  assertInstancesCommute
  match h : pα?, res with
  | some pα, .positive pf => assumeInstancesCommute; return h ▸ .positive (pα := pα) q($pf)
  | some pα, .nonnegative pf => assumeInstancesCommute; return h ▸ .nonnegative (pα := pα) q($pf)
  | _, .nonzero pf => return .nonzero q($pf)
  | none, .positive pf => return .nonzero q(ne_of_gt $pf)
  | _, _ => return .none

/-- Transfer strictness along `h : e = rhs` by delegating `rhs` to `Positivity.core`. -/
private meta def evalViaEq {e rhs : Q(ℝ)} (h : Q($e = $rhs)) : MetaM (RealStrictness e) :=
  return match ← coreReal rhs with
  | .positive pf => .positive q(pos_of_eq_real $h $pf)
  | .nonnegative pf => .nonnegative q(nonneg_of_eq_real $h $pf)
  | .nonzero pf => .nonzero q(ne_zero_of_eq_real $h $pf)
  | .none => .none

/-- Prove `e ≠ 0` along `h : e = -rhs` whenever `Positivity.core` proves `rhs ≠ 0`. -/
private meta def evalViaNegEq {e rhs : Q(ℝ)} (h : Q($e = -$rhs)) : MetaM (RealStrictness e) :=
  return match (← coreReal rhs).toNonzero with
  | some pf => .nonzero q(ne_zero_of_eq_neg $h $pf)
  | none => .none

/-- Syntactically recognize complex expressions that are coerced real numbers (including
ring/field operations and powers built solely from real coercions and numerals), returning
`⟨r, pf⟩` with `pf : c = (r : ℂ)`. Does not invoke `Positivity.core`. -/
private meta partial def extractReal? (c : Q(ℂ)) :
    MetaM (Option (Σ r : Q(ℝ), Q($c = ($r : ℂ)))) := do
  match c with
  | ~q(Complex.ofReal $r) => return some ⟨r, q(rfl)⟩
  | ~q(Nat.cast $n) => return some ⟨q(($n : ℝ)), q((Complex.ofReal_natCast $n).symm)⟩
  | ~q(Int.cast $n) => return some ⟨q(($n : ℝ)), q((Complex.ofReal_intCast $n).symm)⟩
  | ~q(Rat.cast $r) => return some ⟨q(($r : ℝ)), q((Complex.ofReal_ratCast $r).symm)⟩
  | ~q(NNRat.cast $r) => return some ⟨q(($r : ℝ)), q((Complex.ofReal_nnratCast $r).symm)⟩
  | ~q(OfNat.ofNat $n (self := _)) =>
    let some n' := n.rawNatLit? | return none
    if n' == 0 then return some ⟨q((0 : ℝ)), (q(Complex.ofReal_zero.symm) :)⟩
    else if n' == 1 then return some ⟨q((1 : ℝ)), (q(Complex.ofReal_one.symm) :)⟩
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
  | ~q(Complex.I) => return some ⟨q((1 : ℝ)), q(eq_imag_I)⟩
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

/-- One-step sign-preserving algebraic reduction of `Complex.re w` to a real expression. -/
private meta def simplifyRe? (w : Q(ℂ)) :
    MetaM (Option (Σ r : Q(ℝ), Q(Complex.re $w = $r))) := do
  if let some ⟨r, hr⟩ ← extractReal? w then
    return some ⟨r, q(re_of_eq_ofReal $hr)⟩
  -- Check `Complex.mk` syntactically so structure eta does not match every `w : ℂ`.
  if w.isAppOfArity ``Complex.mk 2 then
    have a : Q(ℝ) := w.appFn!.appArg!
    have b : Q(ℝ) := w.appArg!
    haveI' : $w =Q Complex.mk $a $b := ⟨⟩
    return some ⟨a, q(rfl)⟩
  match w with
  | ~q(Complex.I) => return some ⟨q((0 : ℝ)), q(Complex.I_re)⟩
  | ~q($a + $b) => return some ⟨q(Complex.re $a + Complex.re $b), q(Complex.add_re $a $b)⟩
  | ~q(conj $a) => return some ⟨q(Complex.re $a), q(Complex.conj_re $a)⟩
  | ~q(Star.star $a) => return some ⟨q(Complex.re $a), q(re_star $a)⟩
  | ~q($a⁻¹) => return some ⟨q(Complex.re $a / Complex.normSq $a), q(Complex.inv_re $a)⟩
  | ~q(@HSMul.hSMul ℝ ℂ ℂ _ $r $v) =>
    return some ⟨q($r * Complex.re $v), q(smul_re_real $r $v)⟩
  | ~q(@HSMul.hSMul ℕ ℂ ℂ _ $n $v) =>
    return some ⟨q(($n : ℝ) * Complex.re $v), q(smul_re_nat $n $v)⟩
  | ~q(@HSMul.hSMul ℤ ℂ ℂ _ $n $v) =>
    return some ⟨q(($n : ℝ) * Complex.re $v), q(smul_re_int $n $v)⟩
  | ~q(@HSMul.hSMul ℚ ℂ ℂ _ $r $v) =>
    return some ⟨q(($r : ℝ) * Complex.re $v), q(smul_re_rat $r $v)⟩
  | ~q(@HSMul.hSMul ℚ≥0 ℂ ℂ _ $r $v) =>
    return some ⟨q(($r : ℝ) * Complex.re $v), q(smul_re_nnrat $r $v)⟩
  | ~q(-($a * $b)) =>
    if let some ⟨r, ha⟩ ← extractImag? a then
      return some ⟨q($r * Complex.im $b), q(re_neg_mul_of_eq_imag_left $ha)⟩
    if let some ⟨r, hb⟩ ← extractImag? b then
      return some ⟨q((Complex.im $a) * $r), q(re_neg_mul_of_eq_imag_right $hb)⟩
    return none
  | ~q($a * $b) =>
    if let some ⟨r, ha⟩ ← extractReal? a then
      return some ⟨q($r * Complex.re $b), q(re_mul_of_eq_ofReal_left $ha)⟩
    if let some ⟨r, hb⟩ ← extractReal? b then
      return some ⟨q((Complex.re $a) * $r), q(re_mul_of_eq_ofReal_right $hb)⟩
    match a with
    | ~q(-$a') =>
      if let some ⟨r, ha⟩ ← extractImag? a' then
        return some ⟨q($r * Complex.im $b), q(re_neg_left_mul_of_eq_imag_left $ha)⟩
      if let some ⟨r, hb⟩ ← extractImag? b then
        return some ⟨q((Complex.im $a') * $r), q(re_neg_left_mul_of_eq_imag_right $hb)⟩
      return none
    | _ =>
      match b with
      | ~q(-$b') =>
        if let some ⟨r, ha⟩ ← extractImag? a then
          return some ⟨q($r * Complex.im $b'), q(re_mul_neg_right_of_eq_imag_left $ha)⟩
        if let some ⟨r, hb⟩ ← extractImag? b' then
          return some ⟨q((Complex.im $a) * $r), q(re_mul_neg_right_of_eq_imag_right $hb)⟩
        return none
      | _ => return none
  | ~q($a / $b) =>
    if let some ⟨r, hb⟩ ← extractReal? b then
      return some ⟨q(Complex.re $a / $r), q(re_div_of_eq_ofReal $hb)⟩
    if let some ⟨r, ha⟩ ← extractReal? a then
      return some ⟨q($r * Complex.re $b / Complex.normSq $b), q(re_ofReal_div $ha)⟩
    return none
  | _ => return none

/-- One-step sign-preserving algebraic reduction of `Complex.im w` to a real expression. -/
private meta def simplifyIm? (w : Q(ℂ)) :
    MetaM (Option (Σ r : Q(ℝ), Q(Complex.im $w = $r))) := do
  if let some ⟨_r, hr⟩ ← extractReal? w then
    return some ⟨q((0 : ℝ)), q(im_of_eq_ofReal $hr)⟩
  -- Check `Complex.mk` syntactically so structure eta does not match every `w : ℂ`.
  if w.isAppOfArity ``Complex.mk 2 then
    have a : Q(ℝ) := w.appFn!.appArg!
    have b : Q(ℝ) := w.appArg!
    haveI' : $w =Q Complex.mk $a $b := ⟨⟩
    return some ⟨b, q(rfl)⟩
  match w with
  | ~q(Complex.I) => return some ⟨q((1 : ℝ)), q(Complex.I_im)⟩
  | ~q($a + $b) => return some ⟨q(Complex.im $a + Complex.im $b), q(Complex.add_im $a $b)⟩
  | ~q($a - $b) =>
    if let some ⟨_r, hb⟩ ← extractReal? b then
      return some ⟨q(Complex.im $a), q(im_sub_of_eq_ofReal $hb)⟩
    return none
  | ~q((-$a)⁻¹) => return some ⟨q(Complex.im $a / Complex.normSq $a), q(im_inv_neg $a)⟩
  | ~q(-$a⁻¹) => return some ⟨q(Complex.im $a / Complex.normSq $a), q(im_neg_inv $a)⟩
  | ~q(-($c / $b)) =>
    if let some ⟨r, hc⟩ ← extractReal? c then
      return some ⟨q($r * Complex.im $b / Complex.normSq $b), q(im_neg_div_of_eq_ofReal $hc)⟩
    return none
  | ~q(@HSMul.hSMul ℝ ℂ ℂ _ $r $v) =>
    return some ⟨q($r * Complex.im $v), q(smul_im_real $r $v)⟩
  | ~q(@HSMul.hSMul ℕ ℂ ℂ _ $n $v) =>
    return some ⟨q(($n : ℝ) * Complex.im $v), q(smul_im_nat $n $v)⟩
  | ~q(@HSMul.hSMul ℤ ℂ ℂ _ $n $v) =>
    return some ⟨q(($n : ℝ) * Complex.im $v), q(smul_im_int $n $v)⟩
  | ~q(@HSMul.hSMul ℚ ℂ ℂ _ $r $v) =>
    return some ⟨q(($r : ℝ) * Complex.im $v), q(smul_im_rat $r $v)⟩
  | ~q(@HSMul.hSMul ℚ≥0 ℂ ℂ _ $r $v) =>
    return some ⟨q(($r : ℝ) * Complex.im $v), q(smul_im_nnrat $r $v)⟩
  | ~q(Complex.I * $v) => return some ⟨q(Complex.re $v), q(Complex.I_mul_im $v)⟩
  | ~q($v * Complex.I) => return some ⟨q(Complex.re $v), q(Complex.mul_I_im $v)⟩
  | ~q($a * $b) =>
    if let some ⟨r, ha⟩ ← extractReal? a then
      return some ⟨q($r * Complex.im $b), q(im_mul_of_eq_ofReal_left $ha)⟩
    if let some ⟨r, hb⟩ ← extractReal? b then
      return some ⟨q((Complex.im $a) * $r), q(im_mul_of_eq_ofReal_right $hb)⟩
    if let some ⟨r, ha⟩ ← extractImag? a then
      return some ⟨q($r * Complex.re $b), q(im_mul_of_eq_imag_left $ha)⟩
    if let some ⟨r, hb⟩ ← extractImag? b then
      return some ⟨q((Complex.re $a) * $r), q(im_mul_of_eq_imag_right $hb)⟩
    return none
  | ~q($a / $b) =>
    if let some ⟨r, hb⟩ ← extractReal? b then
      return some ⟨q(Complex.im $a / $r), q(im_div_of_eq_ofReal $hb)⟩
    match a with
    | ~q(-$c) =>
      if let some ⟨r, hc⟩ ← extractReal? c then
        return some ⟨q($r * Complex.im $b / Complex.normSq $b), q(im_neg_ofReal_div $hc)⟩
      return none
    | _ =>
      match b with
      | ~q(-$d) =>
        if let some ⟨r, ha⟩ ← extractReal? a then
          return some ⟨q($r * Complex.im $d / Complex.normSq $d), q(im_ofReal_div_neg $ha)⟩
        return none
      | _ => return none
  | _ => return none

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
  match pα? with
  | some _ => return .none
  | none =>
    match u, α, e with
    | 0, ~q(ℂ), ~q(Complex.ofReal $r) =>
      assertInstancesCommute
      match (← coreReal r).toNonzero with
      | some pr => return .nonzero q(Complex.ofReal_ne_zero.mpr $pr)
      | none => return .none
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

/-- Extension for the `positivity` tactic: real part `Complex.re w` of a complex expression. -/
@[positivity Complex.re _]
meta def evalComplexRe : PositivityExt where eval {u α} zα pα? e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.re $w) =>
    let res : RealStrictness q(Complex.re $w) ← do
      if let some ⟨r, hr⟩ ← simplifyRe? w then
        evalViaEq (rhs := r) hr
      else
        match w with
        | ~q(-$a) => evalViaNegEq q(Complex.neg_re $a)
        | ~q($a * $b) =>
          if let some ⟨_, ha⟩ ← extractImag? a then
            evalViaNegEq q(re_mul_of_eq_imag_left $ha)
          else if let some ⟨_, hb⟩ ← extractImag? b then
            evalViaNegEq q(re_mul_of_eq_imag_right $hb)
          else
            pure .none
        | _ => pure .none
    adaptRealStrictness (zα := zα) (pα? := pα?) (e := e) res
  | _, _, _ => return .none

/-- Extension for the `positivity` tactic: imaginary part `Complex.im w` of a complex
expression. -/
@[positivity Complex.im _]
meta def evalComplexIm : PositivityExt where eval {u α} zα pα? e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Complex.im $w) =>
    let res : RealStrictness q(Complex.im $w) ← do
      if let some ⟨r, hr⟩ ← simplifyIm? w then
        evalViaEq (rhs := r) hr
      else
        match w with
        | ~q(-$a) => evalViaNegEq q(Complex.neg_im $a)
        | ~q(conj $a) => evalViaNegEq q(Complex.conj_im $a)
        | ~q(Star.star $a) => evalViaNegEq q(im_star $a)
        | ~q($a⁻¹) => evalViaNegEq q(im_inv_eq_neg $a)
        | _ => pure .none
    adaptRealStrictness (zα := zα) (pα? := pα?) (e := e) res
  | _, _, _ => return .none

end Mathlib.Meta.Positivity
