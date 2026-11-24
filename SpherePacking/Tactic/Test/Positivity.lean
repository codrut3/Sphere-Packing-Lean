/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.Positivity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Basic

/-!
# Tests for `Complex` and `UpperHalfPlane` `positivity` extensions
-/

@[expose] public section

open Complex Real
open UpperHalfPlane hiding I
open ComplexConjugate

section real_part

example {t : ℝ} (ht : 0 < t) : 0 < (t : ℂ).re := by positivity
example {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (t : ℂ).re := by positivity
example {t : ℝ} (ht : t ≠ 0) : (t : ℂ).re ≠ 0 := by positivity
example {t : ℝ} : 0 < ((t ^ 2 + 1 : ℝ) : ℂ).re := by positivity
example {t : ℝ} : 0 < ((t : ℂ) ^ 2 + 1).re := by positivity
example (n : ℕ) : 0 ≤ (n : ℂ).re := by positivity
example (n : ℕ) : 0 < ((n : ℂ) + 1).re := by positivity
example {q : ℚ} (hq : 0 < q) : 0 < (q : ℂ).re := by positivity
example : 0 < (2 : ℂ).re := by positivity
example : 0 ≤ (0 : ℂ).re := by positivity
example : 0 ≤ I.re := by positivity
example (x : ℝ) : 0 < (Complex.exp (x : ℂ)).re := by positivity
example {a b : ℝ} (ha : 0 < a) : 0 < (Complex.mk a b).re := by positivity
example {w : ℂ} (hw : 0 < w.re) : 0 < (conj w).re := by positivity
example {w : ℂ} (hw : 0 < w.re) : 0 < (star w).re := by positivity
example {w : ℂ} (hw : 0 < w.re) : 0 < w⁻¹.re := by positivity
example {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ w⁻¹.re := by positivity
example {w : ℂ} (hw : w.re ≠ 0) : w⁻¹.re ≠ 0 := by positivity
example {w : ℂ} (hw : w.re ≠ 0) : (-w).re ≠ 0 := by positivity
example {z : ℍ} : 0 < (-(I * (z : ℂ))).re := by positivity
example {z : ℍ} : 0 < (-(2 * π * I * (z : ℂ))).re := by positivity
example {z : ℍ} (n : ℕ) : 0 < (-(2 * π * I * ((n + 1 : ℕ) : ℂ) * (z : ℂ))).re := by positivity
example {r : ℝ} {w : ℂ} (hr : 0 < r) (hw : 0 < w.re) : 0 < (r • w).re := by positivity
example {w : ℂ} {t : ℝ} (hw : 0 < w.re) (ht : 0 < t) : 0 < (w / (t : ℂ)).re := by positivity
example {w : ℂ} {t : ℝ} (hw : 0 < w.re) (ht : 0 < t) : 0 < ((t : ℂ) / w).re := by positivity
example {w : ℂ} (hw : 0 < w.re) : 0 < (1 / w).re := by positivity

end real_part

section imag_part

-- Imaginary-axis upper half-plane point constructions (42+ sites in SpherePacking)
example {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ)).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < ((t : ℂ) * I).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 ≤ (I * (t : ℂ)).im := by positivity
example {t : ℝ} (ht : t ≠ 0) : (I * (t : ℂ)).im ≠ 0 := by positivity
example : 0 < I.im := by positivity
example {t : ℝ} : 0 ≤ (t : ℂ).im := by positivity
example (n : ℕ) : 0 ≤ (n : ℂ).im := by positivity
example (x : ℝ) : 0 ≤ (Complex.exp (x : ℂ)).im := by positivity

-- Compound real factors & recursion
example {t : ℝ} (ht : 0 < t) : 0 < (I * ((1 / t : ℝ) : ℂ)).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < (I / (t : ℂ)).im := by positivity
example {t : ℝ} : 0 < (I * ((t ^ 2 + 1 : ℝ) : ℂ)).im := by positivity
example {t : ℝ} (ht : 1 ≤ t) : 0 < (I * (t : ℂ)).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < (2 * π * I * (t : ℂ)).im := by positivity
example {r : ℝ} {z : ℍ} (hr : 0 < r) : 0 < (r • (z : ℂ)).im := by positivity
example {n : ℕ} {z : ℍ} (hn : 0 < n) : 0 < (n • (z : ℂ)).im := by positivity

-- IntegralParametrisations shapes: `I * t ± 1`, `z + 1`, `z - 1`
example {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ) + 1).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < (I * (t : ℂ) - 1).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < (-1 + I * (t : ℂ)).im := by positivity
example (z : ℍ) : 0 < ((z : ℂ) + 1).im := by positivity
example (z : ℍ) : 0 < ((z : ℂ) - 1).im := by positivity
example (z w : ℍ) : 0 < ((z : ℂ) + (w : ℂ)).im := by positivity

-- Inversion and Möbius `-c / w` on the upper half-plane
example (z : ℍ) : 0 < (-(z : ℂ))⁻¹.im := by positivity
example (z : ℍ) : 0 < (-(z : ℂ)⁻¹).im := by positivity
example (z : ℍ) : 0 < (-1 / (z : ℂ)).im := by positivity
example (z : ℍ) : 0 < (-(1 / (z : ℂ))).im := by positivity
example (z : ℍ) : 0 < (1 / -(z : ℂ)).im := by positivity
example (z : ℍ) : 0 < (-1 / ((z : ℂ) + 1)).im := by positivity
example (t : ℝ) : 0 < (-1 / ((t : ℂ) + I)).im := by positivity
example (t : ℝ) : 0 < (-1 / (-(t : ℂ) + I)).im := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < (-1 / (I * (t : ℂ))).im := by positivity
example (z : ℍ) : 0 < (z : ℂ).im := by positivity
example {t : ℝ} (ht : 0 < t) : (⟨I * (t : ℂ), by positivity⟩ : ℍ).im = t := by simp

end imag_part

section nonzero_and_normSq

-- Without `open scoped ComplexOrder`, `ℂ` has no `PartialOrder`; these still succeed!
example : (I : ℂ) ≠ 0 := by positivity
example (z : ℍ) : (z : ℂ) ≠ 0 := by positivity
example (w : ℂ) : Complex.exp w ≠ 0 := by positivity
example {t : ℝ} (ht : 0 < t) : (t : ℂ) ≠ 0 := by positivity
example (z : ℍ) : (π : ℂ) * I * (z : ℂ) ≠ 0 := by positivity
example : (2 : ℂ) * (π : ℂ) * I ≠ 0 := by positivity
example : (1 : ℂ) ≠ 0 := by positivity
example (a : ℂ) : a / (2 * (π : ℂ) * I) * (2 * (π : ℂ) * I) = a := by field_simp
example (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (z : ℍ) :
    UpperHalfPlane.denom γ (z : ℂ) ≠ 0 := by positivity

-- `Complex.normSq`
example (w : ℂ) : 0 ≤ Complex.normSq w := by positivity
example (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by positivity
example : 0 < Complex.normSq I := by positivity
example (z : ℍ) : 0 < Complex.normSq ((z : ℂ) + 1) := by positivity
example {t : ℝ} (ht : 0 < t) : 0 < Complex.normSq (I * (t : ℂ) - 1) := by positivity

-- `field_simp` automatically discharges `UpperHalfPlane.denom`, `π`, `I`, `(z : ℂ)`
example (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (z : ℍ) (a b : ℂ)
    (h : a / UpperHalfPlane.denom γ (z : ℂ) = b) :
    a = UpperHalfPlane.denom γ (z : ℂ) * b := by
  field_simp at h
  exact h

example (z : ℍ) (a : ℂ) : a / ((π : ℂ) * I * (z : ℂ)) * ((π : ℂ) * I * (z : ℂ)) = a := by
  field_simp

end nonzero_and_normSq

section negative_tests

-- Must fail cleanly when no positivity fact holds
example (t : ℝ) (h : False) : 0 < (I * (t : ℂ)).im := by
  fail_if_success positivity
  exact h.elim

example (h : False) : 0 < (I * I).im := by
  fail_if_success positivity
  exact h.elim

example (t : ℝ) (h : False) : 0 < (t : ℂ).im := by
  fail_if_success positivity
  exact h.elim

example (w : ℂ) (h : False) : 0 < Complex.normSq w := by
  fail_if_success positivity
  exact h.elim

example (h : False) : (0 : ℂ) ≠ 0 := by
  fail_if_success positivity
  exact h.elim

end negative_tests

section axioms_check

theorem test_ax_im {t : ℝ} (ht : 0 < t) : 0 < (2 * π * I * (t : ℂ) - 1).im := by
  positivity

theorem test_ax_denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (z : ℍ) :
    UpperHalfPlane.denom γ (z : ℂ) ≠ 0 := by
  positivity

/--
info: 'test_ax_im' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test_ax_im

/--
info: 'test_ax_denom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms test_ax_denom

end axioms_check
