/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import SpherePacking.Tactic.Positivity.Complex
public import SpherePacking.Tactic.Positivity.UpperHalfPlane

/-!
# `positivity` extensions for `Complex` and `UpperHalfPlane`

Convenience umbrella module importing both layers:

* `SpherePacking.Tactic.Positivity.Complex` — core `Complex` extensions (depends only on
  `Mathlib.Basic.Complex.Basic` and `Mathlib.Tactic.Positivity.Core`);
* `SpherePacking.Tactic.Positivity.UpperHalfPlane` — `UpperHalfPlane` and `Complex.exp`
  extensions (upstreamable separately to `Mathlib.Analysis.Complex.UpperHalfPlane` and
  `Mathlib.Analysis.Complex.Exponential`).
-/
