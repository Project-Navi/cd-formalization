/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 41cee644-80f9-4122-9c7d-c32dc1b571d6

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma laplacian_zero
- lemma laplacian_smul (now an axiom after Phase 2 refactor)
- lemma gradNorm_zero

The following was NOT proved (genuinely unprovable from current axioms):

- lemma gradNorm_const — added as axiom to SemioticOperators
-/

-- NOTE: This file preserves the original Aristotle output against the
-- PRE-Phase 2 axiom set (laplacian_linear, gradNorm_homog).
-- The adapted versions of the proved lemmas are in CdFormal/OperatorLemmas.lean.

import CdFormal.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]
  (ops : SemioticOperators n M)

-- Original Aristotle proofs (against old axiom names)
-- These do NOT build against current axioms; see CdFormal/OperatorLemmas.lean for adapted versions.

/-
lemma laplacian_zero :
    ops.laplacian (fun _ : M => (0 : ℝ)) = fun _ => 0 := by
  convert ops.laplacian_linear ( fun _ => 0 ) ( fun _ => 0 ) ( -1 ) using 1 <;> aesop;

lemma laplacian_smul (c : ℝ) (f : M → ℝ) :
    ops.laplacian (fun x => c * f x) = fun x => c * ops.laplacian f x := by
  by_contra h_nonlinear;
  obtain ⟨x, hx⟩ : ∃ x : M, ops.laplacian (fun x_1 => c * f x_1) x ≠ c * ops.laplacian f x := by
    exact Function.ne_iff.mp h_nonlinear;
  have := ops.laplacian_linear f ( fun _ => 0 ) ( c ) ; simp_all +decide [ funext_iff ] ;
  exact hx ( by simpa using congr_fun ( laplacian_zero ops ) x )

lemma gradNorm_zero (x : M) :
    ops.gradNorm (fun _ : M => (0 : ℝ)) x = 0 := by
  simpa using ops.gradNorm_homog 0 0 x

-- Aristotle failed to find a proof (genuinely unprovable from axioms).
lemma gradNorm_const (a : ℝ) (x : M) :
    ops.gradNorm (fun _ : M => a) x = 0 := by
  sorry
-/

end
