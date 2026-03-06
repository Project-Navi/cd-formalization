/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
# L∞ Bound — Algebraic Core (Paper Lemma 3.10)

At an interior maximum of a solution Φ, the maximum principle gives
∇Φ = 0 and ΔΦ ≤ 0, so the PDE reduces to `b·v ≥ c·v^p`.

The algebraic consequence is `v ≤ (B/c₀)^{1/(p-1)}`. This file proves
that algebraic step. The maximum-principle argument ("at interior max,
∇Φ = 0 and ΔΦ ≤ 0") remains an axiom in `PDEInfra.linfty_bound`.

Together these decompose Paper Lemma 3.10 into:
- **Axiom** (maximum principle): the PDE inequality `b·v ≥ c·v^p` holds
  at an interior maximum
- **Proved** (this file): `b·v ≥ c·v^p` implies `v ≤ (b/c)^{1/(p-1)}`

## Main statements

- `rpow_le_of_mul_rpow_le` — from `b·v ≥ c·v^p` to `v^{p-1} ≤ b/c`
- `linfty_bound_algebraic` — from `b·v ≥ c·v^p` to `v ≤ (b/c)^{1/(p-1)}`

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026, Lemma 3.10.
- [GilbargTrudinger2001] D. Gilbarg and N.S. Trudinger,
  *Elliptic PDEs of Second Order*, Ch. 3.
-/

/-- From the PDE inequality `b·v ≥ c·v^p` at an interior max, divide
    by `c·v` to get `v^{p-1} ≤ b/c`.

    Provenance: Aristotle run `224a0625`. -/
lemma rpow_le_of_mul_rpow_le
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (_hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ^ (p - 1) ≤ b / c := by
  have h_div : b * v / (c * v) ≥ c * v ^ p / (c * v) :=
    div_le_div_of_nonneg_right h (mul_nonneg hc.le hv.le)
  have h_simplified : b / c ≥ v ^ p / v := by
    field_simp [mul_comm, mul_assoc, mul_left_comm] at h_div ⊢
    exact h_div
  rwa [Real.rpow_sub_one hv.ne'] at *

/-- From `b·v ≥ c·v^p` conclude `v ≤ (b/c)^{1/(p-1)}` by taking the
    `(p-1)`-th root. This is the algebraic core of Paper Lemma 3.10.

    Provenance: Aristotle run `224a0625`. -/
theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1)) := by
  have h_root : v ^ (p - 1) ≤ b / c → v ≤ (b / c) ^ (1 / (p - 1)) :=
    fun h ↦ le_trans
      (by rw [← Real.rpow_mul hv.le, mul_one_div_cancel (by linarith), Real.rpow_one])
      (Real.rpow_le_rpow (by positivity) h (one_div_nonneg.mpr (by linarith)))
  exact h_root (rpow_le_of_mul_rpow_le v b c p hv hc hp h)

end
