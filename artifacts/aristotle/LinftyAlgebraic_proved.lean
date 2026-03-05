/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 224a0625-a2ed-45f0-ac27-1dfd0d421057

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma rpow_le_of_mul_rpow_le
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ^ (p - 1) ≤ b / c

- theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1))
-/

/-
L∞ Bound — Algebraic Core (Paper Lemma 3.10)

At an interior maximum of a solution Φ, the maximum principle gives
∇Φ = 0 and ΔΦ ≤ 0, so the PDE reduces to:
  0 ≤ b·Φ - c·Φ^p

The algebraic consequence is Φ ≤ (B/c₀)^{1/(p-1)}.

This file proves that algebraic step. The maximum principle
argument ("at interior max, ∇Φ = 0 and ΔΦ ≤ 0") remains an axiom
in PdeInfra.

Target: Aristotle piecewise proof.
-/

import Mathlib


set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

/-! ## Step 1: From the PDE inequality to a power bound

If b·v ≥ c·v^p with v > 0, c > 0, p > 1, divide both sides
by c·v to get v^{p-1} ≤ b/c. -/

lemma rpow_le_of_mul_rpow_le
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ^ (p - 1) ≤ b / c := by
  -- Divide both sides of the inequality $b * v \geq c * v^p$ by $c * v$ to get $v^{p-1} \leq b / c$.
  have h_div : b * v / (c * v) ≥ c * v ^ p / (c * v) := by
    -- Since $c * v > 0$, dividing both sides of the inequality $b * v \geq c * v^p$ by $c * v$ preserves the inequality.
    apply div_le_div_of_nonneg_right h (mul_nonneg hc.le hv.le);
  -- Simplify the divided inequality to get $v^{p-1} \leq b / c$.
  have h_simplified : b / c ≥ v ^ p / v := by
    -- Cancel out the common terms in the numerator and denominator.
    field_simp [mul_comm, mul_assoc, mul_left_comm] at h_div ⊢
    exact h_div;
  rwa [ Real.rpow_sub_one hv.ne' ] at *

/-! ## Step 2: From the power bound to the L∞ bound

If v^{p-1} ≤ b/c, take the (p-1)-th root to get v ≤ (b/c)^{1/(p-1)}.
Uses monotonicity of rpow with positive exponent. -/

theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1)) := by
  -- Applying the lemma that if $a \leq b$ and both are positive, then $a^{1/(p-1)} \leq b^{1/(p-1)}$.
  have h_root : v ^ (p - 1) ≤ b / c → v ≤ (b / c) ^ (1 / (p - 1)) := by
    exact fun h => le_trans ( by rw [ ← Real.rpow_mul hv.le, mul_one_div_cancel ( by linarith ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) h ( by exact one_div_nonneg.mpr ( by linarith ) ) );
  -- Apply the lemma h_root with the hypothesis h to conclude the proof.
  apply h_root; exact rpow_le_of_mul_rpow_le v b c p hv hc hp h

end