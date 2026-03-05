/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8654be8c-4d83-4367-a089-c0d6e124a201

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (β : ℝ)
    (hL : L > 0) (hb : b > 0) :
    let β_star
-/

-- Hint: This is an algebraic inequality. If β > (π/L)²/b, then βb > (π/L)², so (π/L)² - βb < 0. Use field_simp and nlinarith or linarith after clearing denominators.
import Mathlib


theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (β : ℝ)
    (hL : L > 0) (hb : b > 0) :
    let β_star := (Real.pi / L) ^ 2 / b
    β > β_star → (Real.pi / L) ^ 2 - β * b < 0 := by
  -- By definition of β_star, if β > β_star, then β * b > (Real.pi / L) ^ 2.
  intro β_star hβ
  have h_mul : β * b > (Real.pi / L) ^ 2 := by
    rwa [ gt_iff_lt, div_lt_iff₀ hb ] at hβ;
  grind
