/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f0fbf24b-2ea8-4b5d-869f-cd4fade87407

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem OrderHom.nextFixed_le_of_le
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    (f.nextFixed sub h_sub : α) ≤ super

- theorem monotone_fixed_point_between
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    ∃ x : α, f x = x ∧ sub ≤ x ∧ x ≤ super
-/

/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Order.FixedPoints


set_option relaxedAutoImplicit false

set_option autoImplicit false

universe u

variable {α : Type u} [CompleteLattice α] (f : α →o α)

theorem OrderHom.nextFixed_le_of_le
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    (f.nextFixed sub h_sub : α) ≤ super :=
  by
    -- By induction on $n$, we can show that $f^n(super) \leq super$ for all $n$.
    have h_iter_le_super : ∀ n : ℕ, (f^[n]) super ≤ super := by
      exact fun n => Nat.recOn n ( by simpa ) fun n ih => by simpa only [ Function.iterate_succ_apply' ] using le_trans ( f.monotone ih ) h_super;
    apply le_trans (sInf_le _) (h_iter_le_super 0);
    aesop

theorem monotone_fixed_point_between
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    ∃ x : α, f x = x ∧ sub ≤ x ∧ x ≤ super :=
  by
    -- Let $x$ be the greatest fixed point of $f$ in the interval $[sub, super]$.
    obtain ⟨x, hx⟩ : ∃ x, f x = x ∧ sub ≤ x ∧ x ≤ super := by
      have h_least_upper_bound : ∃ x, f x = x ∧ sub ≤ x ∧ x ≤ super := by
        have h_least_upper_bound : ∃ x, f x ≤ x ∧ sub ≤ x ∧ x ≤ super := by
          exact ⟨ super, h_super, h_le, le_rfl ⟩
        -- By the Knaster-Tarski theorem, since $f$ is monotone and we have a pre-fixed point $x$, there exists a least fixed point $y$ such that $sub \leq y \leq x$.
        obtain ⟨y, hy₁, hy₂⟩ : ∃ y, f y = y ∧ sub ≤ y ∧ y ≤ h_least_upper_bound.choose := by
          have h_least_upper_bound : ∃ y, f y = y ∧ sub ≤ y ∧ y ≤ h_least_upper_bound.choose := by
            have h_least_upper_bound : ∃ y, f y ≤ y ∧ sub ≤ y ∧ y ≤ h_least_upper_bound.choose ∧ ∀ z, f z ≤ z ∧ sub ≤ z ∧ z ≤ h_least_upper_bound.choose → y ≤ z := by
              use sInf { z | f z ≤ z ∧ sub ≤ z ∧ z ≤ h_least_upper_bound.choose };
              refine' ⟨ _, _, _, fun z hz => sInf_le hz ⟩;
              · refine' le_sInf fun z hz => _;
                exact le_trans ( f.monotone ( sInf_le hz ) ) hz.1;
              · exact le_sInf fun z hz => hz.2.1;
              · exact sInf_le ⟨ h_least_upper_bound.choose_spec.1, h_least_upper_bound.choose_spec.2.1, le_rfl ⟩
            obtain ⟨ y, hy₁, hy₂, hy₃, hy₄ ⟩ := h_least_upper_bound
            have hy₅ : f y = y := by
              contrapose! hy₄;
              use f y;
              exact ⟨ ⟨ f.monotone hy₁, h_sub.trans ( f.monotone hy₂ ), hy₁.trans hy₃ ⟩, fun h => hy₄ <| le_antisymm hy₁ h ⟩
            use y, hy₅, hy₂, hy₃;
          exact h_least_upper_bound;
        exact ⟨ y, hy₁, hy₂.1, hy₂.2.trans h_least_upper_bound.choose_spec.2.2 ⟩
      exact h_least_upper_bound;
    use x
