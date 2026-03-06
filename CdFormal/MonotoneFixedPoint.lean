/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Order.FixedPoints

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Monotone Fixed Point Between Sub and Super-Fixed Points

A proved consequence of the Knaster-Tarski theorem: if `f` is a monotone
self-map on a complete lattice, and there exist `sub ≤ f sub` (sub-fixed point)
and `f super ≤ super` (super-fixed point) with `sub ≤ super`, then `f` has
a fixed point `x` with `sub ≤ x ∧ x ≤ super`.

This is the order-theoretic skeleton of the sub/super-solution method
(Amann 1976) used in nonlinear elliptic PDE theory. The PDE content
(monotonicity of T, construction of sub/super-solutions, nontriviality)
remains axiomatic in `PDEInfra`.

## Main statements

- `OrderHom.nextFixed_le_of_le` — `nextFixed sub ≤ super` when `sub ≤ super`
  and `f super ≤ super`
- `monotone_fixed_point_between` — existence of a fixed point between
  sub and super-fixed points

## References

- [Knaster1928] B. Knaster, "Un théorème sur les fonctions d'ensembles," 1928.
- [Tarski1955] A. Tarski, "A lattice-theoretical fixpoint theorem," 1955.
- [Amann1976] H. Amann, "Fixed point equations and nonlinear eigenvalue
  problems in ordered Banach spaces," 1976.
-/

universe u

variable {α : Type u} [CompleteLattice α] (f : α →o α)

/-- The least fixed point above a sub-fixed point is below any super-fixed
    point that dominates it. This bridges `nextFixed` and `prevFixed`.

    Proof: `nextFixed sub` is `lfp` of `(const sub ⊔ f)`. Since
    `(const sub ⊔ f)(super) = sub ⊔ f(super) ≤ sub ⊔ super = super`,
    `super` is a pre-fixed point, so `lfp ≤ super`. -/
theorem OrderHom.nextFixed_le_of_le
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    (f.nextFixed sub h_sub : α) ≤ super :=
  OrderHom.lfp_le _ (sup_le h_le h_super)

/-- **Monotone fixed point between sub and super-fixed points.**

    If `f : α →o α` is monotone on a complete lattice, `sub ≤ f sub`,
    `f super ≤ super`, and `sub ≤ super`, then there exists a fixed point
    `x` with `sub ≤ x ∧ x ≤ super`.

    This is the order-theoretic core of the sub/super-solution method.
    The fixed point is `nextFixed sub`, the least fixed point ≥ sub. -/
theorem monotone_fixed_point_between
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    ∃ x : α, f x = x ∧ sub ≤ x ∧ x ≤ super :=
  let fp := f.nextFixed sub h_sub
  ⟨fp, fp.2, f.le_nextFixed h_sub, f.nextFixed_le_of_le h_sub h_super h_le⟩
