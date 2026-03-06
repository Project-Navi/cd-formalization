/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Bornology.Hom
import Mathlib.Topology.Separation.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bornology Bridge: T_compact ↔ LocallyBoundedMap

Validates that the `T_compact` predicate (used in `PDEInfra`) is equivalent
to Aaron Lin's `LocallyBoundedMap` typing between `vonNBornology` and
`Bornology.relativelyCompact`.

## Main statements

- `compact_image_iff_relativelyCompact_isBounded` — `IsCompact (closure (f '' S))`
  iff `S` is bounded in `Bornology.relativelyCompact`
- `T_compact_toLocallyBoundedMap` — construct a `LocallyBoundedMap` from `T_compact`

## References

- Suggested by Yongxi Lin (Aaron) on Lean Zulip.
-/

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [ContinuousSMul ℝ X] [R0Space X]

/-- Our `IsCompact (closure (f '' S))` formulation is equivalent to
    `@IsBounded _ (relativelyCompact X) (f '' S)`. -/
theorem compact_image_iff_relativelyCompact_isBounded
    (f : X → X) (S : Set X) :
    IsCompact (closure (f '' S)) ↔
    @Bornology.IsBounded _ (Bornology.relativelyCompact X) (f '' S) :=
  sorry

/-- Construct a `LocallyBoundedMap` from `vonNBornology` to `relativelyCompact`
    given the `T_compact` predicate. -/
def T_compact_toLocallyBoundedMap
    (f : X → X)
    (hf : ∀ S : Set X, Bornology.IsVonNBounded ℝ S →
      IsCompact (closure (f '' S))) :
    @LocallyBoundedMap X X
      (Bornology.vonNBornology ℝ X)
      (Bornology.relativelyCompact X) :=
  sorry
