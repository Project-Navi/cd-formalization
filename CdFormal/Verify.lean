/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Theorems
import CdFormal.OperatorLemmas
import CdFormal.CoefficientLemmas
import CdFormal.ScalingUniqueness
import CdFormal.MonotoneFixedPoint
import CdFormal.LinftyAlgebraic

/-!
# Axiom Dependency Map

Run `lake build CdFormal.Verify` to confirm axiom dependencies.
If `sorryAx` appears anywhere, the proof is incomplete.

## Categories

- **Pure algebra**: Only `[propext, Classical.choice, Quot.sound]`.
  These are upstream candidates (see per-theorem annotations).
- **PDEInfra-dependent**: Additionally shows `PDEInfra` fields.
  Paper-specific — not upstream candidates.
- **Definitions**: Should be axiom-free beyond `[propext, Quot.sound]`.
-/

-- § Pure algebra (upstream candidates)
-- No PDEInfra axioms. Depend only on core Lean axioms.
#print axioms viabilityThreshold
#print axioms spectral_characterization_1d
#print axioms scaling_algebraic_contradiction

-- § Derived operator lemmas (from SemioticOperators axioms)
#print axioms laplacian_zero
#print axioms laplacian_linear
#print axioms gradNorm_zero

-- § Scaling uniqueness (from SemioticOperators + SemioticContext)
#print axioms scaling_uniqueness

-- § Coefficient bound lemmas (from SemioticContext bounds)
#print axioms SemioticContext.a_nonneg
#print axioms SemioticContext.a_le_one
#print axioms SemioticContext.p_sub_one_pos

-- § L∞ bound algebraic core (pure real analysis)
#print axioms rpow_le_of_mul_rpow_le
#print axioms linfty_bound_algebraic

-- § Monotone fixed point (from Knaster-Tarski, pure order theory)
#print axioms OrderHom.nextFixed_le_of_le
#print axioms monotone_fixed_point_between

-- § PDEInfra-dependent (paper-specific)
-- Should show PDEInfra fields but NO sorryAx.
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration

-- § Definitions (axiom-free)
#print axioms IsWeakCoherentConfiguration
