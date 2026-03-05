/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Theorems

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

-- § PDEInfra-dependent (paper-specific)
-- Should show PDEInfra fields but NO sorryAx.
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration

-- § Definitions (axiom-free)
#print axioms IsWeakCoherentConfiguration
