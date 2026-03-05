import CdFormal.Theorems

/-!
# Axiom Contamination Checks

Verification dashboard: run `lake build CdFormal.Verify` to confirm which axioms
each theorem depends on. If `sorryAx` appears anywhere, something is broken.

Pure algebra theorems should show only `[propext, Classical.choice, Quot.sound]`.
PDE-dependent theorems should additionally show `PDEInfra` fields but no `sorryAx`.
-/

-- Pure algebra (NO sorryAx, NO PDE axioms)
#print axioms spectral_characterization_1d
#print axioms scaling_algebraic_contradiction

-- PDE-dependent (should show PDEInfra fields, but NO sorryAx)
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration

-- Definitions (should be axiom-free)
#print axioms IsWeakCoherentConfiguration
#print axioms viabilityThreshold
