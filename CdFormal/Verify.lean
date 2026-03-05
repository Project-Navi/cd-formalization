/-
Axiom contamination checks.

Run `lake build CdFormal.Verify` to confirm which axioms each theorem depends on.

Expected:
  - spectral_characterization_1d: [propext, Classical.choice, Quot.sound] (pure algebra)
  - scaling_algebraic_contradiction: same (pure algebra)
  - SemioticBVP.exists_isWeakCoherentConfiguration: above + PdeInfra fields (no sorryAx)
  - SemioticBVP.exists_pos_isWeakCoherentConfiguration: above + PdeInfra fields (no sorryAx)

If `sorryAx` appears anywhere, something is broken.
-/

import CdFormal.Theorems

-- Pure algebra (NO sorryAx, NO PDE axioms)
#print axioms spectral_characterization_1d
#print axioms scaling_algebraic_contradiction

-- PDE-dependent (should show PdeInfra fields, but NO sorryAx)
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration

-- Definitions (should be axiom-free)
#print axioms IsWeakCoherentConfiguration
#print axioms viabilityThreshold
