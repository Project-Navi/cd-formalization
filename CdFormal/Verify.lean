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
import CdFormal.Graph.Existence
import CdFormal.Graph.Example

/-!
# Axiom Dashboard

Prints the axioms used by the headline results and the declarations the documentation cites.
Run `lake env lean -DwarningAsError=true CdFormal/Verify.lean`; CI requires one record per
line below, each using only `propext`, `Classical.choice` and `Quot.sound`.

`#print axioms` lists Lean axioms only. Hypotheses are not axioms: the class `PDEInfra` and
the structures `SolutionOperator` and `PrincipalEigendata` appear in the signatures of the
continuum existence theorems, not in this output. The finite-graph theorem takes no such
structure; its hypotheses are stated in its signature.
-/

-- Algebra and real analysis
#print axioms viabilityThreshold
#print axioms spectral_characterization_1d
#print axioms viabilityThreshold_lt_iff
#print axioms scaling_algebraic_contradiction
#print axioms rpow_le_of_mul_rpow_le
#print axioms linfty_bound_algebraic

-- Order theory (Knaster–Tarski)
#print axioms OrderHom.nextFixed_le_of_le
#print axioms monotone_fixed_point_between

-- Definitions and consequences of the `SemioticOperators` and `SemioticContext` fields
#print axioms SemioticContext.a
#print axioms SemioticContext.canonicalViability
#print axioms laplacian_zero
#print axioms laplacian_linear
#print axioms gradNorm_zero
#print axioms zero_solves_equation
#print axioms SemioticContext.a_nonneg
#print axioms SemioticContext.a_le_one
#print axioms SemioticContext.p_sub_one_pos
#print axioms scaling_uniqueness

-- Continuum existence, conditional on `PDEInfra` and `SolutionOperator`
#print axioms IsWeakCoherentConfiguration
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration

-- Finite-graph existence (no assumed analysis)
#print axioms SemioticGraph.a
#print axioms SemioticGraph.laplacian
#print axioms SemioticGraph.gradNorm
#print axioms SemioticGraph.gradNorm_nonneg
#print axioms SemioticGraph.gradNorm_smul
#print axioms SemioticGraph.gradNorm_const
#print axioms SemioticGraph.IsSolution
#print axioms SemioticGraph.interiorGraph
#print axioms SemioticGraph.energy
#print axioms SemioticGraph.unitSphere
#print axioms SemioticGraph.principalEigenvalue
#print axioms SemioticGraph.principalEigenvalue_mul_le
#print axioms SemioticGraph.principalEigenvalue_le_of_laplacian_eq
#print axioms SemioticGraph.principalEigenvalue_neg
#print axioms SemioticGraph.exists_pos_eigenvector
#print axioms SemioticGraph.fixedPointMap
#print axioms SemioticGraph.isSolution_of_fixedPointMap_eq
#print axioms SemioticGraph.fixedPointMap_eq_iff_isSolution
#print axioms SemioticGraph.fixedPointMap_mono
#print axioms SemioticGraph.exists_isSolution_between
#print axioms SemioticGraph.smul_subsolution
#print axioms SemioticGraph.plateau_supersolution
#print axioms SemioticGraph.exists_pos_graph
#print axioms SemioticGraph.exists_pos_graph_of_unweighted
#print axioms SemioticGraph.triangle
#print axioms SemioticGraph.exists_pos_triangle
