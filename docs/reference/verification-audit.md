# Verification Audit

Machine-verified correspondence between the paper and the Lean formalization. Last updated against Lean 4 v4.28.0, Mathlib v4.28.0.

---

## Paper-to-Lean alignment

| Paper result | Lean declaration | Status |
|-------------|-----------------|--------|
| Definition 2.1 (Semiotic Manifold) | `SemioticManifold` | Verified definition |
| Definition 2.2 (Coefficients) | `SemioticContext` | Verified definition |
| Definition 3.1 (BVP V1') | `SemioticBVP` | Verified definition |
| Definition 3.1 (Creative drive) | `SemioticContext.a` | Verified definition |
| Definition 3.3 (Canonical viability) | `SemioticContext.canonicalViability` | Verified definition |
| Section 3.2 (Weak coherent configuration) | `IsWeakCoherentConfiguration` | Verified definition |
| Definition 3.13 (Principal eigenvalue) | `PrincipalEigendata` | Verified structure |
| Lemma 3.7 (Compactness of T) | `PDEInfra.T_compact` | **Axiom** |
| Lemma 3.10 (L∞ bound, analytic) | `PDEInfra.linfty_bound` | **Axiom** |
| Lemma 3.10 (L∞ bound, algebraic) | `linfty_bound_algebraic` | **Proved** |
| Lemma 3.11 (\(C^{1,\alpha}\) bound) | --- | Not formalized |
| Theorem 3.12 (Existence) | `SemioticBVP.exists_isWeakCoherentConfiguration` | **Proved** (conditional on `PDEInfra`) |
| Theorem 3.16 (Nontriviality) | `SemioticBVP.exists_pos_isWeakCoherentConfiguration` | **Proved** (conditional on `PDEInfra`) |
| Section 3.4 (Spectral, 1D) | `spectral_characterization_1d` | **Proved** (pure algebra) |
| Open Problem #3 (Uniqueness) | `scaling_uniqueness` | **Proved** (proportional-class; full uniqueness open) |
| Knaster-Tarski core | `monotone_fixed_point_between` | **Proved** (pure order theory) |

---

## Axiom dependency dashboard

Run `lake build CdFormal.Verify` to reproduce. The output of `#print axioms` for each declaration:

### Pure algebra --- no domain axioms

| Declaration | Axioms |
|------------|--------|
| `viabilityThreshold` | `[propext, Quot.sound]` |
| `spectral_characterization_1d` | `[propext, Classical.choice, Quot.sound]` |
| `scaling_algebraic_contradiction` | `[propext, Classical.choice, Quot.sound]` |

### Operator lemmas --- from SemioticOperators

| Declaration | Axioms |
|------------|--------|
| `laplacian_zero` | `[propext, Classical.choice, Quot.sound]` |
| `laplacian_linear` | `[propext, Classical.choice, Quot.sound]` |
| `gradNorm_zero` | `[propext, Classical.choice, Quot.sound]` |

### Scaling uniqueness --- from SemioticOperators + SemioticContext

| Declaration | Axioms |
|------------|--------|
| `scaling_uniqueness` | `[propext, Classical.choice, Quot.sound]` |

### Coefficient bounds --- from SemioticContext

| Declaration | Axioms |
|------------|--------|
| `SemioticContext.a_nonneg` | `[propext, Classical.choice, Quot.sound]` |
| `SemioticContext.a_le_one` | `[propext, Classical.choice, Quot.sound]` |
| `SemioticContext.p_sub_one_pos` | `[propext, Classical.choice, Quot.sound]` |

### L∞ bound algebraic core --- pure real analysis

| Declaration | Axioms |
|------------|--------|
| `rpow_le_of_mul_rpow_le` | `[propext, Classical.choice, Quot.sound]` |
| `linfty_bound_algebraic` | `[propext, Classical.choice, Quot.sound]` |

### Monotone fixed point --- pure order theory

| Declaration | Axioms |
|------------|--------|
| `OrderHom.nextFixed_le_of_le` | `[propext, Quot.sound]` |
| `monotone_fixed_point_between` | `[propext, Quot.sound]` |

!!! note "No Classical.choice"
    The monotone fixed-point theorems use only `[propext, Quot.sound]`, making them candidates for **constructive** upstream contribution to Mathlib.

### PDE-level existence --- from PDEInfra

| Declaration | Axioms |
|------------|--------|
| `SemioticBVP.exists_isWeakCoherentConfiguration` | `[propext, Classical.choice, Quot.sound]` + `PDEInfra` fields |
| `SemioticBVP.exists_pos_isWeakCoherentConfiguration` | `[propext, Classical.choice, Quot.sound]` + `PDEInfra` fields |

!!! warning "No sorryAx"
    If `sorryAx` appears in any output above, the proof is **incomplete**. This is checked automatically in CI.

### Definitions --- axiom-free

| Declaration | Axioms |
|------------|--------|
| `IsWeakCoherentConfiguration` | `[propext, Quot.sound]` |

---

## Machine-checked definitions

### SemioticManifold (Definition 2.1)

A compact, connected, smooth Riemannian manifold --- the space of possible meanings.

```lean
class SemioticManifold (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M] where
  riemannianMetric : Bundle.RiemannianMetric
    (fun (_ : M) ↦ EuclideanSpace ℝ (Fin n))
```

### SemioticContext (Definitions 2.2, 3.1)

The coefficient fields with explicit bounds:

- Care \(\kappa : M \to [0,1]\)
- Coherence \(\gamma : M \to [0,1]\)
- Contradiction \(\mu : M \to [0,1]\)
- Viability potential \(b : M \to \mathbb{R}\)
- Carrying capacity \(c : M \to \mathbb{R}\) with \(c(x) \geq c_0 > 0\)
- Saturation exponent \(p > 1\)

### SemioticBVP (Definition 3.1, V1')

The boundary value problem encoding:

\[
-\Delta\Phi(x) = a(x)\,|\nabla\Phi(x)| + b(x)\,\Phi(x) - c(x)\,(\max(\Phi(x), 0))^p
\]

with \(\Phi = 0\) on \(\partial M\). The positive part \(\Phi_+ = \max(\Phi, 0)\) follows the operator formulation in Paper Section 3.2.

### IsWeakCoherentConfiguration (Section 3.2)

A weak coherent configuration is simply a function \(\Phi : M \to \mathbb{R}\) satisfying both the PDE and the boundary condition:

```lean
def IsWeakCoherentConfiguration (bvp : SemioticBVP n M) (Φ : M → ℝ) : Prop :=
  bvp.equation Φ ∧ bvp.boundary_condition Φ
```

---

## Aristotle prover artifacts

Results originally proved by the [Aristotle](https://harmonic.fun) theorem prover, integrated into the main build after manual adaptation for Lean 4.28.0:

| Artifact | Aristotle ID | Status |
|----------|-------------|--------|
| L∞ bound algebraic core | `224a0625` | Proved and integrated (`LinftyAlgebraic.lean`) |
| Scaling uniqueness | `1c3414f4`, `60ec288c` | Proved and integrated (`ScalingUniqueness.lean`) |
| Operator lemmas | `41cee644` | Partially proved; `gradNorm_const` added as axiom |

---

## Known limitations

1. **Boundary encoding.** `SemioticBVP.boundary` is an unstructured `Set M` with no requirement that it equals the topological boundary. Encoding manifold-with-boundary requires infrastructure not yet in Mathlib.

2. **Lemma 3.11 not formalized.** The \(C^{1,\alpha}\) interpolation bound requires H&ouml;lder space types.

3. **Full uniqueness open.** `scaling_uniqueness` proves uniqueness within the class of proportional rescalings only. Full uniqueness (Paper Open Problem #3) would require comparison principles not available in Mathlib.
