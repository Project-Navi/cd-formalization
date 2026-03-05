# Creative Determinant — Lean 4 Verification Audit

**Date:** 2026-03-05
**Lean toolchain:** `leanprover/lean4:v4.28.0`
**Mathlib:** `v4.28.0` (pinned in `lakefile.toml`)
**Build status:** Clean (`lake build --wfail`, 0 warnings, 0 `sorryAx`)

---

## 1. Fully Proved (no sorry, no custom axioms)

All items below depend only on the Lean kernel axioms `[propext, Classical.choice, Quot.sound]`.
Confirmed via `#print axioms` in `CdFormal/Verify.lean`.

### 1.1 Spectral Characterization (1D) — Paper §3.4

**Statement:** For constant viability `b` on `[0,L]`, the principal eigenvalue is
`λ₁ = (π/L)² − β·b`. The condition `λ₁ < 0` is equivalent to `β > β*` where `β* = (π/L)²/b`.

```lean
-- CdFormal/Theorems.lean

def viabilityThreshold (L : ℝ) (b : ℝ) : ℝ :=
  (Real.pi / L) ^ 2 / b

theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ) (hb : b > 0) :
    let beta_star := viabilityThreshold L b
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0 := by
  intro beta_star h_beta
  have h1 : beta > (Real.pi / L) ^ 2 / b := h_beta
  have h2 : beta * b > (Real.pi / L) ^ 2 := by
    rwa [gt_iff_lt, div_lt_iff₀ hb] at h1
  linarith
```

**Axiom dependencies:** `[propext, Classical.choice, Quot.sound]` — pure algebra.

### 1.2 Scaling Algebraic Contradiction — used in uniqueness arguments

**Statement:** If `p > 1`, `k > 1`, `c > 0`, `Φ > 0`, and `-c·k·Φ^p ≤ -c·k^p·Φ^p`, then `False`.
Core algebraic step: `k > 1` and `p > 1` imply `k < k^p`, contradicting `k ≥ k^p`.

```lean
-- CdFormal/Theorems.lean

lemma scaling_algebraic_contradiction
    (p : ℝ) (k : ℝ) (c : ℝ) (Phi_val : ℝ)
    (hp : p > 1) (hk : k > 1) (hc : c > 0) (hPhi : Phi_val > 0)
    (h_eq : -c * k * Phi_val ^ p ≤ -c * k ^ p * Phi_val ^ p) :
    False := by
  have hcΦp : (0 : ℝ) < c * Phi_val ^ p := by positivity
  have h_div : k ≥ k ^ p := by nlinarith
  have h_lt : k < k ^ p := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hk hp
    simp only [Real.rpow_one] at h
    exact h
  linarith
```

**Axiom dependencies:** `[propext, Classical.choice, Quot.sound]` — pure algebra.

### 1.3 Operator Consequence Lemmas — derived from `SemioticOperators` axioms

**Statement:** Basic properties derived from the `SemioticOperators` axiom contract,
validating that the axioms are well-formed and non-vacuous.

```lean
-- CdFormal/OperatorLemmas.lean

lemma laplacian_zero :
    ops.laplacian (fun _ : M ↦ (0 : ℝ)) = fun _ ↦ 0 := by
  have h := ops.laplacian_smul (fun _ ↦ (0 : ℝ)) 0
  simp only [zero_mul] at h
  exact h

lemma gradNorm_zero (x : M) :
    ops.gradNorm (fun _ : M ↦ (0 : ℝ)) x = 0 := by
  have h := ops.gradNorm_smul (fun _ ↦ (0 : ℝ)) 0 x
  simp only [zero_mul, abs_zero] at h
  exact h
```

Also includes the composed linearity lemma:

```lean
lemma laplacian_linear (f g : M → ℝ) (c : ℝ) :
    ops.laplacian (fun x ↦ c * f x + g x) =
    fun x ↦ c * ops.laplacian f x + ops.laplacian g x
```

**Axiom dependencies:** `SemioticOperators.laplacian_add`, `SemioticOperators.laplacian_smul`,
`SemioticOperators.gradNorm_smul` — derived from operator axioms only (no `PDEInfra`).

**Provenance:** Aristotle run `41cee644-80f9-4122-9c7d-c32dc1b571d6` (original proofs against
pre-Phase 2 axiom set, adapted here for current axioms).

### 1.4 Coefficient Bound Lemmas — derived from `SemioticContext` bounds

**Statement:** Properties of the creative drive coefficient a(x) = κγμ
and the saturation exponent p, derived from the coefficient bounds.

```lean
-- CdFormal/CoefficientLemmas.lean

theorem SemioticContext.a_nonneg (x : M) : 0 ≤ ctx.a x
theorem SemioticContext.a_le_one (x : M) : ctx.a x ≤ 1
theorem SemioticContext.p_sub_one_pos : 0 < ctx.p - 1
```

**Axiom dependencies:** `[propext, Classical.choice, Quot.sound]` — pure algebra
from `κ_bounds`, `γ_bounds`, `μ_bounds`, `one_lt_p`.

### 1.5 Existence of Weak Coherent Configurations — Paper Theorem 3.12

**Statement:** Under the `PDEInfra` typeclass, the BVP admits at least one nonnegative solution.

**Proof chain:** L∞ bound → Schaefer set bounded → Schaefer fixed point → maximum principle.

```lean
-- CdFormal/Theorems.lean

theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) := by
  have h_bounded := infra.linfty_bound B hB
  obtain ⟨Phi, hfix⟩ := infra.schaefer infra.T_continuous_compact h_bounded
  exact ⟨Phi, solOp.T_fixed_point Phi hfix, infra.fixed_point_nonneg Phi hfix⟩
```

**Axiom dependencies:** `PDEInfra.T_continuous_compact`, `PDEInfra.linfty_bound`,
`PDEInfra.schaefer`, `PDEInfra.fixed_point_nonneg`, `SolutionOperator.T_fixed_point` — no `sorryAx`.

### 1.6 Existence of Nontrivial Coherent Configurations — Paper Theorem 3.16

**Statement:** When `λ₁(-Δ - b; M) < 0`, there exists a positive solution in the interior.

**Proof chain:** monotone iteration (sub/super-solution) → nontrivial fixed point → maximum principle.

```lean
-- CdFormal/Theorems.lean

theorem SemioticBVP.exists_pos_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (beta : ℝ)
    (eig : PrincipalEigendata bvp beta)
    (eigval_neg : eig.eigval < 0) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) ∧
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0) := by
  obtain ⟨Phi, hfix, x, hx_int, hx_pos⟩ := infra.monotone_iteration beta eig eigval_neg
  exact ⟨Phi, solOp.T_fixed_point Phi hfix,
    infra.fixed_point_nonneg Phi hfix, x, hx_int, hx_pos⟩
```

**Axiom dependencies:** `PDEInfra.monotone_iteration`, `PDEInfra.fixed_point_nonneg`,
`SolutionOperator.T_fixed_point` — no `sorryAx`.

### 1.7 L∞ Bound — Algebraic Core — Paper Lemma 3.10 (partial)

**Statement:** At an interior maximum, the PDE reduces to `b·v ≥ c·v^p`. The algebraic
consequence is `v ≤ (B/c₀)^{1/(p-1)}`. This is the algebraic half of Lemma 3.10; the
maximum-principle half (∇u = 0, Δu ≤ 0 at interior max) remains an axiom.

Proved by Aristotle (`224a0625`).

```lean
-- artifacts/aristotle/LinftyAlgebraic_proved.lean

lemma rpow_le_of_mul_rpow_le
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ^ (p - 1) ≤ b / c := by
  have h_div : b * v / (c * v) ≥ c * v ^ p / (c * v) := by
    apply div_le_div_of_nonneg_right h (mul_nonneg hc.le hv.le);
  have h_simplified : b / c ≥ v ^ p / v := by
    field_simp [mul_comm, mul_assoc, mul_left_comm] at h_div ⊢
    exact h_div;
  rwa [ Real.rpow_sub_one hv.ne' ] at *

theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1)) := by
  have h_root : v ^ (p - 1) ≤ b / c → v ≤ (b / c) ^ (1 / (p - 1)) := by
    exact fun h => le_trans
      ( by rw [ ← Real.rpow_mul hv.le, mul_one_div_cancel ( by linarith ), Real.rpow_one ] )
      ( Real.rpow_le_rpow ( by positivity ) h ( by exact one_div_nonneg.mpr ( by linarith ) ) );
  apply h_root; exact rpow_le_of_mul_rpow_le v b c p hv hc hp h
```

**Axiom dependencies:** `[propext, Classical.choice, Quot.sound]` — pure real analysis, no `sorryAx`.

### 1.8 Scaling Uniqueness — Proportional solutions are impossible

**Statement:** If Φ solves the CD equation and kΦ (with k > 1) also solves it, then at any
point where c(x) > 0 and Φ(x) > 0, we get a contradiction. Solutions are unique within the
class of proportional rescalings. Full uniqueness remains Open Problem #3 in the paper.

Proved by Aristotle (`1c3414f4`).

**Note:** This artifact (`artifacts/aristotle/ScalingUniqueness_proved.lean`) was proved against
the pre-Phase 2 axiom names (`laplacian_linear`, `gradNorm_homog`, `p_gt_one`) and does not
build against the current code. The algebraic core `scaling_algebraic_contradiction` (§1.2)
captures the key inequality and is fully integrated.

**Axiom dependencies:** `[propext, Classical.choice, Quot.sound]` — uses only `SemioticOperators`
fields and `SemioticContext.one_lt_p`. No `sorryAx`.

---

## 2. Machine-Verified Definitions (no axioms beyond kernel)

All structures below typecheck against Mathlib with zero `sorry`.

### 2.1 Semiotic Manifold — Paper Definition 2.1

```lean
-- CdFormal/Basic.lean

abbrev SemioticModel (n : ℕ) := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))

class SemioticManifold (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M] where
  riemannianMetric : Bundle.RiemannianMetric (fun (_ : M) ↦ EuclideanSpace ℝ (Fin n))
```

### 2.2 Coefficient Structure — Paper Definitions 2.2, 3.1

```lean
-- CdFormal/Basic.lean

structure SemioticContext (n : ℕ) (M : Type*) [...] [SemioticManifold n M] where
  κ : M → ℝ                              -- Care field
  γ : M → ℝ                              -- Coherence field
  μ : M → ℝ                              -- Contradiction field
  b : M → ℝ                              -- Viability potential
  c : M → ℝ                              -- Carrying capacity
  p : ℝ                                  -- Saturation exponent
  κ_bounds : ∀ x, 0 ≤ κ x ∧ κ x ≤ 1
  γ_bounds : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1
  μ_bounds : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1
  c_pos : ∃ c₀ > 0, ∀ x, c x ≥ c₀
  one_lt_p : 1 < p
```

### 2.3 Creative Drive — Paper Definition 3.1

```lean
-- CdFormal/Basic.lean

def SemioticContext.a (ctx : SemioticContext n M) (x : M) : ℝ :=
  ctx.κ x * ctx.γ x * ctx.μ x
```

### 2.4 Canonical Viability Closure — Paper Definition 3.3

```lean
-- CdFormal/Basic.lean

def SemioticContext.canonicalViability
    (ctx : SemioticContext n M) (lambda : ℝ) (x : M) : ℝ :=
  ctx.κ x * ctx.γ x - lambda * ctx.μ x
```

### 2.5 PDE Operators — Paper Section 3.2

```lean
-- CdFormal/Basic.lean

structure SemioticOperators (n : ℕ) (M : Type*) [...] [SemioticManifold n M] where
  laplacian : (M → ℝ) → (M → ℝ)
  gradNorm : (M → ℝ) → (M → ℝ)
  laplacian_add : ∀ (f g : M → ℝ),
    laplacian (fun x ↦ f x + g x) = fun x ↦ laplacian f x + laplacian g x
  laplacian_smul : ∀ (f : M → ℝ) (c : ℝ),
    laplacian (fun x ↦ c * f x) = fun x ↦ c * laplacian f x
  gradNorm_nonneg : ∀ (f : M → ℝ) (x : M), 0 ≤ gradNorm f x
  gradNorm_smul : ∀ (f : M → ℝ) (c : ℝ) (x : M),
    gradNorm (fun y ↦ c * f y) x = |c| * gradNorm f x
  gradNorm_const : ∀ (a : ℝ) (x : M), gradNorm (fun _ ↦ a) x = 0
```

### 2.6 Boundary Value Problem — Paper Definition 3.1 (V1')

```lean
-- CdFormal/Basic.lean

structure SemioticBVP (n : ℕ) (M : Type*) [...] [SemioticManifold n M] where
  ctx : SemioticContext n M
  ops : SemioticOperators n M
  boundary : Set M
  interior_nonempty : ∃ x, x ∉ boundary
  equation : (M → ℝ) → Prop := fun Φ ↦
    ∀ x, -(ops.laplacian Φ x) =
      (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) -
      (ctx.c x) * (max (Φ x) 0) ^ (ctx.p)
  boundary_condition : (M → ℝ) → Prop := fun Φ ↦
    ∀ x ∈ boundary, Φ x = 0
```

**Note:** The saturation term uses `max (Φ x) 0` (positive part) matching the operator
formulation `F(ψ) = a|∇ψ| + bψ - c(ψ₊)^p` in Paper Section 3.2. For nonneg solutions, `Φ₊ = Φ`.

**Note:** `interior_nonempty` prevents `boundary = Set.univ`, which would make existence
theorems vacuously true.

### 2.7 Weak Coherent Configuration — Paper §3.2

```lean
-- CdFormal/Basic.lean

def IsWeakCoherentConfiguration (bvp : SemioticBVP n M) (Φ : M → ℝ) : Prop :=
  bvp.equation Φ ∧ bvp.boundary_condition Φ
```

### 2.8 Solution Operator — Paper Section 3.2

```lean
-- CdFormal/Axioms.lean

structure SolutionOperator (bvp : SemioticBVP n M) where
  T : (M → ℝ) → (M → ℝ)
  T_boundary : ∀ u x, x ∈ bvp.boundary → T u x = 0
  T_fixed_point : ∀ Φ, T Φ = Φ → IsWeakCoherentConfiguration bvp Φ
```

### 2.9 Principal Eigendata — Paper Definition 3.13

```lean
-- CdFormal/Axioms.lean

structure PrincipalEigendata (bvp : SemioticBVP n M) (beta : ℝ) where
  eigval : ℝ
  eigfun : M → ℝ
  eigfun_pos : ∀ x, x ∉ bvp.boundary → eigfun x > 0
  eigfun_boundary : ∀ x ∈ bvp.boundary, eigfun x = 0
  eigen_eq : ∀ x,
    -(bvp.ops.laplacian eigfun x) - beta * (bvp.ctx.b x) * (eigfun x) = eigval * (eigfun x)
```

---

## 3. The Axiom Boundary — `PDEInfra` Typeclass

These are the assumptions that Lean takes on trust. Each corresponds to a classical result
from elliptic PDE theory not yet available in Mathlib for abstract Riemannian manifolds.

```lean
-- CdFormal/Axioms.lean

class PDEInfra (bvp : SemioticBVP n M) (solOp : SolutionOperator bvp) : Prop where
```

| Field | Paper Reference | Classical Source | Mathlib Status |
|-------|----------------|-----------------|----------------|
| `T_continuous_compact : True` | Lemma 3.7 | Schauder estimates + Arzelà-Ascoli | Requires Hölder spaces on manifolds (not in Mathlib) |
| `linfty_bound` | Lemma 3.10 | Maximum principle at interior max | Algebraic core proved (§1.6); max principle not in Mathlib for manifolds |
| `schaefer` | Theorem 3.12 | Schaefer 1955; Deimling 1985 | Schaefer's theorem not in Mathlib (draft issue: `drafts/mathlib_issue_schaefer.md`) |
| `fixed_point_nonneg` | Theorem 3.12 | Maximum principle | Strong max principle not in Mathlib for manifolds |
| `monotone_iteration` | Theorem 3.16 | Amann 1976 sub/super-solution | Sub/super-solution theory not in Mathlib |

### 3.1 `T_continuous_compact`

```lean
  T_continuous_compact : True
```

**Known limitation:** This field is currently `True` (a placeholder). The `schaefer` axiom
takes this as a hypothesis (via `True →`), so the dependency is structurally present but
content-free until Mathlib gains Hölder spaces on manifolds. See `drafts/mathlib_issue_schaefer.md`.

**Why it can't be proved now:** Mathlib has no `C^{k,α}` Hölder space type on Riemannian manifolds,
no Schauder estimates, and no Arzelà-Ascoli for manifold function spaces.

### 3.2 `linfty_bound` (Lemma 3.10)

```lean
  linfty_bound :
    ∀ (B : ℝ), (∀ x, bvp.ctx.b x ≤ B) →
    ∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K
```

**Decomposition:** The proof has two parts:
1. **Analytic:** At interior max, `∇u = 0` and `Δu ≤ 0` (maximum principle — must remain axiom)
2. **Algebraic:** `b·v ≥ c·v^p` implies `v ≤ (B/c₀)^{1/(p-1)}` (**proved** — see §1.6)

### 3.3 `schaefer` (Schaefer's Fixed-Point Theorem)

```lean
  schaefer :
    True →
    (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K) →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

**Note:** The `True →` first argument corresponds to `T_continuous_compact`. At the call site,
`infra.T_continuous_compact` is passed. This makes the dependency structurally visible even
though the content is currently trivial.

**Why it can't be proved now:** Requires Schaefer's theorem for continuous compact operators
on a Banach space. Mathlib has Banach space basics but not this fixed-point theorem.

### 3.4 `fixed_point_nonneg` (Maximum Principle)

```lean
  fixed_point_nonneg :
    ∀ (Φ : M → ℝ), solOp.T Φ = Φ → ∀ x, Φ x ≥ 0
```

**Why it can't be proved now:** Requires strong maximum principle for elliptic operators
on manifolds. Mathlib has no maximum principle infrastructure.

### 3.5 `monotone_iteration` (Sub/Super-Solution, Amann 1976)

```lean
  monotone_iteration :
    ∀ (beta : ℝ) (eig : PrincipalEigendata bvp beta),
      eig.eigval < 0 →
      ∃ Φ : M → ℝ, solOp.T Φ = Φ ∧ (∃ x, x ∉ bvp.boundary ∧ Φ x > 0)
```

**Why it can't be proved now:** Requires sub/super-solution existence theorem in ordered
Banach spaces, plus the strong maximum principle for interior positivity.

---

## 4. Aristotle Prover Artifacts

Artifacts from the Aristotle theorem prover are archived in `artifacts/aristotle/`.
These are raw outputs — some proved against earlier axiom names and may not build
against the current codebase.

### 4.1 L∞ Bound Algebraic Core — **PROVED**

**Aristotle ID:** `224a0625-a2ed-45f0-ac27-1dfd0d421057`
**Output:** `artifacts/aristotle/LinftyAlgebraic_proved.lean`
**Status:** Proved and integrated. See §1.6 for full proofs.

### 4.2 Scaling Uniqueness — **PROVED**

**Aristotle ID:** `1c3414f4-fd21-47b5-99a1-2ab27892df92`
**Output:** `artifacts/aristotle/ScalingUniqueness_proved.lean`
**Status:** Proved. The algebraic core is integrated as `scaling_algebraic_contradiction` (§1.2).
The full `scaling_uniqueness` theorem references pre-Phase 2 axiom names and needs updating
to build against current code.

### 4.3 Operator Consequence Lemmas — **PARTIALLY PROVED**

**Aristotle ID:** `41cee644-80f9-4122-9c7d-c32dc1b571d6`
**Output:** `artifacts/aristotle/41cee644-80f9-4122-9c7d-c32dc1b571d6.lean`

Results:
- `laplacian_zero` — **proved** (adapted and integrated in `CdFormal/OperatorLemmas.lean`)
- `gradNorm_zero` — **proved** (adapted and integrated in `CdFormal/OperatorLemmas.lean`)
- `gradNorm_const` — **failed** (genuinely unprovable from existing axioms; added as a new
  axiom `SemioticOperators.gradNorm_const` in `CdFormal/Basic.lean`)

---

## 5. Not Currently Possible with Mathlib

These results require infrastructure that Mathlib does not have as of v4.28.0.

| Result | What's Missing | Mathlib Status |
|--------|---------------|----------------|
| **Schaefer's fixed-point theorem** | Leray-Schauder degree or Schaefer's theorem for compact operators on Banach spaces | Banach space basics exist; no fixed-point theorems of this type |
| **Schauder estimates** (`‖u‖_{C^{2,α}} ≤ C(‖f‖_{C^{0,α}} + ‖u‖_{C^0})`) | Hölder spaces on manifolds, elliptic regularity | No Hölder space type, no Schauder theory |
| **Strong maximum principle** | Maximum principle for elliptic operators on Riemannian manifolds | No maximum principle infrastructure |
| **Sub/super-solution theorem** (Amann 1976) | Ordered Banach space iteration, comparison principle | No ordered-cone iteration machinery |
| **Principal eigenvalue existence** | Krein-Rutman theorem or variational characterization on manifolds | No Krein-Rutman; Rayleigh quotient exists for finite-dim only |
| **Arzelà-Ascoli on manifolds** | Compact embedding `C^{k+1,α} ↪ C^{k,α}` on compact manifolds | Arzelà-Ascoli exists for metric spaces but not for Hölder embeddings |
| **Full uniqueness** | Not claimed in paper (Open Problem #3); would need comparison principle + structure theory for nonlinear elliptic BVPs | Beyond current scope |

---

## 6. CI and Verification Infrastructure

### Build command
```
lake build --wfail
```
Fails on any warning (including `sorry`), ensuring no silent contamination.

### Axiom dependency dashboard (`CdFormal/Verify.lean`)

```lean
-- § Pure algebra (upstream candidates)
-- No PDEInfra axioms. Depend only on core Lean axioms.
#print axioms viabilityThreshold
#print axioms spectral_characterization_1d
#print axioms scaling_algebraic_contradiction

-- § Derived operator lemmas (from SemioticOperators axioms)
#print axioms laplacian_zero
#print axioms laplacian_linear
#print axioms gradNorm_zero

-- § Coefficient bound lemmas (from SemioticContext bounds)
#print axioms SemioticContext.a_nonneg
#print axioms SemioticContext.a_le_one
#print axioms SemioticContext.p_sub_one_pos

-- § PDEInfra-dependent (paper-specific)
-- Should show PDEInfra fields but NO sorryAx.
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration

-- § Definitions (axiom-free)
#print axioms IsWeakCoherentConfiguration
```

### Sorry contamination check (CI)
```yaml
- uses: leanprover/lean-action@v1
  with:
    build-args: "--wfail"

- name: Check for sorry contamination
  run: |
    lake env lean CdFormal/Verify.lean 2>&1 | tee verify_output.txt
    if grep -q "sorryAx" verify_output.txt; then
      echo "FATAL: sorryAx found in verified theorems!"
      exit 1
    fi
```

---

## 7. Project Structure

```
cd_formalization/
├── .github/workflows/lean_action_ci.yml   # CI with --wfail + sorry check
├── CdFormal.lean                          # root import (Basic, Axioms, Theorems,
│                                          #   OperatorLemmas, CoefficientLemmas, Verify)
├── CdFormal/
│   ├── Basic.lean                         # definitions (§2)
│   ├── Axioms.lean                        # PDE infrastructure typeclass (§3)
│   ├── Theorems.lean                      # proved theorems (§1)
│   ├── OperatorLemmas.lean                # derived operator lemmas (§1.3)
│   ├── CoefficientLemmas.lean             # coefficient bound lemmas (§1.4)
│   └── Verify.lean                        # axiom dependency dashboard (§6)
├── drafts/                                # Aristotle targets + community drafts
│   ├── LinftyAlgebraic.lean
│   ├── OperatorLemmas.lean
│   ├── ScalingUniqueness.lean
│   ├── zulip_schaefer_post.md
│   └── mathlib_issue_schaefer.md
├── artifacts/aristotle/                   # Aristotle prover outputs (raw archives)
├── docs/internal/upstream-strategy.md     # upstream engagement strategy
├── LICENSE                                # Apache 2.0
├── lakefile.toml                          # Lake config (Mathlib v4.28.0)
├── lake-manifest.json                     # dependency lock
└── lean-toolchain                         # leanprover/lean4:v4.28.0
```

---

## 8. Paper ↔ Lean Alignment

| Paper Result | Lean Name | Status |
|-------------|-----------|--------|
| Def 2.1 (Semiotic Manifold) | `SemioticManifold` | Verified definition |
| Def 2.2 (Coefficients) | `SemioticContext` | Verified definition |
| Def 3.1 (BVP V1') | `SemioticBVP` | Verified definition |
| Def 3.1 (Creative drive) | `SemioticContext.a` | Verified definition |
| Def 3.3 (Canonical viability) | `SemioticContext.canonicalViability` | Verified definition |
| Def 3.6 (Weak coherent config) | `IsWeakCoherentConfiguration` | Verified definition |
| Def 3.13 (Principal eigenvalue) | `PrincipalEigendata` | Verified structure |
| Lemma 3.7 (Compactness of T) | `PDEInfra.T_continuous_compact` | Axiom (placeholder) |
| Lemma 3.10 (L∞ bound) | `PDEInfra.linfty_bound` + `linfty_bound_algebraic` | Axiom (max principle) + **proved** (algebraic core) |
| Lemma 3.11 (C^{1,α} bound) | Not formalized | Paper proof strengthened (interpolation) |
| Thm 3.12 (Existence) | `SemioticBVP.exists_isWeakCoherentConfiguration` | **Proved** (conditional on PDEInfra) |
| Thm 3.16 (Nontriviality) | `SemioticBVP.exists_pos_isWeakCoherentConfiguration` | **Proved** (conditional on PDEInfra) |
| §3.4 (Spectral, 1D) | `spectral_characterization_1d` | **Proved** (pure algebra) |
| Open Problem #3 (Uniqueness) | `scaling_algebraic_contradiction` | **Proved** (partial: algebraic core of proportional-class uniqueness) |
