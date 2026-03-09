# Theorem Catalog

All 15 proved results in the Creative Determinant formalization, organized by dependency tier. Every theorem compiles with zero `sorry` under `lake build --wfail`.

---

## Tier 1 --- Pure Algebra

These depend only on Lean kernel axioms: `propext`, `Classical.choice`, `Quot.sound`.

### Spectral characterization (1D)

**Paper:** Section 3.4

For constant viability \(b > 0\) on \([0, L]\), the principal eigenvalue is \(\lambda_1 = (\pi/L)^2 - \beta b\). The viability threshold is:

\[
\beta^* = \frac{(\pi/L)^2}{b}
\]

When \(\beta > \beta^*\), we have \(\lambda_1 < 0\) --- the spectral condition for nontrivial solutions.

```lean
def viabilityThreshold (L : ℝ) (b : ℝ) : ℝ :=
  (Real.pi / L) ^ 2 / b

theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ) (hb : b > 0) :
    let beta_star := viabilityThreshold L b
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0
```

**File:** `CdFormal/Theorems.lean`

---

### Scaling algebraic contradiction

**Paper:** Used in uniqueness arguments

If \(p > 1\) and \(k > 1\), then \(k < k^p\) (via `Real.self_lt_rpow_of_one_lt`). Combined with the hypothesis \(-c \cdot k \cdot \Phi^p \leq -c \cdot k^p \cdot \Phi^p\), this yields `False`.

```lean
lemma scaling_algebraic_contradiction
    (p : ℝ) (k : ℝ) (c : ℝ) (Phi_val : ℝ)
    (hp : p > 1) (hk : k > 1) (hc : c > 0) (hPhi : Phi_val > 0)
    (h_eq : -c * k * Phi_val ^ p ≤ -c * k ^ p * Phi_val ^ p) :
    False
```

**File:** `CdFormal/Theorems.lean`

---

## Tier 2 --- Real Analysis

Pure real analysis with no domain-specific axioms. Upstream candidates for Mathlib.

### v^(p−1) ≤ b/c from PDE inequality

**Paper:** Lemma 3.10 (algebraic step)

From the PDE inequality at an interior maximum, \(b \cdot v \geq c \cdot v^p\). Dividing by \(c \cdot v > 0\):

\[
v^{p-1} \leq \frac{b}{c}
\]

```lean
lemma rpow_le_of_mul_rpow_le
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0)
    (h : b * v ≥ c * v ^ p) :
    v ^ (p - 1) ≤ b / c
```

**File:** `CdFormal/LinftyAlgebraic.lean` --- **Provenance:** Aristotle run `224a0625`

---

### L∞ bound algebraic core

**Paper:** Lemma 3.10 (algebraic core)

Taking the \((p-1)\)-th root of the previous result:

\[
v \leq \left(\frac{b}{c}\right)^{1/(p-1)}
\]

```lean
theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1))
```

**File:** `CdFormal/LinftyAlgebraic.lean` --- **Provenance:** Aristotle run `224a0625`

---

## Tier 3 --- Order Theory

These depend only on `propext` and `Quot.sound` --- **no `Classical.choice`** --- making them candidates for constructive upstream contribution.

### nextFixed ≤ super-fixed point

**Paper:** Order-theoretic core of Amann (1976)

The least fixed point above a sub-fixed point is below any super-fixed point that dominates it.

**Proof:** `nextFixed sub` is `lfp` of `(const sub ⊔ f)`. Since `(const sub ⊔ f)(super) = sub ⊔ f(super) ≤ sub ⊔ super = super`, the element `super` is a pre-fixed point, so `lfp ≤ super` by `OrderHom.lfp_le`.

```lean
theorem OrderHom.nextFixed_le_of_le
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    (f.nextFixed sub h_sub : α) ≤ super
```

**File:** `CdFormal/MonotoneFixedPoint.lean`

---

### Monotone fixed point between sub/super

**Paper:** Order-theoretic skeleton of the sub/super-solution method

If \(f : \alpha \to \alpha\) is monotone on a complete lattice, \(\text{sub} \leq f(\text{sub})\), \(f(\text{super}) \leq \text{super}\), and \(\text{sub} \leq \text{super}\), then \(f\) has a fixed point \(x\) with:

\[
\text{sub} \leq x \leq \text{super}
\]

```lean
theorem monotone_fixed_point_between
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    ∃ x : α, f x = x ∧ sub ≤ x ∧ x ≤ super
```

**File:** `CdFormal/MonotoneFixedPoint.lean`

---

## Tier 4 --- Operator Lemmas

Derived from `SemioticOperators` axioms (linearity, homogeneity, constant gradient).

### Laplacian of zero

\(\Delta(0) = 0\), from `laplacian_smul` with \(c = 0\).

```lean
@[simp]
lemma laplacian_zero :
    ops.laplacian (fun _ : M ↦ (0 : ℝ)) = fun _ ↦ 0
```

**File:** `CdFormal/OperatorLemmas.lean`

---

### Laplacian linearity

\(\Delta(c \cdot f + g) = c \cdot \Delta f + \Delta g\), composed from `laplacian_add` and `laplacian_smul`.

```lean
lemma laplacian_linear (f g : M → ℝ) (c : ℝ) :
    ops.laplacian (fun x ↦ c * f x + g x) =
    fun x ↦ c * ops.laplacian f x + ops.laplacian g x
```

**File:** `CdFormal/OperatorLemmas.lean`

---

### Gradient norm of zero

\(\|\nabla 0\| = 0\), from `gradNorm_const` with \(a = 0\).

```lean
@[simp]
lemma gradNorm_zero (x : M) :
    ops.gradNorm (fun _ : M ↦ (0 : ℝ)) x = 0
```

**File:** `CdFormal/OperatorLemmas.lean`

---

## Tier 5 --- Coefficient Bounds

Derived from `SemioticContext` field constraints (\(\kappa, \gamma, \mu \in [0,1]\), \(p > 1\)).

### Creative drive is nonnegative

\(a(x) = \kappa(x) \cdot \gamma(x) \cdot \mu(x) \geq 0\), since each factor lies in \([0,1]\).

```lean
theorem SemioticContext.a_nonneg (x : M) : 0 ≤ ctx.a x
```

**File:** `CdFormal/CoefficientLemmas.lean`

---

### Creative drive is bounded

\(a(x) = \kappa(x) \cdot \gamma(x) \cdot \mu(x) \leq 1\), since each factor lies in \([0,1]\).

```lean
theorem SemioticContext.a_le_one (x : M) : ctx.a x ≤ 1
```

**File:** `CdFormal/CoefficientLemmas.lean`

---

### Saturation exponent gap

\(p - 1 > 0\), directly from the `one_lt_p` field.

```lean
theorem SemioticContext.p_sub_one_pos : 0 < ctx.p - 1
```

**File:** `CdFormal/CoefficientLemmas.lean`

---

## Tier 6 --- PDE-Level Results

These compose `PDEInfra` axioms. All axiom dependencies are visible via `[PDEInfra bvp solOp]`.

### Existence of weak coherent configurations (Theorem 3.12)

**Paper:** Theorem 3.12

The BVP admits at least one nonnegative solution \(\Phi \geq 0\).

**Proof chain:** L∞ bound \(\to\) Schaefer set bounded \(\to\) Schaefer fixed point \(\to\) maximum principle.

```lean
theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0)
```

**Axiom dependencies:** `T_compact`, `linfty_bound`, `schaefer`, `fixed_point_nonneg`

**File:** `CdFormal/Theorems.lean`

---

### Existence of nontrivial configurations (Theorem 3.16)

**Paper:** Theorem 3.16

When viability exceeds dissipation (\(\lambda_1 < 0\)), there exists a positive solution in the interior --- coherent presence can be self-maintained.

**Proof chain:** Monotone iteration \(\to\) nontrivial fixed point \(\to\) maximum principle.

```lean
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
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0)
```

**Axiom dependencies:** `monotone_iteration`, `fixed_point_nonneg`

**File:** `CdFormal/Theorems.lean`

---

### Scaling uniqueness

**Paper:** Partial answer to Open Problem #3

If \(\Phi\) solves the CD equation and \(k\Phi\) (with \(k > 1\)) also solves it, then at any point where \(c(x_0) > 0\) and \(\Phi(x_0) > 0\), we reach a contradiction. Solutions are unique within the class of proportional rescalings.

**Proof sketch:**

1. \(\Delta(k\Phi) = k\Delta\Phi\) (linearity)
2. \(|\nabla(k\Phi)| = k|\nabla\Phi|\) (homogeneity, \(k > 0\))
3. \((k\Phi)^p = k^p \Phi^p\) (power rule)
4. Equating the two PDE evaluations: \(k \cdot c \cdot \Phi^p = c \cdot k^p \cdot \Phi^p\)
5. Since \(c > 0\) and \(\Phi^p > 0\): \(k = k^p\), contradicting \(k < k^p\) for \(k > 1\), \(p > 1\)

```lean
theorem scaling_uniqueness
    (ops : SemioticOperators n M)
    (ctx : SemioticContext n M)
    (Φ : M → ℝ) (k : ℝ)
    (hk : k > 1)
    (hΦ_eq : ∀ x, -(ops.laplacian Φ x) = ...)
    (hkΦ_eq : ∀ x, -(ops.laplacian (fun y ↦ k * Φ y) x) = ...)
    (x₀ : M) (hc : ctx.c x₀ > 0) (hΦpos : Φ x₀ > 0) :
    False
```

**Axiom dependencies:** `SemioticOperators` fields only --- **no `PDEInfra`**

**File:** `CdFormal/ScalingUniqueness.lean` --- **Provenance:** Aristotle runs `1c3414f4`, `60ec288c`
