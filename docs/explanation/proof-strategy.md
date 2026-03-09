# Proof Strategy

How the Creative Determinant existence theory is structured in Lean 4 --- from definitions to the headline theorems.

---

## The goal

Prove two existence theorems for the boundary value problem:

\[
-\Delta\Phi = a(x)\,|\nabla\Phi| + b(x)\,\Phi - c(x)\,(\Phi_+)^p, \qquad \Phi\big|_{\partial M} = 0
\]

on a compact Riemannian manifold \(M\), where the coefficients encode care (\(\kappa\)), coherence (\(\gamma\)), and contradiction (\(\mu\)):

- **Theorem 3.12** (existence): a nonnegative solution \(\Phi \geq 0\) exists.
- **Theorem 3.16** (nontriviality): when viability exceeds dissipation --- that is, when the principal eigenvalue \(\lambda_1(-\Delta - b;\, M) < 0\) --- a **positive** solution exists in the interior.

---

## Architecture: axiomatize the analysis, verify the logic

The central design decision is **where to draw the boundary between what Lean proves and what it takes on trust**.

Classical elliptic PDE theory (Schauder estimates, maximum principles, Schaefer's theorem, sub/super-solution iteration) is not yet available in Mathlib for abstract Riemannian manifolds. Rather than wait for these to be formalized, the proof strategy is:

1. **Axiomatize** the five classical results as the `PDEInfra` typeclass
2. **Verify** that the headline theorems follow from these axioms by correct logical composition
3. **Prove** everything else --- algebra, real analysis, order theory, operator consequences, coefficient bounds --- with zero axioms beyond Lean's kernel

This means the formalization answers a precise question: *Given standard elliptic PDE infrastructure, does the proof logic actually work?* The answer is yes, machine-checked.

---

## The proof chain

### Theorem 3.12 --- Existence of nonnegative solutions

The proof composes three `PDEInfra` axioms in sequence:

```
L∞ bound  ───►  Schaefer's theorem  ───►  Maximum principle
(linfty_bound)    (schaefer)              (fixed_point_nonneg)
    │                  │                        │
    ▼                  ▼                        ▼
Schaefer set     Fixed point Φ          Φ(x) ≥ 0 ∀x
is bounded       with T(Φ) = Φ
```

In Lean:

```lean
theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) := by
  have h_bounded := infra.linfty_bound B hB
  obtain ⟨Phi, hfix⟩ := infra.schaefer infra.T_compact h_bounded
  exact ⟨Phi, solOp.T_fixed_point Phi hfix,
         infra.fixed_point_nonneg Phi hfix⟩
```

The proof is three lines. The work is in establishing that the axioms compose correctly --- that the output of each step has the right type to feed into the next.

### Theorem 3.16 --- Existence of positive solutions

When the principal eigenvalue is negative (\(\lambda_1 < 0\)), the sub/super-solution method produces a nontrivial fixed point:

```
Monotone iteration  ───►  Maximum principle  ───►  T-fixed = BVP solution
(monotone_iteration)      (fixed_point_nonneg)     (T_fixed_point)
      │                         │                        │
      ▼                         ▼                        ▼
  Fixed point Φ            Φ(x) ≥ 0 ∀x          IsWeakCoherentConfiguration
  with Φ(x₀) > 0
  in interior
```

In Lean:

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
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0) := by
  obtain ⟨Phi, hfix, x, hx_int, hx_pos⟩ :=
    infra.monotone_iteration beta eig eigval_neg
  exact ⟨Phi, solOp.T_fixed_point Phi hfix,
    infra.fixed_point_nonneg Phi hfix, x, hx_int, hx_pos⟩
```

---

## Supporting results

The headline theorems rest on a foundation of fully proved lemmas organized in four tiers.

### Tier 1 --- Pure algebra (no domain axioms)

These depend only on Lean's kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Spectral characterization (1D).** For constant viability \(b\) on \([0, L]\), the principal eigenvalue is \(\lambda_1 = (\pi/L)^2 - \beta b\). The condition \(\lambda_1 < 0\) reduces to \(\beta > \beta^*\) where:

\[
\beta^* = \frac{(\pi/L)^2}{b}
\]

**Scaling algebraic contradiction.** If \(p > 1\) and \(k > 1\), then \(k < k^p\). This is the algebraic core of the scaling uniqueness argument --- used to show that proportional rescalings \(k\Phi\) cannot also be solutions.

### Tier 2 --- Real analysis (no domain axioms)

**L∞ bound algebraic core.** From the PDE inequality at an interior maximum:

\[
b \cdot v \geq c \cdot v^p \quad\Longrightarrow\quad v \leq \left(\frac{b}{c}\right)^{1/(p-1)}
\]

The proof divides both sides by \(c \cdot v\) (positive), obtains \(v^{p-1} \leq b/c\), then takes the \((p-1)\)-th root using `Real.rpow_le_rpow`. This is the algebraic half of Paper Lemma 3.10; the maximum-principle half (\(\nabla u = 0\), \(\Delta u \leq 0\) at interior max) remains an axiom.

### Tier 3 --- Order theory (no `Classical.choice`)

**Monotone fixed point between sub/super.** If \(f : \alpha \to \alpha\) is monotone on a complete lattice with \(\text{sub} \leq f(\text{sub})\) and \(f(\text{super}) \leq \text{super}\), then \(f\) has a fixed point \(x\) with \(\text{sub} \leq x \leq \text{super}\).

This is the order-theoretic skeleton of Amann's (1976) sub/super-solution method. The proof uses `OrderHom.nextFixed` from Mathlib's Knaster-Tarski infrastructure. Notably, these theorems depend only on `[propext, Quot.sound]` --- **no `Classical.choice`** --- making them candidates for constructive upstream contribution.

### Tier 4 --- Derived lemmas

**Operator consequences** (from `SemioticOperators` axioms):

- \(\Delta(0) = 0\) --- from homogeneity with \(c = 0\)
- \(\Delta(cf + g) = c\Delta f + \Delta g\) --- from additivity + homogeneity
- \(\|\nabla 0\| = 0\) --- from `gradNorm_const` with \(a = 0\)

**Coefficient bounds** (from `SemioticContext` field constraints):

- \(a(x) = \kappa\gamma\mu \geq 0\) --- each factor in \([0,1]\)
- \(a(x) = \kappa\gamma\mu \leq 1\) --- each factor in \([0,1]\)
- \(p - 1 > 0\) --- from \(p > 1\)

**Scaling uniqueness** (PDE-level, from `SemioticOperators` + `SemioticContext`):

If \(\Phi\) and \(k\Phi\) with \(k > 1\) both solve the BVP, then at any point where \(c(x_0) > 0\) and \(\Phi(x_0) > 0\), we reach a contradiction. The proof uses Laplacian linearity (\(\Delta(k\Phi) = k\Delta\Phi\)), gradient homogeneity (\(|\nabla(k\Phi)| = k|\nabla\Phi|\)), and the algebraic fact \(k < k^p\).

---

## Design principles

### Explicit axiom surface

Every axiom lives in the `PDEInfra` typeclass. Downstream theorems declare their dependence via `[PDEInfra bvp solOp]`. There is no hidden trust --- `#print axioms` in `Verify.lean` lists exactly what each theorem assumes.

### Decomposition strategy

Where possible, results are decomposed into an **axiom** (analytic) part and a **proved** (algebraic) part. The L∞ bound is the clearest example:

- **Axiom:** at an interior maximum, \(\nabla u = 0\) and \(\Delta u \leq 0\) (maximum principle)
- **Proved:** \(bv \geq cv^p\) implies \(v \leq (b/c)^{1/(p-1)}\) (pure real analysis)

This maximizes the proved surface area while being honest about what requires classical PDE infrastructure.

### Upstream candidates

Results that depend on no domain-specific axioms are tagged as upstream candidates for Mathlib contribution:

- `monotone_fixed_point_between` (order theory, no `Classical.choice`)
- `OrderHom.nextFixed_le_of_le` (order theory, no `Classical.choice`)
- `rpow_le_of_mul_rpow_le` and `linfty_bound_algebraic` (pure real analysis)

These are self-contained lemmas that could benefit the broader Lean community.
