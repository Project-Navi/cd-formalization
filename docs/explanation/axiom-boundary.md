# The Axiom Boundary

The `PDEInfra` typeclass packages five classical results from elliptic PDE theory that are not yet available in Mathlib for abstract Riemannian manifolds. This page documents each axiom, explains why it cannot currently be proved in Lean, and tracks its Mathlib status.

---

## Design philosophy

The axiom boundary is the most important architectural decision in this formalization. The guiding principles are:

1. **Nothing hidden.** Every assumption is an explicit field of a typeclass, not a `sorry` buried in a proof.
2. **Dependency visible.** Theorems that use PDE axioms carry `[PDEInfra bvp solOp]` in their signature. Run `#print axioms` to confirm.
3. **Minimize the surface.** Prove everything that can be proved. Only axiomatize what genuinely requires missing Mathlib infrastructure.
4. **Use real mathematics.** The axiom types are not arbitrary --- they carry genuine mathematical content (bornological compactness, eigenvalue structure).

---

## The typeclass

```lean
class PDEInfra (bvp : SemioticBVP n M) (solOp : SolutionOperator bvp) : Prop where
  T_compact        : ...   -- Lemma 3.7
  linfty_bound     : ...   -- Lemma 3.10
  schaefer         : ...   -- Theorem 3.12
  fixed_point_nonneg : ... -- Theorem 3.12
  monotone_iteration : ... -- Theorem 3.16
```

The `Prop`-valued typeclass ensures that axioms are **proof obligations**, not data --- a `PDEInfra` instance witnesses that the five results hold, but carries no computational content.

---

## Axiom 1: T_compact --- Compactness of the solution operator

**Paper reference:** Lemma 3.7

**Classical source:** Schauder estimates + Arzel&agrave;-Ascoli

```lean
T_compact : ∀ S : Set (M → ℝ),
  Bornology.IsVonNBounded ℝ S →
  IsCompact (closure (solOp.T '' S))
```

**What it says:** The solution operator \(T\) maps von Neumann bounded sets to relatively compact sets. In functional analysis terms, \(T\) is a compact operator.

**Why bornological typing?** Mathlib's `Bornology.IsVonNBounded` provides a rigorous characterization of bounded sets in locally convex spaces. This follows an approach suggested by Yongxi Lin (Aaron) on Lean Zulip --- the axiom carries real mathematical content, not just a placeholder.

**Why it can't be proved now:** Requires \(C^{k,\alpha}\) H&ouml;lder spaces on Riemannian manifolds, Schauder estimates (\(\|u\|_{C^{2,\alpha}} \leq C(\|f\|_{C^{0,\alpha}} + \|u\|_{C^0})\)), and Arzel&agrave;-Ascoli for manifold function spaces. None of these exist in Mathlib as of v4.28.0.

---

## Axiom 2: linfty_bound --- L∞ bound for the Schaefer set

**Paper reference:** Lemma 3.10

**Classical source:** Maximum principle (Gilbarg-Trudinger, Chapter 3)

```lean
linfty_bound :
  ∀ (B : ℝ), (∀ x, bvp.ctx.b x ≤ B) →
  ∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K
```

**What it says:** If \(u = \tau T(u)\) for \(\tau \in [0,1]\), then \(\|u\|_\infty \leq K\). The bound \(K = (B/c_0)^{1/(p-1)}\) comes from evaluating the PDE at an interior maximum.

**Decomposition:** This axiom has two parts:

| Part | Status | Content |
|------|--------|---------|
| Maximum principle: at interior max, \(\nabla u = 0\) and \(\Delta u \leq 0\) | **Axiom** | Requires strong maximum principle on manifolds |
| Algebraic: \(bv \geq cv^p \Rightarrow v \leq (b/c)^{1/(p-1)}\) | **Proved** | `linfty_bound_algebraic` in `LinftyAlgebraic.lean` |

The algebraic core is fully machine-checked. Only the analytic step (maximum principle) remains axiomatic.

---

## Axiom 3: schaefer --- Schaefer's fixed-point theorem

**Paper reference:** Theorem 3.12

**Classical source:** Schaefer (1955); Deimling (1985)

```lean
schaefer :
  (∀ S : Set (M → ℝ), Bornology.IsVonNBounded ℝ S →
    IsCompact (closure (solOp.T '' S))) →
  (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K) →
  ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

**What it says:** If \(T\) is compact and the Schaefer set \(\{u : u = \tau T(u),\; \tau \in [0,1]\}\) is bounded, then \(T\) has a fixed point.

**Structural note:** The first argument is `T_compact` --- at the call site, `infra.T_compact` is passed explicitly. This makes the dependency chain structurally visible: compactness feeds into Schaefer's theorem, not just logically but in the Lean proof term.

**Why it can't be proved now:** Mathlib has Banach space basics but no Schaefer's fixed-point theorem (or Leray-Schauder degree theory). A draft Mathlib issue is at [`drafts/mathlib_issue_schaefer.md`](https://github.com/Project-Navi/cd-formalization/blob/main/drafts/mathlib_issue_schaefer.md).

---

## Axiom 4: fixed_point_nonneg --- Maximum principle for fixed points

**Paper reference:** Theorem 3.12 (nonnegativity step)

**Classical source:** Strong maximum principle

```lean
fixed_point_nonneg :
  ∀ (Φ : M → ℝ), solOp.T Φ = Φ → ∀ x, Φ x ≥ 0
```

**What it says:** Fixed points of \(T\) are nonnegative. This follows from the \(\Phi_+\) truncation in the saturation term and standard maximum principle arguments.

**Why it can't be proved now:** Requires the strong maximum principle for elliptic operators on Riemannian manifolds. Mathlib has no maximum principle infrastructure.

---

## Axiom 5: monotone_iteration --- Sub/super-solution method

**Paper reference:** Theorem 3.16

**Classical source:** Amann (1976)

```lean
monotone_iteration :
  ∀ (beta : ℝ) (eig : PrincipalEigendata bvp beta),
    eig.eigval < 0 →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ ∧ (∃ x, x ∉ bvp.boundary ∧ Φ x > 0)
```

**What it says:** When the principal eigenvalue \(\lambda_1 < 0\):

1. \(\varepsilon\varphi_1\) is a sub-solution for small \(\varepsilon\) (Paper Thm 3.16, Step 1)
2. A large constant \(K\) is a super-solution (Step 2)
3. Monotone iteration between them converges to a nontrivial fixed point with \(\Phi > 0\) in the interior (Step 3)

**Order-theoretic skeleton proved.** The abstract Knaster-Tarski result --- that a monotone map on a complete lattice has a fixed point between sub and super-fixed points --- is fully proved in `MonotoneFixedPoint.lean`. Only the PDE content (monotonicity of \(T\), construction of sub/super-solutions, nontriviality) remains axiomatic.

**Why it can't be proved now:** Requires sub/super-solution existence in ordered Banach spaces, comparison principles, and the strong maximum principle for interior positivity. None of these are in Mathlib.

---

## What's not in Mathlib (v4.28.0)

| Missing infrastructure | Required by | Mathlib status |
|-----------------------|-------------|----------------|
| H&ouml;lder spaces on manifolds | `T_compact` | No \(C^{k,\alpha}\) type |
| Schauder estimates | `T_compact` | No Schauder theory |
| Strong maximum principle | `linfty_bound`, `fixed_point_nonneg`, `monotone_iteration` | No max principle |
| Schaefer's fixed-point theorem | `schaefer` | No Leray-Schauder theory |
| Sub/super-solution theory | `monotone_iteration` | No ordered-cone iteration |
| Principal eigenvalue existence | `PrincipalEigendata` | No Krein-Rutman theorem |
| Arzel&agrave;-Ascoli on manifolds | `T_compact` | Exists for metric spaces, not H&ouml;lder embeddings |

---

## Verification

Run `lake build CdFormal.Verify` and confirm:

- `exists_isWeakCoherentConfiguration` shows `PDEInfra` fields but **no `sorryAx`**
- `exists_pos_isWeakCoherentConfiguration` shows `PDEInfra` fields but **no `sorryAx`**
- Pure algebra results show only `[propext, Classical.choice, Quot.sound]`
- Monotone fixed-point results show only `[propext, Quot.sound]` (no `Classical.choice`)
