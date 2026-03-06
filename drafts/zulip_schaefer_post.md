# Zulip Post Draft: Schaefer's Fixed-Point Theorem

**Channel:** `#Is there code for X?`
**Subject:** Schaefer's fixed-point theorem (nonlinear compact operators)

---

Hi everyone,

I'm Nelson — first time posting here. I've been working on a Lean 4
formalization of a nonlinear elliptic PDE result as part of a research
project, and it's been a great way to learn both Lean and Mathlib. I'm
hoping to get some guidance from the community on a gap I've hit.

**Context:** I have a formalization of existence theory for a nonlinear
elliptic BVP on compact Riemannian manifolds
([cd-formalization](https://github.com/Project-Navi/cd-formalization)).
The proof chain — L∞ bound → Schaefer set bounded → fixed point →
maximum principle — builds and passes CI with `--wfail`, zero `sorry`.
But five steps in the chain are axiomatized in a `PDEInfra` typeclass
because the underlying classical PDE infrastructure isn't in Mathlib yet.

The one I'd most like to understand better is **Schaefer's fixed-point
theorem** (Deimling 1985, Thm 9.2): if *T : E → E* is continuous and
compact on a Banach space, and the set *{x : ∃ τ ∈ [0,1], x = τ · T(x)}*
is bounded, then *T* has a fixed point.

**What I've found so far:**
- `IsCompactOperator` for linear maps (`Mathlib.Analysis.Normed.Operator.Compact`)
- Sperner's lemma (#25231) — great to see this landing, since it's the
  foundation of the Brouwer → Schauder → Schaefer chain
- No Schauder or Schaefer fixed-point theorems yet

**Where I'm stuck:** In my formalization, the Schaefer step is axiomatized as:

```lean
schaefer :
  True →  -- placeholder for T continuous & compact
  (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K) →
  ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

The `True →` is a placeholder for the compactness hypothesis — I wasn't
sure how to state "T is continuous and maps bounded sets to relatively
compact sets" for a nonlinear operator in Mathlib's current API. The
linear `IsCompactOperator` doesn't quite fit since Schaefer applies to
nonlinear maps.

**What I'm looking for:**
- Has anyone started work on Schaefer, Schauder, or Leray-Schauder
  (beyond the Sperner foundation)?
- Is there a preferred way to express nonlinear compactness (something
  like `IsCompactMap`)? I'd appreciate guidance on how this should fit
  the existing API.
  - I'm looking to contribute upstream if this would support Mathlib's long-term goals — I'd just need some mentoring on the right approach since I'm new to the Mathlib
  contribution process.

**AI disclosure:** The equations, proof strategy, and formalization
architecture are my own work — Claude (Anthropic) assisted with Lean 4
syntax and Mathlib API navigation, and Aristotle (theorem prover)
automated some standalone algebraic lemmas. All code is manually
reviewed; the Lean compiler is the final arbiter (`lake build --wfail`).

Thank you in advance for the guidance!
