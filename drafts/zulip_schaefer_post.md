# Zulip Post Draft: Schaefer's Fixed-Point Theorem

**Channel:** `#Is there code for X?`
**Subject:** Schaefer's fixed-point theorem (nonlinear compact operators)

---

Hi all,

I'm looking for Schaefer's fixed-point theorem or the Leray-Schauder
continuation principle in Mathlib — is there existing work on either of these?

**Context:** Schaefer's theorem says that if *T : E → E* is continuous and
compact (maps bounded sets to relatively compact sets) on a Banach space, and
the set *S = {x : ∃ τ ∈ [0,1], x = τ · T(x)}* is bounded, then *T* has a
fixed point. It's a standard tool in nonlinear PDE existence theory (Deimling
1985, Theorem 9.2; Evans 2010, §9.2.2).

**What I've found so far:**
- `IsCompactOperator` exists for linear maps (`Mathlib.Analysis.Normed.Operator.Compact`)
- Sperner's lemma is in progress (#25231), which is on the path to Brouwer → Schauder → Schaefer
- I don't see Schauder's fixed-point theorem (compact convex set version) either

**Concrete use case:** I'm working on a formalization of existence theory for a
nonlinear elliptic BVP on compact Riemannian manifolds
([Project-Navi/cd-formalization](https://github.com/Project-Navi/cd-formalization)).
The proof chain goes: L∞ bound → Schaefer set bounded → **Schaefer's theorem**
→ fixed point. Everything except the Schaefer step is verified in Lean 4 against
Mathlib; that step is currently axiomatized as:

```lean
schaefer :
  True →  -- placeholder for T continuous & compact
  (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K) →
  ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

**API question:** The nonlinear case needs a notion of "compact map" for
nonlinear operators (T maps bounded sets to relatively compact sets). Should
this extend or parallel `IsCompactOperator`? I'd appreciate any guidance on
how this fits the existing API before attempting anything.

**AI disclosure:** Parts of the formalization were developed with Claude
(Anthropic) and Aristotle (theorem prover). All code has been manually
reviewed and understood.

Thanks for any pointers!
