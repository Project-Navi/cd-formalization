# Zulip Post Draft: Schaefer's Fixed-Point Theorem

**Channel:** `#Is there code for X?`
**Subject:** Schaefer's fixed-point theorem (nonlinear compact operators)

---

Hi all,

Is there existing work on Schaefer's fixed-point theorem or the
Leray-Schauder continuation principle in Mathlib?

**The theorem:** If *T : E → E* is continuous and compact on a Banach
space, and the set *{x : ∃ τ ∈ [0,1], x = τ · T(x)}* is bounded,
then *T* has a fixed point (Deimling 1985, Thm 9.2).

**What I've found:**
- `IsCompactOperator` for linear maps (`Mathlib.Analysis.Normed.Operator.Compact`)
- Sperner's lemma (#25231) on the path to Brouwer → Schauder → Schaefer
- No Schauder or Schaefer fixed-point theorems

**Use case:** I have a Lean 4 formalization of existence theory for a
nonlinear elliptic BVP on compact Riemannian manifolds
([cd-formalization](https://github.com/Project-Navi/cd-formalization)).
The proof chain — L∞ bound, Schaefer set bounded, fixed point, maximum
principle — is verified except the Schaefer step, which is axiomatized:

```lean
schaefer :
  True →  -- placeholder for T continuous & compact
  (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K) →
  ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

**API question:** The nonlinear case needs "compact map" for nonlinear
operators (bounded sets → relatively compact sets). Should this extend
or parallel `IsCompactOperator`? Happy to take guidance on how this
fits the existing API.

**AI disclosure:** Parts of the formalization use Claude (Anthropic)
and Aristotle (theorem prover). All code is manually reviewed.

Thanks for any pointers!
