# Feature Request: Schaefer's Fixed-Point Theorem

## Mathematical Statement

**Schaefer's Fixed-Point Theorem** (Schaefer 1955; Deimling 1985, Theorem 9.2):

Let *E* be a Banach space and let *T : E → E* be a continuous operator whose image is relatively compact. Define the **Schaefer set**

$$S = \{ x \in E \mid \exists\, \tau \in [0,1],\ x = \tau\, T(x) \}.$$

If *S* is bounded, then *T* has a fixed point.

This is a direct corollary of the Leray–Schauder continuation principle and is one of the most widely used fixed-point theorems in nonlinear PDE theory. Note that *T* is **not** assumed linear — the theorem applies to nonlinear operators.

## What Mathlib Currently Has

- `IsCompactOperator` and basic composition/precomposition lemmas (`Mathlib.Analysis.Normed.Operator.Compact`)
- Banach space infrastructure (`Mathlib.Analysis.NormedSpace.Basic`)
- Brouwer's fixed-point theorem is listed in `docs/100.yaml` but references an external Lean 3 repo, not Mathlib itself
- **No** Schaefer, Leray–Schauder, or Schauder fixed-point theorem
- **No** fixed-point theorems for compact operators on infinite-dimensional spaces

## API Design Question

Schaefer's theorem applies to **nonlinear** operators — the compactness condition is that *T* maps bounded sets to relatively compact sets (i.e., *T* is a compact map in the nonlinear sense). However, Mathlib's `IsCompactOperator` is currently defined for linear maps.

There are a few possible approaches, and I'd welcome guidance from maintainers on which fits the library best:

1. **Extend `IsCompactOperator` (or add a parallel predicate) for nonlinear maps** — e.g., `IsCompactMap T` meaning the image of any bounded set under *T* has compact closure. This is the most general and the standard definition in nonlinear functional analysis (Deimling Ch. 9).

2. **State the theorem for continuous maps with relatively compact image** — weaker but avoids the design question around `IsCompactOperator`. Something like requiring `IsCompact (closure (Set.range T))` or a bounded-set version.

3. **State the linear version first** and generalize later — this would slot directly into the existing `IsCompactOperator` API but wouldn't cover the nonlinear PDE use case.

Option 1 seems most useful long-term, but option 2 would be a reasonable first step.

## Why This Matters

Schaefer's theorem is the standard tool for proving existence of solutions to nonlinear elliptic and parabolic PDEs via the operator formulation. Without it, any Lean formalization of PDE existence theory must axiomatize the fixed-point step.

### Concrete use case

We are formalizing the existence theory for a nonlinear elliptic BVP on compact Riemannian manifolds ([Project-Navi/cd-formalization](https://github.com/Project-Navi/cd-formalization)). The proof chain is:

1. Define a solution operator *T* (continuous, compact by Schauder estimates)
2. Prove the Schaefer set is bounded (a priori L∞ bound — **algebraic core proved in Lean**)
3. Apply Schaefer's theorem to obtain a fixed point ← **currently axiomatized**
4. Conclude existence

Steps 1, 2 (algebraic part), and 4 are fully verified in Lean 4 against Mathlib v4.28.0. Step 3 is the gap. Our axiomatization:

```lean
class PdeInfra (bvp : SemioticBVP n M) (solOp : SolutionOperator bvp) : Prop where
  ...
  schaefer :
    (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K) →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

Having Schaefer's theorem in Mathlib would let us (and others) replace this axiom with a real proof.

## Suggested Lean Statement

Assuming option 2 (minimal dependencies, nonlinear):

```lean
/-- Schaefer's fixed-point theorem: if T is continuous, maps bounded sets to
    relatively compact sets, and the Schaefer set {x | ∃ τ ∈ [0,1], x = τ • T(x)}
    is bounded, then T has a fixed point. -/
theorem schaefer_fixed_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : E → E} (hT_cont : Continuous T)
    (hT_compact : ∀ S : Set E, Bornology.IsBounded S →
      IsCompact (closure (T '' S)))
    (hS : ∃ K, ∀ x : E, (∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ x = τ • T x) → ‖x‖ ≤ K) :
    ∃ x : E, T x = x := by
  sorry
```

## Proof Strategy and Dependencies

The standard proof goes through the Leray–Schauder continuation principle (or degree theory). A more elementary route:

1. For each *n*, define *Tₙ(x) = T(x) / max(1, ‖T(x)‖/n)* (a truncation into the ball of radius *n*)
2. *Tₙ* maps *B̄(0, n) → B̄(0, n)*, is continuous, and the image is relatively compact
3. By Schauder's fixed-point theorem (compact convex set version), *Tₙ* has a fixed point *xₙ*
4. The boundedness of *S* gives a uniform bound on *‖xₙ‖*, so for large *n*, *xₙ = T(xₙ)*

This route requires **Schauder's fixed-point theorem for compact convex sets**, which in turn requires **Brouwer's fixed-point theorem** (see #25231 for Sperner's lemma, one route to Brouwer). So this feature request is likely blocked by that dependency chain:

```
Brouwer (or Sperner #25231 → Brouwer)
    → Schauder (compact convex set)
    → Schaefer (this request)
```

Filing this now to document the downstream need and the connection to Sperner/Brouwer.

## References

- H. Schaefer, "Über die Methode der a priori-Schranken," *Math. Ann.* **129** (1955), 415–416.
- K. Deimling, *Nonlinear Functional Analysis*, Springer, 1985, Theorem 9.2.
- L.C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §9.2.2.
- D. Gilbarg and N.S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer, 2001.

## Related Missing Results

These would further unblock PDE formalization in Mathlib:

| Result | Dependency | Use Case |
|--------|-----------|----------|
| Schauder fixed-point theorem (compact convex) | Brouwer + compact operators | Intermediate step for Schaefer |
| Leray–Schauder continuation | Degree theory or Schaefer | General nonlinear PDE existence |
| Strong maximum principle | Elliptic operator theory | Positivity/uniqueness of PDE solutions |
