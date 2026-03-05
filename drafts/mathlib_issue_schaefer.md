# Feature Request: Schaefer's Fixed-Point Theorem

## Mathematical Statement

**Schaefer's Fixed-Point Theorem** (Schaefer 1955; Deimling 1985, Theorem 9.2):

Let *E* be a Banach space and let *T : E → E* be a continuous operator that
maps bounded sets to relatively compact sets. Define the **Schaefer set**

$$S = \{ x \in E \mid \exists\, \tau \in [0,1],\ x = \tau\, T(x) \}.$$

If *S* is bounded, then *T* has a fixed point.

This is a corollary of the Leray-Schauder continuation principle and one of the
most widely used fixed-point theorems in nonlinear PDE theory. Note that *T* is
**not** assumed linear.

## What Mathlib Currently Has

- `IsCompactOperator` and basic composition/precomposition lemmas
  (`Mathlib.Analysis.Normed.Operator.Compact`) — linear maps only
- Banach space infrastructure (`Mathlib.Analysis.NormedSpace.Basic`)
- Sperner's lemma (#25231) — on the path to Brouwer
- **No** Schaefer, Leray-Schauder, or Schauder fixed-point theorem
- **No** fixed-point theorems for compact operators on infinite-dimensional spaces

## API Design Question

Schaefer's theorem applies to **nonlinear** operators — the compactness
condition is that *T* maps bounded sets to relatively compact sets (i.e., *T*
is a compact map in the nonlinear sense). Mathlib's `IsCompactOperator` is
currently defined for linear maps.

Possible approaches (seeking maintainer guidance):

1. **Extend or parallel `IsCompactOperator` for nonlinear maps** — e.g.,
   `IsCompactMap T` meaning the image of any bounded set under *T* has
   compact closure. This is the standard definition in nonlinear functional
   analysis (Deimling Ch. 9).

2. **State the theorem for continuous maps with relatively compact image** —
   weaker but avoids the design question. Require something like
   `∀ S, Bornology.IsBounded S → IsCompact (closure (T '' S))`.

3. **State the linear version first** and generalize later — slots into the
   existing `IsCompactOperator` API but doesn't cover the nonlinear PDE
   use case.

## Proof Strategy and Dependencies

The standard proof goes through the Leray-Schauder continuation principle.
A more elementary route via truncation:

1. For each *n*, define *Tₙ(x) = T(x) / max(1, ‖T(x)‖/n)*
2. *Tₙ* maps the ball of radius *n* to itself, is continuous, image is
   relatively compact
3. By Schauder's fixed-point theorem (compact convex set version), *Tₙ*
   has a fixed point *xₙ*
4. Boundedness of *S* gives a uniform bound on *‖xₙ‖*, so for large *n*,
   *xₙ = T(xₙ)*

Dependency chain:

```
Brouwer (or Sperner #25231 → Brouwer)
    → Schauder (compact convex set)
    → Schaefer (this request)
```

## Concrete Downstream Use Case

We are formalizing existence theory for a nonlinear elliptic BVP on compact
Riemannian manifolds
([Project-Navi/cd-formalization](https://github.com/Project-Navi/cd-formalization)).
The proof chain is:

1. Define a solution operator *T* (continuous, compact by Schauder estimates)
2. Prove the Schaefer set is bounded (a priori L∞ bound — algebraic core
   proved in Lean)
3. Apply Schaefer's theorem to obtain a fixed point — **currently axiomatized**
4. Conclude existence

The axiomatization:

```lean
class PDEInfra (bvp : SemioticBVP n M) (solOp : SolutionOperator bvp) : Prop where
  /-- T is continuous and compact (placeholder — see known limitation) -/
  T_continuous_compact : True
  ...
  /-- Schaefer's fixed-point theorem -/
  schaefer :
    True →  -- placeholder for T continuous & compact
    (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K) →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

Having Schaefer's theorem in Mathlib would let us (and others) replace this
axiom with a real proof.

**AI disclosure:** Parts of the formalization were developed with Claude
(Anthropic) and Aristotle (theorem prover). All code has been manually
reviewed and understood.

## References

- H. Schaefer, "Uber die Methode der a priori-Schranken," *Math. Ann.*
  **129** (1955), 415-416.
- K. Deimling, *Nonlinear Functional Analysis*, Springer, 1985, Theorem 9.2.
- L.C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §9.2.2.
- D. Gilbarg and N.S. Trudinger, *Elliptic Partial Differential Equations
  of Second Order*, Springer, 2001.

## Related Missing Results

| Result | Dependency | Use Case |
|--------|-----------|----------|
| Schauder fixed-point theorem (compact convex) | Brouwer + compact operators | Intermediate step for Schaefer |
| Leray-Schauder continuation | Degree theory or Schaefer | General nonlinear PDE existence |
| Strong maximum principle | Elliptic operator theory | Positivity/uniqueness of PDE solutions |
