# Feature Request: Schaefer's Fixed-Point Theorem

## Mathematical Statement

**Schaefer's Fixed-Point Theorem** (Schaefer 1955; Deimling 1985, Thm 9.2):

Let *E* be a Banach space and *T : E → E* continuous, mapping bounded
sets to relatively compact sets. If the **Schaefer set**
*S = {x ∈ E | ∃ τ ∈ [0,1], x = τ T(x)}* is bounded, then *T* has a
fixed point.

## Current Mathlib State

- `IsCompactOperator` for linear maps (`Mathlib.Analysis.Normed.Operator.Compact`)
- Banach space infrastructure (`Mathlib.Analysis.NormedSpace.Basic`)
- Sperner's lemma (#25231) on the Brouwer path
- **No** Schaefer, Leray-Schauder, or Schauder fixed-point theorems

## API Design Question

Schaefer applies to **nonlinear** operators. The compactness condition
is that *T* maps bounded sets to relatively compact sets. Possible
approaches (seeking guidance):

1. **`IsCompactMap T`** — `∀ S, Bornology.IsBounded S →
   IsCompact (closure (T '' S))`. Extends the concept to nonlinear maps.
2. **Continuous with relatively compact image** — weaker, avoids the
   design question.
3. **Linear version first** — slots into `IsCompactOperator`, doesn't
   cover the nonlinear PDE use case.

## Proof Strategy

Standard route via truncation:

1. Define *Tₙ(x) = T(x) / max(1, ‖T(x)‖/n)*
2. *Tₙ* maps the ball of radius *n* to itself, is continuous, image
   relatively compact
3. Schauder's theorem → *Tₙ* has fixed point *xₙ*
4. Boundedness of *S* gives uniform bound → for large *n*, *xₙ = T(xₙ)*

Dependency chain: Brouwer (Sperner #25231) → Schauder → Schaefer

## Downstream Use Case

We formalize existence theory for a nonlinear elliptic BVP on compact
Riemannian manifolds
([cd-formalization](https://github.com/Project-Navi/cd-formalization)).
The proof chain is verified in Lean 4 against Mathlib v4.28.0 except
the Schaefer step, which is axiomatized in a `PDEInfra` typeclass:

```lean
schaefer :
  True →  -- placeholder for T continuous & compact
  (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K) →
  ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

The project has zero `sorry`, zero `sorryAx`, CI with `--wfail`, and
13 axiom-checked theorems. Having Schaefer in Mathlib would replace
this axiom with a real proof.

**AI disclosure:** Parts of the formalization use Claude (Anthropic)
and Aristotle (theorem prover). All code is manually reviewed.

## References

- H. Schaefer, "Über die Methode der a priori-Schranken," *Math. Ann.*
  **129** (1955), 415–416.
- K. Deimling, *Nonlinear Functional Analysis*, Springer, 1985, Thm 9.2.
- L.C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010,
  §9.2.2.
