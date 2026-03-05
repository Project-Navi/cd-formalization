# Mathlib Conventions Compliance — Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Bring the cd_formalization Lean 4 project into compliance with Mathlib naming, formatting, documentation, and import conventions (items 1–5 from audit).

**Architecture:** Five mechanical refactoring tasks, each independently testable via `lake build --wfail`. No mathematical changes — only names, docstrings, import locations, and variable blocks. Each task touches a small surface area and is verified by a successful build.

**Tech Stack:** Lean 4 v4.28.0, Mathlib, `lake build --wfail`

---

### Task 1: Rename existence theorems (High priority)

**Files:**
- Modify: `CdFormal/Theorems.lean:77,103`
- Modify: `CdFormal/Verify.lean:22-23`

**Context:** Mathlib never uses `existence_` prefix in theorem names. The convention is `exists_` for existential conclusions, namespaced under the relevant type. Two theorems need renaming.

**Step 1: Rename in Theorems.lean**

In `CdFormal/Theorems.lean`, make these two name changes:

```lean
-- Line 77: change
theorem existence_weak_coherent_configuration
-- to:
theorem SemioticBVP.exists_isWeakCoherentConfiguration

-- Line 103: change
theorem existence_nontrivial_coherent_configuration
-- to:
theorem SemioticBVP.exists_pos_isWeakCoherentConfiguration
```

For the namespaced theorems, the `{n}` and `{M}` implicit args stay, but `(bvp : SemioticBVP n M)` moves to the namespace. Since we're using `SemioticBVP.` prefix, the first explicit argument `bvp` becomes dot-notation eligible. No signature changes needed beyond the name.

**Step 2: Update Verify.lean references**

In `CdFormal/Verify.lean`, update the `#print axioms` calls:

```lean
-- Line 22: change
#print axioms existence_weak_coherent_configuration
-- to:
#print axioms SemioticBVP.exists_isWeakCoherentConfiguration

-- Line 23: change
#print axioms existence_nontrivial_coherent_configuration
-- to:
#print axioms SemioticBVP.exists_pos_isWeakCoherentConfiguration
```

**Step 3: Build and verify**

Run: `lake build --wfail`
Expected: Success, zero sorry, zero errors.

**Step 4: Commit**

```bash
git add CdFormal/Theorems.lean CdFormal/Verify.lean
git commit -m "refactor: rename existence theorems to Mathlib exists_ convention"
```

---

### Task 2: Fix module docstrings (High priority)

**Files:**
- Modify: `CdFormal/Basic.lean:1-11,25,40,90,113,147`
- Modify: `CdFormal/Axioms.lean:1-23,34,56,80`
- Modify: `CdFormal/Theorems.lean:1-11,22,50,69`
- Modify: `CdFormal/Verify.lean:1-13`

**Context:** Mathlib requires module docstrings to use `/-! ... -/` syntax (not `/-`), placed *after* imports, with structured sections including `## Main definitions`.

**Step 1: Fix Basic.lean**

Remove the block comment before imports (lines 1-11). After line 23 (`open scoped ...`), insert a proper module docstring:

```lean
/-!
# Creative Determinant Framework — Core Definitions

Formalization of the semiotic manifold, coefficient structures, PDE operators,
boundary value problem, and weak coherent configuration.

## Main definitions

- `SemioticModel` — model with corners for the semiotic manifold
- `SemioticManifold` — compact, connected, smooth Riemannian manifold (Paper Definition 2.1)
- `SemioticContext` — coefficients κ, γ, μ, b, c, p for the BVP (Paper Definitions 2.2, 3.1)
- `SemioticOperators` — abstract Laplacian and gradient norm (Paper Section 3.2)
- `SemioticBVP` — the boundary value problem -ΔΦ = a|∇Φ| + bΦ - cΦᵖ (Paper Definition 3.1)
- `IsWeakCoherentConfiguration` — a solution to the BVP (Paper §3.2)

## References

- [Spence2026] N. Spence, "The Creative Determinant: Autopoietic Closure as a
  Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions," 2026.
-/
```

Keep the existing `/-! ## Semiotic Manifold -/` section headers — those are already correct `/-!` syntax.

**Step 2: Fix Axioms.lean**

Remove the block comment before imports (lines 1-23). After line 32 (`open scoped ...`), insert:

```lean
/-!
# PDE Infrastructure Axioms

Axioms encoding classical results from elliptic PDE theory not yet available in
Mathlib for abstract Riemannian manifolds.

## Main definitions

- `SolutionOperator` — the operator T for the BVP (Paper Section 3.2)
- `PrincipalEigendata` — principal eigenvalue and eigenfunction (Paper Definition 3.13)
- `PdeInfra` — typeclass packaging five PDE infrastructure axioms

## Implementation notes

Axioms are packaged in a typeclass `PdeInfra` so downstream theorems explicitly
declare their dependence via `[PdeInfra bvp solOp]`. The axiom surface is:
1. T continuous & compact (placeholder `True`)
2. L∞ bound (maximum principle)
3. Schaefer's fixed-point theorem
4. Fixed-point nonnegativity (maximum principle)
5. Monotone iteration (sub/super-solution, Amann 1976)

## References

- [Schaefer1955] H. Schaefer, "Über die Methode der a priori-Schranken," 1955.
- [Evans2010] L.C. Evans, *Partial Differential Equations*, 2nd ed., Ch. 6.
- [GilbargTrudinger2001] D. Gilbarg and N.S. Trudinger, Ch. 6–8.
- [Amann1976] H. Amann, "Fixed point equations and nonlinear eigenvalue problems," 1976.
- [Spence2026] N. Spence, "The Creative Determinant," 2026.
-/
```

**Step 3: Fix Theorems.lean**

Remove the block comment before imports (lines 1-11). After line 20 (`open scoped ...`), insert:

```lean
/-!
# Creative Determinant — Theorems

## Main statements

- `spectral_characterization_1d` — β > β* implies eigenvalue < 0 (pure algebra)
- `scaling_algebraic_contradiction` — k < kᵖ when p > 1 (pure algebra)
- `SemioticBVP.exists_isWeakCoherentConfiguration` — existence of nonneg solutions (Paper Thm 3.12)
- `SemioticBVP.exists_pos_isWeakCoherentConfiguration` — existence of positive solutions (Paper Thm 3.16)

## Implementation notes

The first two results are proved by pure algebra (no PDE axioms).
The existence theorems compose `PdeInfra` axioms; all dependencies are visible
via `[PdeInfra bvp solOp]` and `#print axioms` in `CdFormal.Verify`.

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.
-/
```

**Step 4: Fix Verify.lean**

Remove the block comment before imports (lines 1-13). After line 15 (`import CdFormal.Theorems`), insert:

```lean
/-!
# Axiom Contamination Checks

Verification dashboard: run `lake build CdFormal.Verify` to confirm which axioms
each theorem depends on. If `sorryAx` appears anywhere, something is broken.

Pure algebra theorems should show only `[propext, Classical.choice, Quot.sound]`.
PDE-dependent theorems should additionally show `PdeInfra` fields but no `sorryAx`.
-/
```

**Step 5: Build and verify**

Run: `lake build --wfail`
Expected: Success.

**Step 6: Commit**

```bash
git add CdFormal/Basic.lean CdFormal/Axioms.lean CdFormal/Theorems.lean CdFormal/Verify.lean
git commit -m "docs: convert to Mathlib module docstring conventions (/-! after imports)"
```

---

### Task 3: Introduce variable blocks (Medium priority)

**Files:**
- Modify: `CdFormal/Basic.lean`
- Modify: `CdFormal/Axioms.lean`
- Modify: `CdFormal/Theorems.lean`

**Context:** The 7-typeclass argument list is repeated 12+ times. Mathlib uses `variable` blocks to declare these once. Each definition/theorem then only lists its own specific parameters.

**Step 1: Add variable block to Basic.lean**

After the module docstring and before `/-! ## Semiotic Manifold -/`, add:

```lean
variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
```

Then for declarations that need `SemioticManifold`, add a second `variable` after the class definition:

```lean
variable [SemioticManifold n M]
```

**Important:** `SemioticModel` and `SemioticManifold` must keep explicit `(n : ℕ) (M : Type*)` in their signatures because they are *defining* these — they can't reference themselves via `variable`. Everything *after* their definitions can use the variable block.

Remove the explicit argument lists from: `SemioticContext`, `SemioticContext.a`, `SemioticContext.canonicalViability`, `SemioticOperators`, `SemioticBVP`, `IsWeakCoherentConfiguration`.

For each, remove the lines:
```lean
    {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M]
```

Note: `SemioticContext` and `SemioticOperators` and `SemioticBVP` currently use *explicit* `(n : ℕ) (M : Type*)` — structures typically need explicit universe-polymorphic parameters. Check if Lean auto-includes from the `variable` block. If structures require explicit params, keep `(n : ℕ) (M : Type*)` but still drop the typeclass instances (they'll come from the variable block).

**Step 2: Add variable block to Axioms.lean**

After the module docstring, add the same variable block. Remove explicit argument lists from `SolutionOperator`, `PrincipalEigendata`, `PdeInfra`.

**Step 3: Add variable block to Theorems.lean**

After the module docstring, add the variable block. Remove explicit argument lists from the two existence theorems (`SemioticBVP.exists_isWeakCoherentConfiguration`, `SemioticBVP.exists_pos_isWeakCoherentConfiguration`). Note: `viabilityThreshold` and `spectral_characterization_1d` don't use the manifold variables (they're 1D algebra), so leave them alone.

**Step 4: Build and verify**

Run: `lake build --wfail`
Expected: Success. This is the trickiest task — Lean's variable inclusion rules may require adjusting. If a structure needs explicit params, add them back selectively.

**Step 5: Commit**

```bash
git add CdFormal/Basic.lean CdFormal/Axioms.lean CdFormal/Theorems.lean
git commit -m "refactor: use variable blocks to eliminate repeated typeclass arguments"
```

---

### Task 4: Move `import Mathlib.Tactic` to Theorems.lean (Medium priority)

**Files:**
- Modify: `CdFormal/Basic.lean:16`
- Modify: `CdFormal/Theorems.lean:13`

**Context:** `Basic.lean` is a definitions-only file with no tactic proofs. `import Mathlib.Tactic` is only needed in `Theorems.lean` (which uses `positivity`, `linarith`, `nlinarith`, `simp only`). Moving it reduces the import footprint and build time for `Basic.lean` and `Axioms.lean`.

**Step 1: Remove from Basic.lean**

Delete line 16 of `CdFormal/Basic.lean`:
```lean
import Mathlib.Tactic
```

**Step 2: Add to Theorems.lean**

In `CdFormal/Theorems.lean`, after `import CdFormal.Axioms`, add:
```lean
import Mathlib.Tactic
```

**Step 3: Build and verify**

Run: `lake build --wfail`
Expected: Success. If `Basic.lean` fails without `Mathlib.Tactic` (e.g., if some notation or instance resolution depends on it), add back a *specific* import (e.g., `Mathlib.Tactic.NormNum`) instead of the blanket import.

**Step 4: Commit**

```bash
git add CdFormal/Basic.lean CdFormal/Theorems.lean
git commit -m "refactor: move Mathlib.Tactic import to Theorems.lean (only file needing tactics)"
```

---

### Task 5: Rename fields to Mathlib conventions (Medium priority)

**Files:**
- Modify: `CdFormal/Basic.lean` (3 renames)
- Modify: `CdFormal/Axioms.lean` (1 rename, update references)
- Modify: `CdFormal/Theorems.lean` (update references)

**Context:** Three naming convention violations:
1. `p_gt_one` → `one_lt_p` (Mathlib normalizes to `lt` not `gt`)
2. `boundaryCondition` → `boundary_condition` (Prop-valued field should be snake_case)
3. `PdeInfra` → `PDEInfra` (known acronyms stay fully capitalized)

**Step 1: Rename `p_gt_one` to `one_lt_p` in Basic.lean**

In `CdFormal/Basic.lean`, change the field name in `SemioticContext`:
```lean
-- Change:
  p_gt_one : p > 1
-- To:
  one_lt_p : 1 < p
```

Note: `p > 1` is definitionally equal to `1 < p` in Lean/Mathlib (`GT.gt` unfolds to `LT.lt` with swapped args), so no proof changes should be needed. But check downstream references.

**Step 2: Rename `boundaryCondition` to `boundary_condition` in Basic.lean**

In `SemioticBVP`:
```lean
-- Change:
  boundaryCondition : (M → ℝ) → Prop := fun Φ =>
-- To:
  boundary_condition : (M → ℝ) → Prop := fun Φ =>
```

In `IsWeakCoherentConfiguration`:
```lean
-- Change:
  bvp.equation Φ ∧ bvp.boundaryCondition Φ
-- To:
  bvp.equation Φ ∧ bvp.boundary_condition Φ
```

**Step 3: Rename `PdeInfra` to `PDEInfra` everywhere**

This affects:
- `CdFormal/Axioms.lean`: class definition (line 88), all doc references
- `CdFormal/Theorems.lean`: `[infra : PdeInfra bvp solOp]` on lines 86 and 112, doc references
- `CdFormal/Verify.lean`: doc text

Use find-and-replace `PdeInfra` → `PDEInfra` across all files.

**Step 4: Build and verify**

Run: `lake build --wfail`
Expected: Success. The `p > 1` ↔ `1 < p` change is the one most likely to cause proof breakage — if it does, adjust the proof in `scaling_algebraic_contradiction` (which references `hp : p > 1`; this would become `hp : 1 < p`, and you may need to adjust `hp` usage to `gt_iff_lt` or just use `hp` directly since Lean should handle the definitional equality).

**Step 5: Commit**

```bash
git add CdFormal/Basic.lean CdFormal/Axioms.lean CdFormal/Theorems.lean CdFormal/Verify.lean
git commit -m "refactor: rename p_gt_one/boundaryCondition/PdeInfra to Mathlib conventions"
```

---

### Post-plan: Update README and docs

After all 5 tasks pass `lake build --wfail`, update `README.md` to reflect any renamed theorems (the table references `existence_weak_coherent_configuration` etc.) and push.
