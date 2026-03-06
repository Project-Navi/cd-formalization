# CLAUDE.md — cd-formalization

## Project

Lean 4 (v4.28.0) + Mathlib formalization of the Creative Determinant framework.
Models autopoietic closure as a nonlinear elliptic BVP on a compact Riemannian
manifold. Fifteen theorems proved with zero sorry. Five classical PDE results
axiomatized via the `PDEInfra` typeclass (Schaefer, Schauder, maximum principle,
Amann iteration, fixed-point nonnegativity).

## Build & verify

```bash
lake build --wfail      # primary check — warnings are errors
lake lint                # Mathlib linter suite
lake build CdFormal.Verify  # axiom dashboard (#print axioms)
```

Pre-commit hooks enforce: trailing whitespace, EOF newline, merge conflicts,
copyright headers on all `.lean` files.

## Lean style (Mathlib conventions)

### Naming

- **Prop terms** (theorems): `snake_case` — `mul_comm`, `rpow_le_of_mul_rpow_le`
- **Types/Props/Sorts** (structures): `UpperCamelCase` — `SemioticBVP`, `IsWeakCoherentConfiguration`
- **Other Type terms**: `lowerCamelCase` — `viabilityThreshold`, `canonicalViability`
- **UpperCamelCase inside snake_case**: becomes `lowerCamelCase` — `neZero_iff` not `NeZero_iff`
- **Conclusion-first**: `lt_of_le_of_ne` (conclusion `lt`, hypotheses `le` and `ne`)
- **`_of_` pattern**: hypotheses joined by `_of_` in order: `C_of_A_of_B` for `A → B → C`
- **American English**: `factorization` not `factorisation`

### Formatting

- **100-char line limit** (linter-enforced)
- **`by` at end of preceding line**, never on its own line
- **2-space indent** for proof bodies; **4-space** for multi-line statements
- **No empty lines** inside declarations (linter-enforced)
- **Focusing dots** `·` flush with current indent, tactics indented beneath
- **`:`, `:=`, infix ops** at end of line, not start of next
- **`fun x ↦`** not `λ x ↦`; **no `$`** (use `<|` if needed)

### Tactics

| Goal type | Preferred tactic |
|-----------|-----------------|
| Linear ℕ/ℤ arithmetic | `omega` |
| Numerical evaluation | `norm_num` |
| Decidable props | `decide` |
| Positivity (0 ≤ x, 0 < x) | `positivity` |
| Monotonicity/congruence | `gcongr` |
| General simplification | `simp` (last resort) |
| Nonlinear arithmetic | `nlinarith [hint]` |
| Field algebra | `field_simp` then `ring` or `linarith` |
| Real powers | `Real.rpow_*` lemmas; `rw [Real.rpow_sub_one]` for `v^(p-1)` |

- **Terminal `simp`**: do NOT squeeze (maintenance burden from lemma renames)
- **Non-terminal `simp`**: MUST be `simp only [...]`
- **One tactic per line** (semicolons only for short single-idea sequences)

### Attributes

- `@[simp]`: equations/iff where LHS is more complex than RHS; must not loop
- `@[ext]`: extensionality lemmas
- `@[simps]`: auto-generate projection simp lemmas for structures
- `@[gcongr]`: congruence lemmas of form `f x₁ ∼ f x₂` given `x₁ ∼ x₂`

### Types and definitions

- **`Type*`** not `Type _` (performance requirement)
- **`where` syntax** for instances, not braces
- **`variable` blocks** for shared parameters — don't repeat `{n : ℕ} {M : Type*}`
- **Hypotheses left of colon** — `(h : 1 < n) : 0 < n` not `: 1 < n → 0 < n`
- **`abbrev`** (reducible) requires justification; `@[irreducible]` requires justification
- **Classical by default** — don't thread `Decidable` instances unless the type requires them

### Documentation

- **Module docstring** (`/-! ... -/`) required after imports: title, summary,
  Main definitions, Main statements, Implementation notes, References, Tags
- **Definition docstrings** (`/-- ... -/`) required on every `def` (linter: `docBlame`)
- **References**: cite as `[AuthorYear]`, e.g. `[GilbargTrudinger2001]`, `[Amann1976]`

### Imports

- **Granular imports only** — never `import Mathlib`
- Import hierarchy: Algebra → Order → Topology → Analysis (no cross-category violations)
- Files under ~1000 lines; split along natural boundaries

## Aristotle prover

**Role: leaf-lemma grinder and dependency detector, not theorem architect.**

### When to use

- Algebraic reshaping (e.g. `bv ≥ cv^p → v^{p-1} ≤ b/c`)
- Positivity/nonzeroness, rpow simplification, division algebra
- High success on algebraic/order-theoretic leaves

### When NOT to use

- Headline theorems, design decisions, anything where definitions are still moving
- If you can't explain in one sentence why the lemma is true, don't submit it

### Submission protocol

1. **Freeze the statement** — hand-design def + statement, compile to sorry, then submit
2. **Each sorry = one leaf** — one concept, one obvious target, short dependency cone
3. **Proof-shaped files** — short helpers first, named intermediates, minimal imports
4. **Batch by type**: positivity → algebra → rpow → order theory → cleanup
5. **`prove_file` with `wait=False`** — runs take minutes to hours; don't poll in tight loops

### Output handling

- Keep the statement, keep discovered dependencies
- **Rewrite proof into clean human-owned form** — Aristotle output is draft, not scripture
- Artifacts go to `artifacts/aristotle/*.lean` (outside build tree, gitignored from lint)

### Known limitations

- Aristotle runs Lean 4.24.0 — outputs may not compile on our 4.28.0
- Sometimes generates `exact?` (interactive-only tactic) — rewrite manually
- Do NOT use `axiom` to provide upstream lemmas — shadows function definitions

## Hard-won API gotchas

### Real.rpow

- `Real.rpow_sub_one (hv : v ≠ 0) : v ^ (p - 1) = v ^ p / v` — key for L∞ algebra
- `Real.rpow_le_rpow` requires `0 ≤ base` and `0 ≤ exponent`
- `Real.rpow_mul (hx : 0 ≤ x)` — exponent product rule needs nonneg base
- `one_div_nonneg.mpr` to prove `0 ≤ 1/(p-1)` from `0 < p-1`

### Bornology / Compactness

- `Bornology.IsVonNBounded ℝ S` — Mathlib's bornological bounded sets
- `IsCompact (closure (T '' S))` — compact image characterization
- These are used in the `T_compact` axiom (PDEInfra typeclass)

### Structure field axioms

- `SemioticOperators` fields (`laplacian_add`, `laplacian_smul`, `gradNorm_nonneg`,
  `gradNorm_smul`, `gradNorm_const`) are **axioms** — proved consequences go in
  `OperatorLemmas.lean` and `CoefficientLemmas.lean`
- `gradNorm_const` was added after Aristotle couldn't derive it — it IS needed as an axiom

### OrderHom / CompleteLattice

- `OrderHom.nextFixed` — Knaster-Tarski iterative construction
- Need `CompleteLattice α` for `OrderHom.nextFixed_le_of_le`
- The `Prop` instance is `Prop.instCompleteLattice` (auto-derived)

## Variable naming

- **Never shadow prelude names**: don't use `le`, `lt`, `eq`, `ne` as variable names
- Standard parameters: `{n : ℕ} {M : Type*}`, `[SemioticManifold n M]`
- `ops : SemioticOperators n M` — abstract PDE operators
- `ctx : SemioticContext n M` — coefficient fields (a, b, c, p)
- `bvp : SemioticBVP n M` — full boundary value problem
- `solOp : SolutionOperator bvp` — solution operator T
- `infra : PDEInfra bvp solOp` — PDE infrastructure axioms
- `Φ` or `Phi` — solutions (weak coherent configurations)

## File structure

| File | Role | Status |
|------|------|--------|
| `Basic.lean` | SemioticManifold, SemioticContext, SemioticBVP, operators | Definitions |
| `Axioms.lean` | PDEInfra typeclass (5 axioms), SolutionOperator, PrincipalEigendata | Axioms |
| `Theorems.lean` | Existence + nontriviality theorems, spectral characterization | Proved |
| `OperatorLemmas.lean` | Δ(0)=0, Δ linear, \|∇0\|=0 | Proved |
| `CoefficientLemmas.lean` | a(x)≥0, a(x)≤1, p-1>0 | Proved |
| `ScalingUniqueness.lean` | kΦ with k>1 is impossible | Proved |
| `LinftyAlgebraic.lean` | bv≥cv^p ⟹ v≤(b/c)^{1/(p-1)} | Proved |
| `MonotoneFixedPoint.lean` | Knaster-Tarski between sub/super-fixed points | Proved |
| `Verify.lean` | Axiom dashboard (#print axioms, 17 declarations) | Dashboard |

## Axiom boundary (PDEInfra)

| Field | Paper Ref | Classical Source |
|-------|-----------|-----------------|
| `T_compact` | Lemma 3.7 | Schauder + Arzelà-Ascoli |
| `linfty_bound` | Lemma 3.10 | Maximum principle (Gilbarg-Trudinger) |
| `schaefer` | Thm 3.12 | Schaefer 1955 |
| `fixed_point_nonneg` | Thm 3.12 | Strong maximum principle |
| `monotone_iteration` | Thm 3.16 | Amann 1976 |

`T_compact` uses bornological vocabulary (`IsVonNBounded → IsCompact`).
The `schaefer` axiom takes `T_compact` as an explicit hypothesis.

## Workflow rules

- **No sorries on main** — every theorem fully proved before shipping
- **Internal docs** (`docs/internal/`) are NOT committed to git
- **Commit messages**: substantive, not ceremonial
- Feature branches merge to main via fast-forward; delete after merge
- **Mathlib PR process**: post to Zulip first, small PRs preferred, AI disclosure required
