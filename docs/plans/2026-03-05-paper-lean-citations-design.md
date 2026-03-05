# Paper Update: Lean Verification Citations — Design

**Goal:** Update `paper/creative_determinant.tex` to accurately reflect the current
Lean 4 formalization, with a verification appendix following math journal conventions.

**Architecture:** Three targeted changes to one file. No restructuring of mathematical
content. Appendix before bibliography (standard math journal placement).

---

## Change 1: Update introduction paragraph (line 91)

Current paragraph mentions only 2 proved results (spectral characterization, scaling
algebraic lemma). Update to reflect:
- 11 proved theorems across 4 dependency tiers
- The `T_continuous_compact : True` placeholder disclosure
- Proper `\cite{}` for Lean 4, Mathlib, and formalization repo (replacing bare `\url{}`)

Keep to one paragraph. This is the introduction, not the appendix.

## Change 2: Add bibliography entries to `cd_refs.bib`

- Lean 4: de Moura & Ullrich, 2021
- Mathlib: mathlib community, 2020+
- Formalization repo: Spence, 2026

Replace bare `\url{}` on line 91 with `\cite{Spence2026Lean}` or similar.

## Change 3: Add Appendix A before bibliography (between line 767 and line 769)

### A.1 Verification Overview
3-4 sentences: Lean 4.28.0, Mathlib v4.28.0, `lake build --wfail`, zero sorry,
13 axiom-checked declarations via `#print axioms`, CI enforcement.

### A.2 Paper-to-Lean Alignment Table
Every numbered definition, lemma, theorem, proposition mapped to Lean name.
Columns: Paper Ref | Lean Declaration | File | Status.
Status values: Proved, Proved (conditional on PDEInfra), Axiom, Definition,
Not formalized. ~27 rows.

### A.3 Axiom Boundary (PDEInfra)
Table of 5 PDEInfra fields. Columns: Axiom | Classical Source | Mathlib Status.
Brief prose on why axiomatized and path to replacing them.

---

## What we are NOT doing

- No inline annotations on theorems
- No changes to mathematical content (Sections 2-5)
- No new `\label{}` tags
- No numerical validation appendix

## Key file paths

- Paper: `paper/creative_determinant.tex`
- Bibliography: `paper/cd_refs.bib`
- Lean source (for reference): `cd_formalization/CdFormal/*.lean`
