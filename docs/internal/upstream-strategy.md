# Upstream Strategy: Two-Track Plan

Based on GPT-5.4 senior Mathlib maintainer review (2026-03-05).

---

## Track 1: Upstream Candidates (reusable algebraic lemmas)

These results have zero PDEInfra dependency, are pure algebra/analysis, and
could live in Mathlib with neutral (non-paper-specific) names.

### Candidate 1: `spectral_characterization_1d`

**Current**: Proves that β > (π/L)²/b implies (π/L)² - βb < 0.

**Neutral statement**: For any a, b > 0, if x > a/b then a - xb < 0. This is
trivial linear algebra. The interesting part is the *context* — connecting it
to the principal eigenvalue of -Δ - βb on [0,L] with Dirichlet conditions.

**Mathlib home**: `Mathlib.Analysis.SpecialFunctions.Trigonometric` or a new
file under `Mathlib.Analysis.ODE.SturmLiouville` if that namespace exists.

**Neutral name**: `sub_neg_of_div_lt` or `eigenvalue_neg_of_gt_threshold` if
contextualized with Sturm-Liouville theory.

**Blocker**: The lemma itself is almost too simple for a standalone Mathlib PR.
It's really a corollary of `div_lt_iff`. The value is in connecting it to
eigenvalue theory, which requires Courant-Fischer (not in Mathlib).

**Recommendation**: Don't upstream this alone. Wait until there's enough
Sturm-Liouville infrastructure to make it part of a meaningful PR.

### Candidate 2: `scaling_algebraic_contradiction`

**Current**: Proves False from k > 1, p > 1, c > 0, Φ > 0, and
-c·k·Φ^p ≤ -c·k^p·Φ^p (i.e., k ≥ k^p is contradicted by k < k^p).

**Neutral statement**: For k > 1 and p > 1, k < k^p. This is
`Real.rpow_lt_rpow_of_exponent_lt` composed with `rpow_one`.

**Mathlib home**: Could be a simp lemma or a named lemma near
`Mathlib.Analysis.SpecialFunctions.Pow.Real`.

**Neutral name**: `lt_rpow_self_of_one_lt` or similar.

**Blocker**: The core fact (`rpow_lt_rpow_of_exponent_lt`) is already in
Mathlib. Our lemma is a 3-line consequence. Might be welcome as a `@[simp]`
lemma if the statement is clean enough.

**Recommendation**: Check if `k < k ^ p` for `1 < k` and `1 < p` exists in
Mathlib already. If not, this is a good "single lemma" PR candidate. Needs
Zulip discussion first.

### Candidate 3: `viabilityThreshold` (definition)

**Current**: `(π/L)² / b` — the critical parameter value.

**Neutral statement**: The principal eigenvalue of -d²/dx² on [0,L] with
Dirichlet conditions is (π/L)². The threshold where (π/L)² - βb = 0 is
β* = (π/L)²/b.

**Blocker**: Same as Candidate 1 — needs Sturm-Liouville context.

**Recommendation**: Bundle with Candidate 1 when eigenvalue infrastructure
exists.

---

## Track 2: Paper-Specific Theory (research package)

These results are inherently tied to the Creative Determinant framework and
should remain in the cd_formalization repo.

### Paper-specific declarations

- `SemioticManifold`, `SemioticContext`, `SemioticOperators`, `SemioticBVP`
- `IsWeakCoherentConfiguration`
- `SemioticContext.a`, `SemioticContext.canonicalViability`
- `SolutionOperator`, `PrincipalEigendata`
- `PDEInfra` typeclass
- `SemioticBVP.exists_isWeakCoherentConfiguration`
- `SemioticBVP.exists_pos_isWeakCoherentConfiguration`

These use domain-specific terminology (care, coherence, contradiction, semiotic
manifold) that is meaningful in the paper's context but not general enough for
Mathlib. They should stay as a research formalization package.

### What makes this package high-quality (maintainer perspective)

1. Explicit axiom boundary via `PDEInfra`
2. Per-theorem dependency annotations (being added)
3. Zero sorry, zero maxHeartbeats overrides
4. Honest documentation about what's proved vs assumed
5. CI enforcement of Mathlib linter conventions

---

## Process: How to upstream

1. **Zulip first**: Post on `#new members` or `#Is there code for X?` to check
   if the result already exists and gauge interest.
2. **Small PRs**: One lemma per PR for new contributors.
3. **AI disclosure**: Required in PR description — which tool, how used,
   contributor vouches for understanding all code.
4. **Neutral naming**: Strip all paper-specific terminology.
5. **Review culture**: Anyone can review; helpful reviews build reputation.

---

## Zulip Engagement Plan

### Post 1: Schaefer's Fixed-Point Theorem (channel: `#Is there code for X?`)

**Framing:** Identify a gap, offer to help fill it. Not promoting a project.

**Structure:**
1. Lead with the mathematical gap: "Is there work on Schaefer's fixed-point theorem
   (or Leray-Schauder continuation) in Mathlib?"
2. Note the dependency chain: Brouwer → Schauder → Schaefer. Reference
   existing Sperner's lemma work (#25231) as progress on the chain.
3. Ask the API design question: should nonlinear compact maps extend
   `IsCompactOperator` or be a separate predicate?
4. Mention the concrete downstream use case: we have a PDE formalization
   that currently axiomatizes this step, link to cd-formalization.
5. AI disclosure: "Parts of the formalization were developed with Claude
   (Anthropic) and Aristotle (theorem prover). All code has been manually
   reviewed and understood."

**Tone:** Contributor identifying a gap and asking for guidance. Not an
expert dictating API design.

### Post 2: `k < k^p` simp lemma (channel: `#Is there code for X?`)

**Framing:** Quick check if a specific lemma exists.

**Structure:**
1. "Does Mathlib have `k < k ^ p` for `1 < k` and `1 < p` (real exponents)?
   I can find `Real.rpow_lt_rpow_of_exponent_lt` but not the direct corollary."
2. If missing: "Happy to PR this as a `@[simp]` lemma near
   `Mathlib.Analysis.SpecialFunctions.Pow.Real` if it would be welcome."

**Sequencing:**
- Post 1 (Schaefer) first — establishes presence, starts a real conversation
- Post 2 (`k < k^p`) after — smaller, could become a first PR quickly

### Follow-ups (contingent on Zulip reception)
- If Schaefer discussion is positive → file GitHub issue (from `drafts/mathlib_issue_schaefer.md`)
- If `k < k^p` is missing → draft small PR, reference Zulip discussion

## Timeline

- **Done**: Per-theorem dependency annotations, Mathlib conventions enforcement
- **Now**: Phase 2 mathematical tightening (Items 6-8)
- **Next**: Zulip Post 1 (Schaefer gap)
- **Then**: Zulip Post 2 (`k < k^p` check)
- **Later**: When Sturm-Liouville or Courant-Fischer lands in Mathlib,
  upstream the eigenvalue threshold results
- **Eventually**: Replace PDEInfra axioms with actual proofs as Mathlib's
  PDE infrastructure grows
