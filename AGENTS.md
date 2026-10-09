# AGENTS.md — cd-formalization

Conventions for this repo: the shared Lean 4 + Mathlib conventions of the Project Navi
formalization repos, plus what is specific to cd. Task-specific proof obligations take
precedence over these generic conventions. Keep the Lean formalization repos on one Lean and
Mathlib release where possible, so lemmas can be ported between them without a bump. This
repo pins `v4.28.0`; fd-formalization has moved to `v4.34.1`, and the notes under *Moving to
v4.34.1* record what that bump changed. API notes below were checked against `v4.28.0`;
re-check them after a bump.

## This project

A formalization of the existence theory for the Creative Determinant problem
−ΔΦ = a|∇Φ| + bΦ − c(Φ₊)ᵖ in M, Φ = 0 on ∂M, with a = κγμ and p > 1.

- **Continuum results are conditional.** `SemioticBVP.exists_isWeakCoherentConfiguration`
  assumes `PDEInfra`, `SolutionOperator` and an upper bound `B` on `b` (`hB`);
  `SemioticBVP.exists_pos_isWeakCoherentConfiguration` assumes `PDEInfra`,
  `SolutionOperator` and supplied `PrincipalEigendata` with a negative eigenvalue. The
  manifold's Laplacian, gradient norm and boundary are abstract data. See *Assumed results*.
- **Finite-graph results assume no unproved result.** `SemioticGraph.exists_pos_graph`
  (`CdFormal/Graph/`) constructs the operators, the principal eigendata and the fixed point
  from concrete data. It holds under `hconn`, `hdom` and `hneg`: a connected interior graph,
  the edge condition and a negative principal eigenvalue.
  `SemioticGraph.exists_pos_graph_of_unweighted` replaces `hdom` with weights in {0, 1}.
- The graph discretization was chosen for this formalization. Do not describe it as matching
  the continuum problem or any deployed model: no relation between them is formalized.

## Invariants

- **No `sorry` in the library on the default branch.** Every declaration under `CdFormal/` is
  fully proved before merge. The statement files under `spec/` are the one exception: each
  restates a headline result with `sorry` as its proof, and CI requires that.
- **No `axiom` declarations.** Classical results that are not proved are assumed through a
  typeclass or structure field (see *Assumed results*, which needs approval), never
  through `axiom`.
- **Axiom allowlist**: every public result depends only on `propext`, `Classical.choice`
  and `Quot.sound`. Anything else, including `sorryAx`, is a failure.
- **Every module compiles.** `lake build` builds only what the root imports, so a file
  nobody imports is never checked and can rot silently. CI builds every tracked module.
- **The assumption boundary is fixed.** Do not add, strengthen or weaken a `PDEInfra`,
  `SolutionOperator` or `PrincipalEigendata` field; the one allowed change is discharging a
  field, as described under *Assumed results*. Do not let a finite-graph result depend on any
  of them. The only hypotheses of `SemioticGraph.exists_pos_graph` are
  connectivity of the interior graph, the edge condition `hdom` (the one extra hypothesis
  approved for it) and a negative principal eigenvalue; keep it that way.
- **Assumption changes require approval.** Never complete an assigned proof by adding an
  unproved hypothesis, infrastructure field, or equivalent assumption unless the task
  explicitly authorizes a conditional result. A clean axiom report does not discharge
  theorem hypotheses. Report the complete theorem signature and any remaining assumed
  mathematical results.
- **No vacuous assumptions.** Never encode an open problem or a missing proof as `True`,
  an unconstrained `Nonempty` witness, or an arbitrary `Type` the model gets to choose.
  An assumption is a concrete proposition about the actual mathematical objects, or it is
  not there.

## Build & verify

```bash
lake exe cache get                                   # Mathlib oleans; never build Mathlib
lake build --wfail                                   # warnings are errors (includes sorry)
lake lint                                            # Mathlib environment linters
lake env lean -DwarningAsError=true <Pkg>/Verify.lean   # axiom dashboard
lake build Spec && lake env lean spec/Check.lean        # statement files against the library
```

- `CdFormal/Verify.lean` holds exactly one `#print axioms` record per selected declaration:
  every headline result and the supporting declarations the docs cite. The headline results
  are listed once, in the CI workflow (`HEADLINE_RESULTS`), not in `Verify.lean` or `spec/`,
  so dropping one from the dashboard or from the statement files fails CI. Add a new headline
  result to all three: the workflow list, a `#print axioms` record, and a statement in
  `spec/Spec.lean` copied from the source with its proof replaced by `sorry`. Every record may
  use only `propext`, `Classical.choice` and `Quot.sound`.
- `spec/` holds `Spec.lean` and `Check.lean` only; CI rejects any other file there. The only
  messages `spec/Spec.lean` may produce are its own `sorry` warnings, read by CI as Lean's JSON
  messages with the package's linters on.
- A statement file states; it does not prove. `spec/Check.lean` rejects a statement whose proof
  is not `sorry`, a statement whose type differs from the library declaration of the same name
  (binder names and annotations aside), a library declaration that is not a theorem, and a
  library proof whose axioms leave the allowlist.
- If the sandbox cannot install Lean or fetch the Mathlib cache, push to a draft PR and
  let CI build and verify. Report which checks ran where; never claim a local build that
  did not happen.
- Audit for placeholders: `rg -n '\bsorry\b|sorryAx' <Pkg>` must return nothing, even in
  comments; CI runs the same check.
- Independent kernel replay: `lake env leanchecker --fresh <Pkg>` re-checks every
  declaration in a fresh kernel, outside the elaborator that produced it.
- Test the checkers themselves. An axiom or `sorry` gate that silently passes is worse than
  none (a pipe without `pipefail` once hid Lean failures here). When you add or change a
  gate, also add a small negative fixture that must fail it and a snapshot of expected
  axiom output that its parser must accept. In this repo's CI only the environment check
  carries a fixture (an `axiom` and an `opaque` constant it must report). After changing the
  axiom dashboard parser, the statement-file comparator or the audit, test them by hand: a
  file that uses `sorry`, a statement with a changed hypothesis, a statement proved instead
  of stated, and a library proof that uses native evaluation (which declares an auxiliary
  axiom under Lean v4.34.1).
- Change `lake-manifest.json` only in an intentional dependency bump. No CI guard enforces
  this here; check the diff yourself.
- If a repo has a docs site, `uv run zensical build` must succeed; CI also checks the
  built site's local links.
- This repo's CI runs:
  - a module check: every tracked `CdFormal/*.lean` module is imported by `CdFormal.lean`;
  - `lake build --wfail` of the root and every module, then `lake lint`;
  - the axiom check: the selection includes every headline result, one record each, all
    within the allowlist;
  - the statement-file check: every headline result has a statement in `spec/Spec.lean`, and
    every statement there matches its library declaration as described above;
  - the documented-names check: every inline-code token in the README and docs that looks
    like a Lean name containing an uppercase letter, `_` or `.`, and every declaration shown
    in a Lean code block there, must resolve (all-lowercase names are not checked);
  - the header check: every file has the copyright header and a module docstring after the
    imports (Lean itself rejects an `import` after any command, so imports come first);
  - the placeholder audit: no `sorry` or `sorryAx` anywhere in the library sources, comments
    included (a text search; `spec/` is outside it by design);
  - the environment check: no module of the library declares an `axiom` or an `opaque`
    constant, read from the compiled environment, after a self-test with a fixture that
    declares both;
  - the docs build, and a link check that also verifies fragments.
  Everything else in this file is a convention to follow, not an automated gate.
- If a repo has a `Makefile`, use its targets (`build`, `verify`, `audit`, `lint`) as
  the canonical commands.

## Project configuration

- Lean options live in `lakefile.toml` `[leanOptions]`, the single source of truth. Do
  not add per-file `set_option` for them.
  ```toml
  [leanOptions]
  pp.unicode.fun = true
  relaxedAutoImplicit = false
  autoImplicit = false
  maxHeartbeats = 200000
  weak.linter.mathlibStandardSet = true
  linter.style.longLine = true
  linter.style.lambdaSyntax = true
  linter.style.dollarSyntax = true
  linter.style.cdot = true
  linter.style.missingEnd = true
  ```
  Don't add per-file `set_option` lines for these: they are redundant, and from v4.34 the
  header linter rejects them.
- `lintDriver = "batteries/runLinter"`.
- Mathlib is required at a release tag (`rev = "v4.28.0"`), with no local fork and no
  `require` overrides. Bump only when a needed API landed or changed.
- A Lake dependency on another formalization repo pins a commit, not a branch. Bump it
  deliberately, after that commit builds cleanly and its axiom report is clean, and keep
  both repos on the same Lean and Mathlib pin.

## File layout

Every `.lean` file, in order:

1. Copyright header, matching the repository's `LICENSE` and actual contributors (the
   example below is this repo's; list every author of the file and keep existing credit):
   ```lean
   /-
   Copyright (c) 2026 Nelson Spence. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Nelson Spence
   -/
   ```
2. Granular imports. **Never `import Mathlib`.**
3. Module docstring `/-! ... -/`: title, summary, `## Main definitions`,
   `## Main statements`, `## Implementation notes`, `## References`, `## Tags`.

- Keep files under ~1000 lines and split along natural boundaries.
- Respect the import hierarchy: Algebra → Order → Topology → Analysis.
- Mathlib's module system: a repo that has adopted it starts every file with `module`,
  uses `public import`, and wraps exposed definitions in `@[expose] public section`.
  Adoption is repo-wide and happens in one change; don't mix header styles in one repo.
- Keep general-purpose results apart from project-specific ones. General lemmas live in
  their own directory under Mathlib-style namespaces, depend only on Mathlib and each
  other, and never import the project-specific layer. Once a repo has both layers, add a
  CI check on the import direction. This repo has no separate general-purpose layer: the
  continuum development is in `CdFormal/` and the finite-graph development in
  `CdFormal/Graph/`. New general-purpose declarations go in Mathlib-style namespaces;
  existing root-namespace lemmas such as `monotone_fixed_point_between` are cited by the docs
  and CI, so don't rename them without approval.
- Unfinished or exploratory work lives in an `Experimental/` directory. Only
  `Experimental/` and `Verify/` may import it; add a CI check for that when the directory
  first appears. This repo has none.
- Every `def` has a `/-- ... -/` docstring (the `docBlame` linter checks this).
- Cite references as `[AuthorYear]`.

## Naming (Mathlib)

- Theorems (Prop terms): `snake_case`, e.g. `viabilityThreshold_lt_iff`.
- Types, structures, classes, Props-as-types: `UpperCamelCase`.
- Other terms (defs, functions, instances): `lowerCamelCase`.
- An UpperCamelCase name inside snake_case becomes lowerCamelCase: `neZero_iff`, not
  `NeZero_iff`.
- Conclusion first, hypotheses joined by `_of_` in order: `C_of_A_of_B` for `A → B → C`.
- American English (`factorization`).
- No Greek letters in new declaration names; spell them out (`sigma`, not `σ`). The
  coefficient fields `κ`, `γ`, `μ` and their `_bounds` fields keep the paper's notation.
- Name instances explicitly: `instance instFintypeFoo : Fintype Foo`.
- Never shadow prelude names with variables (`le`, `lt`, `eq`, `ne`).
- Fix one set of standard parameter names per repo and declare them in `variable` blocks.

## Formatting

- 100-character lines.
- `by` at the end of the preceding line, never on its own line.
- 2-space indent for proof bodies; 4-space for continuation lines of a statement.
- No blank lines inside a declaration.
- Focusing dots `·` flush with the current indent, with the tactics beneath them.
- `:`, `:=` and infix operators end a line; they don't start the next one.
- `fun x ↦`, not `λ`. No `$`; use `<|`.
- One tactic per line. Semicolons are only for a short sequence that expresses one idea.

## Definitions and statements

- `Type*`, not `Type _`.
- `where` syntax for instances, not braces.
- Hypotheses go left of the colon: `(h : 1 < n) : 0 < n`, not `: 1 < n → 0 < n`.
- `abbrev` and `@[irreducible]` each need a stated justification.
- Classical by default. Don't thread `Decidable` instances unless the type demands them.
- Order definition arguments to match the API lemmas you'll use, e.g.
  `{v | G.edist v c < r}` if the lemmas put the varying argument first, so downstream
  proofs don't need `symm`/`comm`.
- If a construction has distinguished points, make them definitionally where the API
  expects them, e.g. build an equivalence to `Fin n` by hand so they land at known indices.
  `Fintype.equivFinOfCardEq` scatters them to unknown indices.

## Attributes

- `@[simp]` on equations or iffs whose LHS is more complex than the RHS. It must not loop.
- `@[ext]` on extensionality lemmas; `@[simps]` for structure projections.
- `@[gcongr]` on congruence lemmas of the form `f x₁ ∼ f x₂` given `x₁ ∼ x₂`.
- Every new `@[simp]`, `@[ext]` or `@[aesop]` attribute gets a one-line comment saying why.
  No project-local `@[aesop]` rules in general-purpose files.

## Tactics

| Goal | Reach for |
|------|-----------|
| Linear ℕ/ℤ arithmetic | `omega` |
| Numerals | `norm_num` |
| Decidable props | `decide` |
| `0 ≤ x`, `0 < x` | `positivity` |
| Monotonicity / congruence | `gcongr` |
| Nonlinear arithmetic | `nlinarith [hints]` |
| ℕ subtraction | `zify [h₁, h₂]` first |
| Field algebra | `field_simp`, then `ring` or `linarith` |
| General rewriting | `simp` (last resort) |

- A terminal `simp` stays unsqueezed, since squeezed lists break on lemma renames.
- A non-terminal `simp` must be `simp only [...]`.
- `aesop` only with explicit local rule sets, or replaced by the script `aesop?` produces.
  Flag any non-terminal `ring_nf`; its normal form changes between Mathlib versions.
- For set equality, `ext v; simp [...]` is canonical. Skip `ext` when `simp` alone closes
  it. Don't hand-build `constructor`/`rcases`/`absurd` chains.
- `simp` with commutativity lemmas (`adj_comm`, `or_comm`) often closes goals that look
  like they need `tauto`.
- Write `.rfl`, not `Iff.rfl`. Prefer a named lemma to `show _ from rfl`, e.g.
  `one_add_one_eq_two.symm`.
- When a `simp` call leaves an unexpected residual goal, an explicit
  `rw [defn, lemma₁, lemma₂]` chain is often more robust.
- `exact?`, `apply?` and `simp?` are for exploration only. Never commit them.

## API notes (Mathlib v4.28.0)

**Casts**
- After `Nat.cast_sub`, normalize with `simp only [Nat.cast_ofNat, Nat.cast_one]` before
  `linarith` can close the goal.
- `exact_mod_cast` settles `↑n` vs `n` mismatches.
- `Nat.cast_pos : 0 < (↑n : R) ↔ 0 < n`.
- `tendsto_natCast_atTop_atTop` needs an explicit `(R := ℝ)`.

**ℕ and `Fin`**
- `ring` does not close `a * a ^ n = a ^ (n + 1)` on ℕ. Use `rw [pow_succ, mul_comm]`.
- `omega` does not see `Fin` value facts. State them first, e.g.
  `have : (j.succ : ℕ) = j + 1 := Fin.val_succ j`. The same goes for `(⟨m, h⟩ : Fin n).val`
  inside a lemma's statement: restate the lemma with `m` so the value reduces.
- Division by a variable is an opaque atom for `omega`, and two spellings of one quotient
  are two atoms. `generalize` the quotient in the goal and its facts before `omega`.
- `i ≤ 0` on `Fin` to `i = 0`: `Fin.le_zero_iff.mp`, not `ext; omega`.
- `Function.iterate_succ_apply'` unfolds `f^[n+1] x = f (f^[n] x)` from the right.

**Real analysis**
- `Real.log 0 = 0`, so positivity side conditions are load-bearing.
- `Real.log_pow : log (x ^ n) = n * log x`; `Real.log_pos : 1 < x → 0 < log x`.
- `Real.rpow_sub_one (hv : v ≠ 0) : v ^ (p - 1) = v ^ p / v`.
- `Real.rpow_le_rpow` needs `0 ≤ base` and `0 ≤ exponent`; `Real.rpow_mul` needs `0 ≤ x`.
- `one_div_nonneg.mpr` gives `0 ≤ 1 / (p - 1)` from `0 < p - 1`.
- `ContDiff` at `n = ⊤` reduces to an existential, so dot notation (`.comp`) fails. Call
  `ContDiff.comp hg hf` as a function.
- `ContDiff.continuous_fderiv` takes `(hn : n ≠ 0)`, not `1 ≤ n`. Discharge it with
  `(by decide)`.
- `LinearMap.isUnit_iff_ker_eq_bot` needs the `LinearMap.` prefix.
- There is no standalone `continuous_det`; `grind +suggestions` can derive it.

**Filters**
- `Tendsto.squeeze'` argument order: lower tendsto, upper tendsto, lower eventually,
  upper eventually.
- `Tendsto.atTop_mul_const` takes the positivity proof first, then the tendsto.
- Standard pattern: `filter_upwards [eventually_gt_atTop 0] with g hg`.

**Graphs, order, dynamics**
- `SimpleGraph.mk` needs the `Std.Symmetric` / `Std.Irrefl` wrappers, not a raw `∀`.
  `SimpleGraph.fromRel` (used by `interiorGraph`) symmetrizes for you and avoids them.
- `pathGraph` exists, but Mathlib has no distance lemmas for it.
- `OrderHom.nextFixed` (Knaster–Tarski) needs `CompleteLattice α`.
- Periodic points live in `Dynamics.PeriodicPts.Defs` (`Function.minimalPeriod`,
  `Function.IsPeriodicPt`), not `GroupTheory.OrderOfElement`.

**Probability and information theory**
- `PMF` coerces through `FunLike`; there is no `PMF.apply` lemma, so write `p a`.
  `PMF.tsum_coe : ∑' a, p a = 1`. `PMF.uniformOfFinset` is in
  `Mathlib.Probability.Distributions.Uniform`.
- `ENNReal.toReal_rpow x z : x.toReal ^ z = (x ^ z).toReal` holds with no side
  conditions; use `.symm` to push `toReal` outward.
- `μ ≪ ν` is scoped notation: `open MeasureTheory` wherever it appears.
- `InformationTheory.klDiv` is an `irreducible_def`: work through its API
  (`klDiv_of_ac_of_integrable`, `klDiv_eq_zero_iff`, `toReal_klDiv`,
  `klDiv_eq_integral_klFun`), never by unfolding.
- Logarithms are `Real.log` (natural log) only. Convert bases at the statement level.

**Moving to v4.34.1** (found in fd-formalization's bump from v4.28.0; expect the same here)
- `SimpleGraph.mk` takes `Std.Symm` and `Std.Irrefl` structures: wrap each proof in `⟨...⟩`.
- Mathlib has `SimpleGraph.ball c r = {v | G.edist v c < r}` (since v4.30.0); the centre
  lemma is `mem_ball_self`.
- `dif_pos` / `dif_neg` are deprecated; `dite_eq_left` / `dite_eq_right` have the same
  statements.
- `Mathlib.Data.Real.Basic` moved to `Mathlib.Basic.Real.Basic`; `ENat.toNat_coe` is
  `ENat.toNat_natCast`.
- The header linter checks every file: the module docstring must follow the imports
  directly, so per-file `set_option` lines above it fail the build.
- `simp` does not unfold a type defined with `def` (for example a `def` that is a `Sum`). An
  equality it leaves between terms that differ only in proofs needs a final `rfl`, and
  `Sum.inl ≠ Sum.inr` at such a type needs `Sum.inl_ne_inr`.
- A term that equals another only after unfolding a definition (in fd, `embed hub0` and the
  next generation's `hub0`) breaks `rw` ("motive is not type correct") in goals whose walks
  mention it. Add the `rfl` lemma,
  move the walk with `Walk.copy`, or prove the arithmetic for an arbitrary length and apply
  it to the walk's length.
- Using `show` to change the goal is flagged by a linter; use `change`.
- `ring` may no longer be imported transitively; import `Mathlib.Tactic.Ring` or avoid it.

**Measure and dimension**
- Area formula: `MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv` in
  `Mathlib.MeasureTheory.Function.Jacobian`.
- `dimH`, `ContDiffOn.dimH_image_le` and `hausdorffMeasure_of_dimH_lt` are in
  `Mathlib.Topology.MetricSpace.HausdorffDimension`.
- `absolutelyContinuous_isAddHaarMeasure` is in `Mathlib.MeasureTheory.Measure.Haar.Unique`.
- Bounded sets: `Bornology.IsVonNBounded ℝ S`.

## Assumed results

Only when the task explicitly authorizes a conditional result (see *Invariants*). When a
classical result is too large to prove in the repo, assume it explicitly and keep the
boundary visible:

- Bundle the assumptions as fields of a typeclass or structure (an `…Infra` class),
  one field per classical result, each with a docstring naming its source.
- Theorems take the class as a hypothesis, so every dependency is visible in the
  signature and `#print axioms` stays clean.
- Put the consequences you prove from the fields in separate lemma files. Only add a
  field when it provably cannot be derived from the existing ones.
- Keep proof trees that don't need the assumptions free of any import of the class.

In this repo the boundary is `CdFormal/Axioms.lean`, and `docs/explanation/axiom-boundary.md`
must describe it exactly:

| Field | Classical source |
|---|---|
| `PDEInfra.T_compact` | Schauder estimates, Arzelà–Ascoli |
| `PDEInfra.linfty_bound` | Maximum principle |
| `PDEInfra.schaefer` | Schaefer's fixed-point theorem [Schaefer1955] |
| `PDEInfra.fixed_point_nonneg` | Maximum principle |
| `PDEInfra.monotone_iteration` | Sub/super-solution iteration [Amann1976] |
| `PrincipalEigendata` | Krein–Rutman or variational theory |

`SolutionOperator` supplies an operator `T` with two assumed properties:
`SolutionOperator.T_boundary` (`T u` vanishes on the boundary) and
`SolutionOperator.T_fixed_point` (fixed points of `T` are solutions). The axiom check cannot
see these hypotheses, so every statement of a continuum result, in the docs and
docstrings, must name them. Discharging a field means proving it from Mathlib and removing
it from the class, not adding a new assumption in its place.

## Documentation must match the code

- CI resolves the Lean names in the README and docs (inline names containing an uppercase
  letter, `_` or `.`, and declarations shown in Lean code blocks), so renaming a declaration
  fails CI until the docs follow.
- Every Lean name that appears in the README or docs must resolve. Check this
  mechanically by generating a file of `#check @Name` lines and running
  `lake env lean` on it.
- State hypotheses exactly as in the theorem (e.g. `1 < u`, `u ≤ v`), and state what is
  **not** formalized. Never let a theorem name or summary claim more than the
  statement proves.
- Keep a short list of public names (the headline results) and make sure `Verify.lean`
  covers all of them.

## Scope and credit

- State the hypotheses of a result wherever the result is mentioned: `1 < p`, `0 < c`, the
  `PDEInfra` hypotheses for continuum results, and `hconn`, `hdom`, `hneg` for the graph
  result. `hdom` is sufficient for the proof, not claimed necessary.
- Credit for the finite-graph formulation and proof route goes to Andrew Edmark (@aedmark),
  as the README words it. The discretization, the Jacobi splitting and the edge condition
  were chosen for this formalization and are not claimed to be his; keep that distinction
  wherever the credit appears.

## Aristotle (automated prover)

Aristotle grinds leaf lemmas and detects dependencies. It is not the theorem architect.

- **Good targets**: cast control (ℕ → ℝ), positivity and nonzeroness, algebraic
  reshaping, `Fin` arithmetic, rpow/log/pow simplification, squeeze bounds,
  recurrence-to-closed-form algebra.
- **Bad targets**: headline theorems, design decisions, anything whose definitions are
  still moving. If you can't say in one sentence why a lemma is true, don't submit it.
- **Protocol**:
  1. Freeze the statement: hand-write the definition and statement, and compile with `sorry`.
  2. One `sorry` per leaf: one concept, an obvious target, a short dependency cone.
  3. Proof-shaped files: short helpers first, named intermediates, minimal imports.
  4. Batch by kind: positivity → algebra → analysis → cleanup.
  5. Submit with `wait=False`. Runs take minutes to hours, so don't poll in a tight loop.
- **Output is a draft.** Keep the statement and any dependencies it discovered, then
  rewrite the proof into clean, human-owned form:
  - Rewrite `import Mathlib` to granular imports.
  - Replace `exact?` with the actual term or tactic.
  - Reject any `axiom` it introduces, since axioms can shadow real definitions.
  - Reject new definitions, global `@[simp]` attributes, `maxHeartbeats` overrides and
    `pp.all`; none of them belongs in a leaf proof.
  - Rebuild with `lake build --wfail`: Aristotle doesn't run the project's style linters.
- Before trusting output, check Aristotle's Lean version against `lean-toolchain`.
- Elaborating a file runs code (`#eval`, `initialize`, tactics, macros), so elaborate a
  returned file in a sandbox before it touches the repository: no network, home directory
  hidden, the project read-only. With bubblewrap, from the project root:

  ```bash
  bwrap --ro-bind /usr /usr --symlink usr/lib /lib --symlink usr/lib /lib64 \
    --symlink usr/bin /bin --ro-bind /etc /etc --tmpfs "$HOME" \
    --ro-bind "$HOME/.elan" "$HOME/.elan" --ro-bind "$PWD" "$PWD" \
    --ro-bind <returned-dir> /untrusted --proc /proc --dev /dev --tmpfs /tmp \
    --unshare-all --die-with-parent --chdir "$PWD" lake env lean /untrusted/<File>.lean
  ```

  Adjust the binds to where elan and the toolchain live on your machine.
- Keep raw prover artifacts and run logs out of the public repository. Commit only the
  rewritten proofs, and credit Aristotle in the README.
