# Paper Lean Verification Citations — Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Update `paper/creative_determinant.tex` with accurate Lean 4 verification citations: updated intro paragraph, bibliography entries, and a new Appendix A with alignment table and axiom boundary.

**Architecture:** Three tasks modifying two files (`paper/creative_determinant.tex` and `paper/cd_refs.bib`). Each task is independently testable via `pdflatex` compilation. No changes to mathematical content.

**Tech Stack:** LaTeX (pdflatex), BibTeX

---

### Task 1: Add bibliography entries to `cd_refs.bib`

**Files:**
- Modify: `paper/cd_refs.bib` (append after the last entry, before EOF)

**Step 1: Add three new bib entries**

Append the following to the end of `paper/cd_refs.bib`, before any trailing whitespace:

```bibtex
% -----------------------------------------------------------------------------
% FORMAL VERIFICATION (Lean 4 / Mathlib)
% -----------------------------------------------------------------------------

@inproceedings{deMoura2021,
  author    = {Leonardo de Moura and Sebastian Ullrich},
  title     = {The {L}ean 4 Theorem Prover and Programming Language},
  booktitle = {Automated Deduction -- CADE 28},
  series    = {Lecture Notes in Computer Science},
  volume    = {12699},
  pages     = {625--635},
  publisher = {Springer},
  year      = {2021}
}

@misc{Mathlib2020,
  author       = {{The mathlib Community}},
  title        = {The {L}ean Mathematical Library},
  howpublished = {\url{https://github.com/leanprover-community/mathlib4}},
  year         = {2020},
  note         = {Accessed 2026}
}

@misc{Spence2026Lean,
  author       = {Nelson Spence},
  title        = {Creative {D}eterminant: {L}ean 4 Formalization},
  howpublished = {\url{https://github.com/Project-Navi/cd-formalization}},
  year         = {2026},
  note         = {Lean 4.28.0, Mathlib v4.28.0. Zero \texttt{sorry}, CI-enforced}
}
```

**Step 2: Verify compilation**

Run from `paper/` directory:
```bash
cd /home/ndspence/GitHub/navi-creative-determinant/paper && pdflatex creative_determinant.tex && bibtex creative_determinant && pdflatex creative_determinant.tex && pdflatex creative_determinant.tex
```
Expected: Compiles without errors. New entries appear in bibliography.

**Step 3: Commit**

```bash
git add paper/cd_refs.bib
git commit -m "refs: add Lean 4, Mathlib, and formalization repo bib entries"
```

---

### Task 2: Update the introduction formal verification paragraph

**Files:**
- Modify: `paper/creative_determinant.tex:90-91`

**Context:** Line 90 is `\subsection*{Formal verification}`. Line 91 is the single paragraph. The paragraph currently mentions only 2 proved results and uses a bare `\url{}`.

**Step 1: Replace line 91**

Replace the entire content of line 91 (the paragraph starting with "The mathematical foundations..." and ending with "...navi-creative-determinant}.") with the following. Keep `\subsection*{Formal verification}` on line 90 unchanged.

```latex
The mathematical foundations of this framework are machine-verified using the Lean~4 theorem prover~\cite{deMoura2021} with the Mathlib library~\cite{Mathlib2020}. The formalization~\cite{Spence2026Lean} covers the semiotic manifold structure, coefficient bounds, the Laplace--Beltrami and gradient-norm operators, the full boundary value problem~\eqref{eq:mainBVP}, and the definition of weak coherent configurations. Eleven theorems are proved without \texttt{sorry} axioms, organized in four dependency tiers: (i)~pure algebra requiring no domain axioms (spectral characterization, scaling contradiction); (ii)~derived operator lemmas from abstract Laplacian linearity and gradient-norm homogeneity; (iii)~coefficient bound lemmas from the $[0,1]$ field constraints; and (iv)~PDE-level results including a scaling uniqueness theorem showing that proportional solutions $k\Phi$ with $k>1$ are impossible. The existence theorems (Theorems~\ref{thm:existenceV1prime} and~\ref{thm:nontrivialV1prime}) are proved in Lean conditional on a \texttt{PDEInfra} typeclass that axiomatizes five classical results from elliptic PDE theory not yet available in Mathlib for abstract Riemannian manifolds: Schaefer's fixed-point theorem, Schauder estimates, the maximum principle, fixed-point nonnegativity, and sub-/super-solution monotone iteration. The compactness-of-$T$ axiom is currently a placeholder (\texttt{True}) since Mathlib lacks H\"older spaces on manifolds; the structural dependency is preserved via a \texttt{True $\to$} hypothesis in the Schaefer axiom. The axiom boundary is explicit: each assumption corresponds to a named classical result, and the \texttt{\#print axioms} command confirms that no \texttt{sorryAx} appears in any verified theorem. A complete paper-to-Lean alignment table is given in Appendix~\ref{app:verification}. All Lean source files, CI pipelines (which fail on any \texttt{sorry} via \texttt{-{}-wfail}), and computational artifacts are available at~\cite{Spence2026Lean}. Numerical validation with $O(h^2)$ grid convergence supplements the formal proofs.
```

**Step 2: Verify compilation**

```bash
cd /home/ndspence/GitHub/navi-creative-determinant/paper && pdflatex creative_determinant.tex
```
Expected: Compiles with a warning about undefined reference `app:verification` (not yet created — that's Task 3). No errors.

**Step 3: Commit**

```bash
git add paper/creative_determinant.tex
git commit -m "paper: update formal verification paragraph with current Lean state"
```

---

### Task 3: Add Appendix A before bibliography

**Files:**
- Modify: `paper/creative_determinant.tex:767-768` (insert between Acknowledgments and `\bibliographystyle`)

**Context:** Line 767 is the Acknowledgments paragraph. Line 768 is blank. Line 769 is `\bibliographystyle{unsrt}`. Insert the appendix between line 768 and line 769.

**Step 1: Insert appendix**

Insert the following block between line 768 (end of Acknowledgments) and line 769 (`\bibliographystyle{unsrt}`):

```latex

\appendix
\section{Formal Verification Details}\label{app:verification}

\subsection{Verification overview}

The formalization is implemented in Lean~4.28.0 against Mathlib v4.28.0~\cite{deMoura2021,Mathlib2020}. The build command \texttt{lake build -{}-wfail} fails on any warning, including \texttt{sorry} axioms, ensuring zero silent contamination. Continuous integration enforces this on every commit. The verification module (\texttt{CdFormal/Verify.lean}) runs \texttt{\#print axioms} on every proved theorem; all show only the Lean kernel axioms \texttt{[propext, Classical.choice, Quot.sound]} with no \texttt{sorryAx}. The full source is available at~\cite{Spence2026Lean}.

\subsection{Paper-to-Lean alignment}

Table~\ref{tab:alignment} maps every numbered formal statement in this paper to its Lean~4 counterpart. ``Proved'' means the Lean kernel has verified the proof with no \texttt{sorry}. ``Proved (PDEInfra)'' means the proof is verified but depends on the \texttt{PDEInfra} typeclass axioms described in Section~\ref{sec:axiom_boundary}. ``Definition'' means the declaration type-checks against Mathlib with no proof obligations. ``Not formalized'' means the result is not represented in the Lean codebase (typically interpretive remarks, temporal dynamics, or geometric/operational results outside the PDE core).

\begin{table}[ht]
\centering
\small
\caption{Paper-to-Lean alignment. File paths are relative to \texttt{CdFormal/}.}
\label{tab:alignment}
\begin{tabular}{@{}llll@{}}
\toprule
\textbf{Paper Ref} & \textbf{Lean Declaration} & \textbf{File} & \textbf{Status} \\
\midrule
Def.\ 2.1 (Semiotic manifold) & \texttt{SemioticManifold} & \texttt{Basic} & Definition \\
Def.\ 2.3 (Characteristic fields) & \texttt{SemioticContext}, \texttt{.a} & \texttt{Basic} & Definition \\
Def.\ 3.1 (V1\('\)$) & \texttt{SemioticBVP} & \texttt{Basic} & Definition \\
Def.\ 3.3 (Canonical closure) & \texttt{.canonicalViability} & \texttt{Basic} & Definition \\
Def.\ 3.6 (Weak coherent config.) & \texttt{IsWeakCoherentConfiguration} & \texttt{Basic} & Definition \\
Def.\ 3.13 (Principal eigenvalue) & \texttt{PrincipalEigendata} & \texttt{Axioms} & Definition \\
\midrule
Lemma 3.7 (Compactness of $T$) & \texttt{PDEInfra.T\_continuous\_compact} & \texttt{Axioms} & Axiom \\
Assumption 3.8 (Coercivity) & Hypothesis \texttt{hB} in Thm.\ 3.12 & \texttt{Theorems} & Proved \\
Lemma 3.10 ($L^\infty$ bound) & \texttt{PDEInfra.linfty\_bound} & \texttt{Axioms} & Axiom \\
Lemma 3.11 ($C^{1,\alpha}$ bound) & (subsumed by \texttt{linfty\_bound}) & --- & Not formalized \\
Thm.\ 3.12 (Existence) & \texttt{.exists\_isWeakCoherentConfiguration} & \texttt{Theorems} & Proved (PDEInfra) \\
Thm.\ 3.16 (Nontriviality) & \texttt{.exists\_pos\_isWeakCoherentConfiguration} & \texttt{Theorems} & Proved (PDEInfra) \\
\midrule
--- (Spectral, 1D) & \texttt{spectral\_characterization\_1d} & \texttt{Theorems} & Proved \\
--- (Scaling algebra) & \texttt{scaling\_algebraic\_contradiction} & \texttt{Theorems} & Proved \\
--- (Scaling uniqueness) & \texttt{scaling\_uniqueness} & \texttt{ScalingUniqueness} & Proved \\
--- (Operator: $\Delta(0)=0$) & \texttt{laplacian\_zero} & \texttt{OperatorLemmas} & Proved \\
--- (Operator: linearity) & \texttt{laplacian\_linear} & \texttt{OperatorLemmas} & Proved \\
--- (Operator: $|\nabla 0|=0$) & \texttt{gradNorm\_zero} & \texttt{OperatorLemmas} & Proved \\
--- ($a(x) \geq 0$) & \texttt{SemioticContext.a\_nonneg} & \texttt{CoefficientLemmas} & Proved \\
--- ($a(x) \leq 1$) & \texttt{SemioticContext.a\_le\_one} & \texttt{CoefficientLemmas} & Proved \\
--- ($p - 1 > 0$) & \texttt{SemioticContext.p\_sub\_one\_pos} & \texttt{CoefficientLemmas} & Proved \\
\midrule
Defs.\ 3.19--3.27 (Temporal) & --- & --- & Not formalized \\
Defs.\ 4.1--4.8, Props.\ 4.5, 4.9 & --- & --- & Not formalized \\
Defs.\ 5.1, 5.3 (Operational) & --- & --- & Not formalized \\
\bottomrule
\end{tabular}
\end{table}

\subsection{Axiom boundary: the PDEInfra typeclass}\label{sec:axiom_boundary}

The \texttt{PDEInfra} typeclass packages five assumptions from classical elliptic PDE theory that are not yet available in Mathlib for abstract Riemannian manifolds. Downstream theorems declare their dependence explicitly via \texttt{[PDEInfra bvp solOp]}. Table~\ref{tab:axioms} itemizes each axiom.

\begin{table}[ht]
\centering
\small
\caption{The five \texttt{PDEInfra} axioms and their classical sources.}
\label{tab:axioms}
\begin{tabular}{@{}lll@{}}
\toprule
\textbf{Axiom} & \textbf{Classical Source} & \textbf{Mathlib Status} \\
\midrule
\texttt{T\_continuous\_compact} & Schauder estimates + Arzel\`a--Ascoli & No H\"older spaces on manifolds \\
\texttt{linfty\_bound} & Maximum principle (Gilbarg--Trudinger) & No max.\ principle for manifolds \\
\texttt{schaefer} & Schaefer 1955~\cite{Schaefer1955} & Not in Mathlib \\
\texttt{fixed\_point\_nonneg} & Strong maximum principle & No max.\ principle for manifolds \\
\texttt{monotone\_iteration} & Amann 1976~\cite{Amann1976} & No sub-/super-solution theory \\
\bottomrule
\end{tabular}
\end{table}

The \texttt{T\_continuous\_compact} field is currently \texttt{True} (a placeholder). The Schaefer axiom takes this as a hypothesis via \texttt{True $\to$}, preserving the structural dependency chain even though the content is trivial until Mathlib gains the requisite infrastructure. The algebraic core of the $L^\infty$ bound (Lemma~\ref{lem:LinftyBound})---that $bv \geq cv^p$ implies $v \leq (B/c_0)^{1/(p-1)}$---is independently proved in an Aristotle theorem-prover artifact; the maximum-principle step (that $\nabla u = 0$ and $\Delta u \leq 0$ at an interior maximum) remains an axiom.

As Mathlib's PDE infrastructure grows, these axioms can be replaced one by one with real proofs. The logical structure of the existence and nontriviality theorems is already verified; only the analytic plumbing remains.

```

**Step 2: Verify compilation**

```bash
cd /home/ndspence/GitHub/navi-creative-determinant/paper && pdflatex creative_determinant.tex && bibtex creative_determinant && pdflatex creative_determinant.tex && pdflatex creative_determinant.tex
```
Expected: Compiles without errors. Appendix A appears before bibliography. Tables render. All `\ref` and `\cite` resolve (no undefined references).

**Step 3: Visually inspect the PDF**

Open `paper/creative_determinant.pdf` and verify:
- Appendix A appears after Acknowledgments, before References
- Table 1 (alignment) has ~24 rows, readable formatting
- Table 2 (axioms) has 5 rows
- All cross-references resolve (no "??")
- The introduction paragraph at line 91 reads naturally and cites [deMoura2021], [Mathlib2020], [Spence2026Lean]

**Step 4: Commit**

```bash
git add paper/creative_determinant.tex
git commit -m "paper: add Appendix A with Lean verification alignment table and axiom boundary"
```

---

### Task 4: Final build verification and push

**Files:**
- None modified (verification only)

**Step 1: Clean build from scratch**

```bash
cd /home/ndspence/GitHub/navi-creative-determinant/paper && rm -f *.aux *.bbl *.blg *.log *.out && pdflatex creative_determinant.tex && bibtex creative_determinant && pdflatex creative_determinant.tex && pdflatex creative_determinant.tex
```
Expected: Zero errors, zero undefined references.

**Step 2: Check for LaTeX warnings**

```bash
grep -i "warning\|undefined\|multiply" creative_determinant.log | grep -v "Font"
```
Expected: No "undefined reference" or "multiply-defined label" warnings.

**Step 3: Verify the Lean project still builds**

```bash
cd /home/ndspence/GitHub/navi-creative-determinant/cd_formalization && lake build --wfail 2>&1 | tail -5
```
Expected: `Build completed successfully` with no warnings.

**Step 4: Push**

```bash
cd /home/ndspence/GitHub/navi-creative-determinant && git push
```
