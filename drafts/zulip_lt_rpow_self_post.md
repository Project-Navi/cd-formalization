# Zulip Post Draft: `x < x ^ p` for `1 < x` and `1 < p`

**Channel:** `#Is there code for X?`
**Subject:** `x < x ^ p` for real exponents with `1 < x` and `1 < p`

---

Hi,

Quick check — does Mathlib have the lemma `x < x ^ p` for `1 < x`
and `1 < p` (real rpow)? I can find `Real.rpow_lt_rpow_of_exponent_lt`
which gives `x ^ y < x ^ z` from `1 < x` and `y < z`, and composing
with `rpow_one` gives what I need in two lines:

```lean
theorem lt_rpow_self_of_one_lt (hx : 1 < x) (hp : 1 < p) :
    x < x ^ p := by
  have := Real.rpow_lt_rpow_of_exponent_lt hx hp
  rwa [Real.rpow_one] at this
```

But I haven't found a named lemma for this directly. I've been using it
in a formalization of uniqueness results for nonlinear elliptic PDEs
([cd-formalization](https://github.com/Project-Navi/cd-formalization))
and it comes up naturally whenever you have a superlinear exponent.

If it's missing, happy to PR it as a lemma near
`Mathlib.Analysis.SpecialFunctions.Pow.Real`. Would `@[simp]` be
appropriate here, or just a named lemma?

**AI disclosure:** The formalization uses Claude (Anthropic) and
Aristotle (theorem prover). All code is manually reviewed.

Thanks!
