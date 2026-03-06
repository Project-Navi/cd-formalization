# Zulip Post Draft: `x < x ^ p` for `1 < x` and `1 < p`

**Channel:** `#Is there code for X?`
**Subject:** `x < x ^ p` for real exponents with `1 < x` and `1 < p`

---

Hi,

Quick check — does Mathlib have `x < x ^ p` for `1 < x` and `1 < p`
(real rpow)? I can get it in two lines from
`rpow_lt_rpow_of_exponent_lt` + `rpow_one`:

```lean
example (x p : ℝ) (hx : 1 < x) (hp : 1 < p) :
    x < x ^ p := by
  have := Real.rpow_lt_rpow_of_exponent_lt hx hp
  rwa [Real.rpow_one] at this
```

If it's missing, happy to PR it near
`Mathlib.Analysis.SpecialFunctions.Pow.Real`. What would the right
name be?

**AI disclosure:** I found this gap while working on a Lean 4
formalization — the proof strategy is my own work, Claude (Anthropic)
assisted with Lean syntax and Mathlib API navigation.

Thanks!
