/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Graph.Basic
import CdFormal.MonotoneFixedPoint
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Sub- and supersolutions on a finite graph

A Jacobi splitting turns the problem of `CdFormal.Graph.Basic` into a fixed-point equation. With
d(x) = ∑_y w(x,y) and a constant K > 0, the equation at an interior vertex x is equivalent to

  u(x) = (∑_y w(x,y)·u(y) + a(x)·|∇u|(x) + (b(x) + K)·u(x) - c(x)·max(u(x), 0)^p) / (d(x) + K),

and `SemioticGraph.fixedPointMap` is the map sending u to this right-hand side at interior vertices
and to 0 on the boundary. Its fixed points are exactly the solutions it can produce
(`SemioticGraph.isSolution_of_fixedPointMap_eq`).

For functions with values in [0, M] that vanish on the boundary, the map is monotone when K is
large, provided a(x) ≤ √w(x,y) for every edge of positive weight between distinct interior
vertices (`SemioticGraph.fixedPointMap_mono`). Between an ordered subsolution and supersolution,
`monotone_fixed_point_between` on the order interval then gives a solution
(`SemioticGraph.exists_isSolution_between`).

Two barriers are provided: a small multiple of a nonnegative eigenfunction with negative eigenvalue
is a subsolution (`SemioticGraph.smul_subsolution`), and the function equal to a large constant M
at interior vertices and to 0 on the boundary is a supersolution
(`SemioticGraph.plateau_supersolution`). The latter is not constant, so its gradient norm is
nonzero next to the boundary; the proof bounds it by completing the square.

## Main definitions

- `SemioticGraph.numer`, `SemioticGraph.fixedPointMap` — the fixed-point map of the splitting
- `SemioticGraph.plateau` — M at interior vertices, 0 on the boundary

## Main statements

- `SemioticGraph.isSolution_of_fixedPointMap_eq` — fixed points are solutions
- `SemioticGraph.fixedPointMap_mono` — monotonicity on [0, M]-valued functions
- `SemioticGraph.exists_isSolution_between` — a solution between a subsolution and a
  supersolution
- `SemioticGraph.smul_subsolution`, `SemioticGraph.plateau_supersolution` — the barriers

## Implementation notes

Only the gradient term needs the edge-dominance condition. When u increases by δ at a neighbour y
of x, |∇u|(x) decreases by at most √w(x,y)·δ, while ∑_y w(x,y)·u(y) increases by w(x,y)·δ, and
a(x) ≤ √w(x,y) makes the gain cover a(x) times the loss. The dependence on u(x) itself, through
|∇u|(x) and the saturation term, is absorbed by K. The condition is sufficient for this argument;
it is not claimed to be necessary for existence.

## References

- [Amann1976] H. Amann, "Fixed point equations and nonlinear eigenvalue problems in ordered
  Banach spaces," 1976.

## Tags

sub- and supersolutions, monotone iteration, Knaster–Tarski, graph Laplacian
-/

noncomputable section

namespace SemioticGraph

/-- A Lipschitz bound for t ↦ t^p on [0, M]: v^p - u^p ≤ p·M^(p-1)·(v - u) for 0 ≤ u ≤ v ≤ M
and p ≥ 1. -/
theorem rpow_sub_rpow_le_mul {u v M p : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvM : v ≤ M)
    (hp : 1 ≤ p) : v ^ p - u ^ p ≤ p * M ^ (p - 1) * (v - u) := by
  rcases (hu.trans huv).eq_or_lt with hv | hv
  · have hu0 : u = 0 := le_antisymm (huv.trans hv.ge) hu
    rw [← hv, hu0, sub_self, sub_self, mul_zero]
  · have hs : 1 + (u / v - 1) = u / v := by ring
    have hb := one_add_mul_self_le_rpow_one_add (s := u / v - 1)
      (by linarith [div_nonneg hu hv.le]) hp
    rw [hs, Real.div_rpow hu hv.le, le_div_iff₀ (Real.rpow_pos_of_pos hv p)] at hb
    have hvp : v ^ p = v ^ (p - 1) * v := by
      rw [← Real.rpow_add_one hv.ne', sub_add_cancel]
    have huv' : u / v * v = u := div_mul_cancel₀ u hv.ne'
    have hkey : (1 + p * (u / v - 1)) * v ^ p = v ^ p + p * v ^ (p - 1) * (u - v) := by
      rw [hvp]
      linear_combination (p * v ^ (p - 1)) * huv'
    have hmono : p * v ^ (p - 1) * (v - u) ≤ p * M ^ (p - 1) * (v - u) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv.le hvM (by linarith)) (by linarith))
        (by linarith)
    rw [hkey] at hb
    linarith

/-- Completing the square: a·√(M·S) ≤ S + (a²/4)·M for M > 0 and S ≥ 0. -/
theorem mul_sqrt_mul_le {a M S : ℝ} (hM : 0 < M) (hS : 0 ≤ S) :
    a * √(M * S) ≤ S + a ^ 2 / 4 * M := by
  have hr := Real.sq_sqrt (mul_nonneg hM.le hS)
  have key : M * (S + a ^ 2 / 4 * M - a * √(M * S)) = (√(M * S) - M * a / 2) ^ 2 := by
    linear_combination -1 * hr
  have h := sq_nonneg (√(M * S) - M * a / 2)
  rw [← key] at h
  linarith [(mul_nonneg_iff_of_pos_left hM).mp h]

variable {V : Type*} (G : SemioticGraph V)

open Classical in
/-- The function equal to `M` at interior vertices and to `0` on the boundary. -/
def plateau (M : ℝ) (x : V) : ℝ := if x ∈ G.boundary then 0 else M

theorem plateau_of_mem {M : ℝ} {x : V} (hx : x ∈ G.boundary) : G.plateau M x = 0 := by
  rw [plateau, if_pos hx]

theorem plateau_of_notMem {M : ℝ} {x : V} (hx : x ∉ G.boundary) : G.plateau M x = M := by
  rw [plateau, if_neg hx]

theorem plateau_le {M : ℝ} (hM : 0 ≤ M) (x : V) : G.plateau M x ≤ M := by
  by_cases hx : x ∈ G.boundary
  · rw [G.plateau_of_mem hx]
    exact hM
  · rw [G.plateau_of_notMem hx]

variable [Fintype V]

/-- The numerator of the fixed-point map:
∑_y w(x,y)·u(y) + a(x)·|∇u|(x) + (b(x) + K)·u(x) - c(x)·max(u(x), 0)^p. -/
def numer (K : ℝ) (u : V → ℝ) (x : V) : ℝ :=
  ∑ y, G.w x y * u y + G.a x * G.gradNorm u x + (G.b x + K) * u x - G.c x * max (u x) 0 ^ G.p

open Classical in
/-- The fixed-point map of the Jacobi splitting with shift `K`: `numer K u x / (d(x) + K)` at
interior vertices and `0` on the boundary. -/
def fixedPointMap (K : ℝ) (u : V → ℝ) (x : V) : ℝ :=
  if x ∈ G.boundary then 0 else G.numer K u x / (∑ y, G.w x y + K)

theorem denom_pos {K : ℝ} (hK : 0 < K) (x : V) : 0 < ∑ y, G.w x y + K :=
  add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun y _ ↦ G.w_nonneg x y) hK

/-- The splitting identity: (d(x) + K)·u(x) - numer K u x is the residual of the equation. -/
theorem mul_sub_numer (K : ℝ) (u : V → ℝ) (x : V) :
    (∑ y, G.w x y + K) * u x - G.numer K u x =
      G.laplacian u x - (G.a x * G.gradNorm u x + G.b x * u x - G.c x * max (u x) 0 ^ G.p) := by
  have hL : G.laplacian u x = (∑ y, G.w x y) * u x - ∑ y, G.w x y * u y := by
    rw [laplacian, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by ring
  rw [hL, numer]
  ring

/-- A fixed point of the map solves the problem. -/
theorem isSolution_of_fixedPointMap_eq {K : ℝ} (hK : 0 < K) {u : V → ℝ}
    (hu : G.fixedPointMap K u = u) : G.IsSolution u := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have h := congrFun hu x
    rw [fixedPointMap, if_neg hx, div_eq_iff (G.denom_pos hK x).ne'] at h
    linarith [G.mul_sub_numer K u x]
  · have h := congrFun hu x
    rw [fixedPointMap, if_pos hx] at h
    exact h.symm

theorem le_fixedPointMap_of_subsolution {K : ℝ} (hK : 0 < K) {u : V → ℝ} {x : V}
    (hx : x ∉ G.boundary)
    (hsub : G.laplacian u x ≤ G.a x * G.gradNorm u x + G.b x * u x - G.c x * max (u x) 0 ^ G.p) :
    u x ≤ G.fixedPointMap K u x := by
  rw [fixedPointMap, if_neg hx, le_div_iff₀ (G.denom_pos hK x)]
  linarith [G.mul_sub_numer K u x]

theorem fixedPointMap_le_of_supersolution {K : ℝ} (hK : 0 < K) {u : V → ℝ} {x : V}
    (hx : x ∉ G.boundary)
    (hsup : G.a x * G.gradNorm u x + G.b x * u x - G.c x * max (u x) 0 ^ G.p ≤ G.laplacian u x) :
    G.fixedPointMap K u x ≤ u x := by
  rw [fixedPointMap, if_neg hx, div_le_iff₀ (G.denom_pos hK x)]
  linarith [G.mul_sub_numer K u x]

/-- Minkowski's inequality for the weighted sums that define the gradient norm. -/
theorem sqrt_sum_add_le (x : V) (f g : V → ℝ) :
    √(∑ y, G.w x y * (f y + g y) ^ 2) ≤
      √(∑ y, G.w x y * f y ^ 2) + √(∑ y, G.w x y * g y ^ 2) := by
  have hA : 0 ≤ ∑ y, G.w x y * f y ^ 2 :=
    Finset.sum_nonneg fun y _ ↦ mul_nonneg (G.w_nonneg x y) (sq_nonneg _)
  have hB : 0 ≤ ∑ y, G.w x y * g y ^ 2 :=
    Finset.sum_nonneg fun y _ ↦ mul_nonneg (G.w_nonneg x y) (sq_nonneg _)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun y ↦ √(G.w x y) * f y)
    (fun y ↦ √(G.w x y) * g y)
  have h1 : ∀ y, √(G.w x y) * f y * (√(G.w x y) * g y) = G.w x y * (f y * g y) := fun y ↦ by
    linear_combination (f y * g y) * Real.mul_self_sqrt (G.w_nonneg x y)
  have h2 : ∀ y, (√(G.w x y) * f y) ^ 2 = G.w x y * f y ^ 2 := fun y ↦ by
    rw [mul_pow, Real.sq_sqrt (G.w_nonneg x y)]
  have h3 : ∀ y, (√(G.w x y) * g y) ^ 2 = G.w x y * g y ^ 2 := fun y ↦ by
    rw [mul_pow, Real.sq_sqrt (G.w_nonneg x y)]
  simp only [h1, h2, h3] at hcs
  have hexp : ∑ y, G.w x y * (f y + g y) ^ 2 =
      ∑ y, G.w x y * f y ^ 2 + 2 * ∑ y, G.w x y * (f y * g y) + ∑ y, G.w x y * g y ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by ring
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), hexp, add_sq,
    Real.sq_sqrt hA, Real.sq_sqrt hB]
  linarith

/-- The weighted ℓ² norm is at most the weighted ℓ¹ norm. -/
theorem sqrt_sum_le_sum (x : V) (f : V → ℝ) :
    √(∑ y, G.w x y * f y ^ 2) ≤ ∑ y, √(G.w x y) * |f y| := by
  have hnn : ∀ y ∈ Finset.univ, 0 ≤ √(G.w x y) * |f y| := fun y _ ↦
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsq : ∀ y, (√(G.w x y) * |f y|) ^ 2 = G.w x y * f y ^ 2 := fun y ↦ by
    rw [mul_pow, Real.sq_sqrt (G.w_nonneg x y), sq_abs]
  rw [Real.sqrt_le_left (Finset.sum_nonneg hnn)]
  calc ∑ y, G.w x y * f y ^ 2 = ∑ y, (√(G.w x y) * |f y|) ^ 2 :=
        Finset.sum_congr rfl fun y _ ↦ (hsq y).symm
    _ ≤ (∑ y, √(G.w x y) * |f y|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg hnn

/-- The gradient term under the edge-dominance condition: if u ≤ v agree on the boundary, then at
an interior vertex x,
a(x)·|∇u|(x) ≤ a(x)·|∇v|(x) + ∑_y w(x,y)·(v(y) - u(y)) + a(x)·(∑_y √w(x,y))·(v(x) - u(x)). -/
theorem a_mul_gradNorm_le
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    {u v : V → ℝ} (huv : ∀ y, u y ≤ v y) (hbd : ∀ y ∈ G.boundary, u y = v y) {x : V}
    (hx : x ∉ G.boundary) :
    G.a x * G.gradNorm u x ≤ G.a x * G.gradNorm v x + ∑ y, G.w x y * (v y - u y) +
      G.a x * (∑ y, √(G.w x y)) * (v x - u x) := by
  have ha := G.a_nonneg x
  have hdx : 0 ≤ v x - u x := sub_nonneg.mpr (huv x)
  have h1 : G.gradNorm u x ≤
      G.gradNorm v x + √(∑ y, G.w x y * (v x - u x - (v y - u y)) ^ 2) := by
    have h := G.sqrt_sum_add_le x (fun y ↦ v y - v x) (fun y ↦ v x - u x - (v y - u y))
    have he : ∀ y, v y - v x + (v x - u x - (v y - u y)) = u y - u x := fun y ↦ by ring
    simp only [he] at h
    exact h
  have h2 : √(∑ y, G.w x y * (v x - u x - (v y - u y)) ^ 2) ≤
      ∑ y, √(G.w x y) * |v x - u x - (v y - u y)| :=
    G.sqrt_sum_le_sum x fun y ↦ v x - u x - (v y - u y)
  have h3 : ∀ y, G.a x * (√(G.w x y) * |v x - u x - (v y - u y)|) ≤
      G.w x y * (v y - u y) + G.a x * √(G.w x y) * (v x - u x) := by
    intro y
    have hdy : 0 ≤ v y - u y := sub_nonneg.mpr (huv y)
    by_cases hyx : y = x
    · rw [hyx, sub_self, abs_zero, mul_zero, mul_zero]
      exact add_nonneg (mul_nonneg (G.w_nonneg x x) hdx)
        (mul_nonneg (mul_nonneg ha (Real.sqrt_nonneg _)) hdx)
    by_cases hy : y ∈ G.boundary
    · have hd0 : v y - u y = 0 := by rw [hbd y hy, sub_self]
      rw [hd0, sub_zero, mul_zero, zero_add, abs_of_nonneg hdx]
      exact le_of_eq (by ring)
    rcases (G.w_nonneg x y).eq_or_lt with hw0 | hw
    · simp [← hw0]
    have hs := Real.sqrt_nonneg (G.w x y)
    have habs : |v x - u x - (v y - u y)| ≤ v x - u x + (v y - u y) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have e1 := mul_le_mul_of_nonneg_left habs (mul_nonneg ha hs)
    have e2 := mul_le_mul_of_nonneg_right (hdom x y hx hy (Ne.symm hyx) hw) (mul_nonneg hs hdy)
    have e3 : √(G.w x y) * (√(G.w x y) * (v y - u y)) = G.w x y * (v y - u y) := by
      rw [← mul_assoc, Real.mul_self_sqrt (G.w_nonneg x y)]
    linarith
  have h4 : G.a x * ∑ y, √(G.w x y) * |v x - u x - (v y - u y)| ≤
      ∑ y, G.w x y * (v y - u y) + G.a x * (∑ y, √(G.w x y)) * (v x - u x) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ ↦ h3 y
  have h5 : G.a x * G.gradNorm u x ≤
      G.a x * (G.gradNorm v x + ∑ y, √(G.w x y) * |v x - u x - (v y - u y)|) :=
    mul_le_mul_of_nonneg_left (by linarith) ha
  linarith

/-- The numerator is monotone on [0, M]-valued functions that agree on the boundary, once `K`
dominates a(x)·∑_y √w(x,y) + c(x)·p·M^(p-1) - b(x). -/
theorem numer_mono
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    {K M : ℝ} (hKM : ∀ x, G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) - G.b x ≤ K)
    {u v : V → ℝ} (hu : ∀ y, 0 ≤ u y) (huv : ∀ y, u y ≤ v y) (hvM : ∀ y, v y ≤ M)
    (hbd : ∀ y ∈ G.boundary, u y = v y) {x : V} (hx : x ∉ G.boundary) :
    G.numer K u x ≤ G.numer K v x := by
  have hgrad := G.a_mul_gradNorm_le hdom huv hbd hx
  have hsum : ∑ y, G.w x y * v y = ∑ y, G.w x y * u y + ∑ y, G.w x y * (v y - u y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ ↦ by ring
  have hvx : 0 ≤ v x := (hu x).trans (huv x)
  have hcp := mul_le_mul_of_nonneg_left
    (rpow_sub_rpow_le_mul (hu x) (huv x) (hvM x) G.one_lt_p.le) (G.c_pos x).le
  have hK := mul_le_mul_of_nonneg_right (hKM x) (sub_nonneg.mpr (huv x))
  rw [numer, numer, max_eq_left (hu x), max_eq_left hvx]
  linarith

/-- The fixed-point map is monotone on [0, M]-valued functions that agree on the boundary. -/
theorem fixedPointMap_mono
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    {K M : ℝ} (hK : 0 < K)
    (hKM : ∀ x, G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) - G.b x ≤ K)
    {u v : V → ℝ} (hu : ∀ y, 0 ≤ u y) (huv : ∀ y, u y ≤ v y) (hvM : ∀ y, v y ≤ M)
    (hbd : ∀ y ∈ G.boundary, u y = v y) (x : V) :
    G.fixedPointMap K u x ≤ G.fixedPointMap K v x := by
  by_cases hx : x ∈ G.boundary
  · rw [fixedPointMap, fixedPointMap, if_pos hx, if_pos hx]
  · rw [fixedPointMap, fixedPointMap, if_neg hx, if_neg hx]
    exact div_le_div_of_nonneg_right (G.numer_mono hdom hKM hu huv hvM hbd hx)
      (G.denom_pos hK x).le

/-- **Sub- and supersolutions.** Under the edge-dominance condition, an ordered pair of a
subsolution `lo ≥ 0` and a supersolution `hi ≤ M`, both vanishing on the boundary, encloses a
solution. The proof applies `monotone_fixed_point_between` to the fixed-point map on the order
interval [lo, hi]. -/
theorem exists_isSolution_between
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    {K M : ℝ} (hK : 0 < K)
    (hKM : ∀ x, G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) - G.b x ≤ K)
    {lo hi : V → ℝ} (hlo : ∀ y, 0 ≤ lo y) (hlohi : ∀ y, lo y ≤ hi y) (hhi : ∀ y, hi y ≤ M)
    (hlo_bd : ∀ y ∈ G.boundary, lo y = 0) (hhi_bd : ∀ y ∈ G.boundary, hi y = 0)
    (hsub : ∀ x, x ∉ G.boundary →
      G.laplacian lo x ≤ G.a x * G.gradNorm lo x + G.b x * lo x - G.c x * max (lo x) 0 ^ G.p)
    (hsup : ∀ x, x ∉ G.boundary →
      G.a x * G.gradNorm hi x + G.b x * hi x - G.c x * max (hi x) 0 ^ G.p ≤ G.laplacian hi x) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ y, lo y ≤ u y ∧ u y ≤ hi y := by
  have hzero : ∀ u : V → ℝ, lo ≤ u → u ≤ hi → ∀ y ∈ G.boundary, u y = 0 :=
    fun u hlu huh y hy ↦
      le_antisymm ((huh y).trans (hhi_bd y hy).le) ((hlo_bd y hy).ge.trans (hlu y))
  have hmono : ∀ u v : V → ℝ, lo ≤ u → u ≤ v → v ≤ hi →
      G.fixedPointMap K u ≤ G.fixedPointMap K v := fun u v hlu huv hvh ↦
    G.fixedPointMap_mono hdom hK hKM (fun y ↦ (hlo y).trans (hlu y)) huv
      (fun y ↦ (hvh y).trans (hhi y)) fun y hy ↦
        (hzero u hlu (huv.trans hvh) y hy).trans (hzero v (hlu.trans huv) hvh y hy).symm
  have hlo_le : lo ≤ G.fixedPointMap K lo := fun x ↦ by
    by_cases hx : x ∈ G.boundary
    · rw [hlo_bd x hx, fixedPointMap, if_pos hx]
    · exact G.le_fixedPointMap_of_subsolution hK hx (hsub x hx)
  have hhi_le : G.fixedPointMap K hi ≤ hi := fun x ↦ by
    by_cases hx : x ∈ G.boundary
    · rw [hhi_bd x hx, fixedPointMap, if_pos hx]
    · exact G.fixedPointMap_le_of_supersolution hK hx (hsup x hx)
  have hmaps : ∀ u ∈ Set.Icc lo hi, G.fixedPointMap K u ∈ Set.Icc lo hi := fun u hu ↦
    ⟨hlo_le.trans (hmono lo u le_rfl hu.1 hu.2),
      (hmono u hi hu.1 hu.2 le_rfl).trans hhi_le⟩
  haveI : Fact (lo ≤ hi) := ⟨hlohi⟩
  obtain ⟨u, hu, -, -⟩ := monotone_fixed_point_between (α := Set.Icc lo hi)
    ⟨fun u ↦ ⟨G.fixedPointMap K u, hmaps u u.2⟩, fun u v huv ↦ hmono u v u.2.1 huv v.2.2⟩
    bot_le le_top bot_le
  have hfix : G.fixedPointMap K u = u := congrArg Subtype.val hu
  exact ⟨u, G.isSolution_of_fixedPointMap_eq hK hfix, fun y ↦ ⟨u.2.1 y, u.2.2 y⟩⟩

/-- **Subsolution.** If φ ≥ 0, φ ≤ 1, (L φ)(x) = b(x)·φ(x) + μ·φ(x) at interior vertices and
c(x)·ε^(p-1) ≤ -μ for every x, then ε·φ is a subsolution. -/
theorem smul_subsolution {φ : V → ℝ} {μ ε : ℝ} (hφ : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1)
    (heq : ∀ x, x ∉ G.boundary → G.laplacian φ x = G.b x * φ x + μ * φ x) (hε : 0 < ε)
    (hεc : ∀ x, G.c x * ε ^ (G.p - 1) ≤ -μ) {x : V} (hx : x ∉ G.boundary) :
    G.laplacian (fun y ↦ ε * φ y) x ≤
      G.a x * G.gradNorm (fun y ↦ ε * φ y) x + G.b x * (ε * φ x) -
        G.c x * max (ε * φ x) 0 ^ G.p := by
  have hs0 : 0 ≤ ε * φ x := mul_nonneg hε.le (hφ x)
  have hsε : ε * φ x ≤ ε := mul_le_of_le_one_right hε.le (hφ1 x)
  have hL : G.laplacian (fun y ↦ ε * φ y) x = ε * G.laplacian φ x := by
    rw [laplacian, laplacian, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ ↦ by ring
  have hpow : (ε * φ x) ^ G.p ≤ ε ^ (G.p - 1) * (ε * φ x) := by
    rcases hs0.eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (zero_lt_one.trans G.one_lt_p).ne', mul_zero]
    · have hsp : (ε * φ x) ^ G.p = (ε * φ x) ^ (G.p - 1) * (ε * φ x) := by
        rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
      rw [hsp]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hs0 hsε (by linarith [G.one_lt_p])) hs0
  have hgrad : 0 ≤ G.a x * G.gradNorm (fun y ↦ ε * φ y) x :=
    mul_nonneg (G.a_nonneg x) (G.gradNorm_nonneg _ x)
  have h1 := mul_le_mul_of_nonneg_left hpow (G.c_pos x).le
  have h2 := mul_le_mul_of_nonneg_left (hεc x) hs0
  rw [hL, heq x hx, max_eq_left hs0]
  linarith

/-- **Supersolution.** If M > 0 and a(x)²/4 + b(x) ≤ c(x)·M^(p-1) for every x, then
`G.plateau M` is a supersolution. -/
theorem plateau_supersolution {M : ℝ} (hM : 0 < M)
    (hMc : ∀ x, G.a x ^ 2 / 4 + G.b x ≤ G.c x * M ^ (G.p - 1)) {x : V} (hx : x ∉ G.boundary) :
    G.a x * G.gradNorm (G.plateau M) x + G.b x * G.plateau M x -
      G.c x * max (G.plateau M x) 0 ^ G.p ≤ G.laplacian (G.plateau M) x := by
  have hpx : G.plateau M x = M := G.plateau_of_notMem hx
  have hS : 0 ≤ ∑ y, G.w x y * (M - G.plateau M y) :=
    Finset.sum_nonneg fun y _ ↦
      mul_nonneg (G.w_nonneg x y) (sub_nonneg.mpr (G.plateau_le hM.le y))
  have hsq : ∀ y, (G.plateau M y - M) ^ 2 = M * (M - G.plateau M y) := by
    intro y
    by_cases hy : y ∈ G.boundary
    · rw [G.plateau_of_mem hy]
      ring
    · rw [G.plateau_of_notMem hy]
      ring
  have hL : G.laplacian (G.plateau M) x = ∑ y, G.w x y * (M - G.plateau M y) := by
    rw [laplacian, hpx]
  have hG : G.gradNorm (G.plateau M) x = √(M * ∑ y, G.w x y * (M - G.plateau M y)) := by
    rw [gradNorm, hpx, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun y _ ↦ by rw [hsq]; ring
  have hMp : M ^ G.p = M ^ (G.p - 1) * M := by
    rw [← Real.rpow_add_one hM.ne', sub_add_cancel]
  have hr := mul_sqrt_mul_le (a := G.a x) hM hS
  have h3 := mul_le_mul_of_nonneg_right (hMc x) hM.le
  rw [hL, hG, hpx, max_eq_left hM.le, hMp]
  linarith

end SemioticGraph

end
