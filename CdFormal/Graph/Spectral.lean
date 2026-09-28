/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Graph.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.Order.Compact

/-!
# The principal eigenvector on a finite graph

The principal Dirichlet eigenvalue λ₁ of L - diag(b) (`SemioticGraph.principalEigenvalue`) is
attained on the unit sphere, and a minimizer satisfies (L φ)(x) = b(x)·φ(x) + λ₁·φ(x) at every
interior vertex. If φ is a minimizer, so is |φ|; when the interior graph is connected, |φ| is
positive at every interior vertex, because a zero of a nonnegative eigenvector spreads to every
neighbour.

## Main statements

- `SemioticGraph.principalEigenvalue_mul_le` — λ₁·∑ u² ≤ E(u) for every `u` vanishing on the
  boundary
- `SemioticGraph.exists_pos_eigenvector` — if the interior graph is connected, a unit
  eigenvector for λ₁ that vanishes on the boundary and is positive at every interior vertex
- `SemioticGraph.principalEigenvalue_neg` — λ₁ < 0 when some `u` vanishing on the boundary has
  negative energy

## Implementation notes

The unit sphere is a closed subset of the cube [-1, 1]^V, so the energy attains its minimum on it.
The eigenvalue equation is the first-order condition at the minimizer: for `h` vanishing on the
boundary, t ↦ E(φ + t·h) - λ₁·∑ (φ + t·h)² is a nonnegative quadratic with no constant term, so
its linear coefficient vanishes (`discrim_le_zero`).

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.

## Tags

graph Laplacian, principal eigenvalue, Rayleigh quotient
-/

namespace SemioticGraph

variable {V : Type*} [Fintype V] (G : SemioticGraph V)

/-- Summation by parts: ∑_x ∑_y w(x,y)·(u(x) - u(y))·(h(x) - h(y)) = 2·∑_x h(x)·(L u)(x). -/
theorem sum_sum_mul_sub_mul_sub (u h : V → ℝ) :
    ∑ x, ∑ y, G.w x y * (u x - u y) * (h x - h y) = 2 * ∑ x, h x * G.laplacian u x := by
  have hswap : ∑ x, ∑ y, G.w x y * (u x - u y) * h y =
      -∑ x, ∑ y, G.w x y * (u x - u y) * h x := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [G.w_symm]
    ring
  calc ∑ x, ∑ y, G.w x y * (u x - u y) * (h x - h y)
      = ∑ x, ∑ y, G.w x y * (u x - u y) * h x - ∑ x, ∑ y, G.w x y * (u x - u y) * h y := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        ring
    _ = 2 * ∑ x, h x * G.laplacian u x := by
        rw [hswap, sub_neg_eq_add, ← two_mul]
        congr 1
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [laplacian, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        ring

/-- The energy along a line: E(φ + t·h) = E(φ) + 2t·∑ h·(L φ - b·φ) + t²·E(h). -/
theorem energy_add_smul (φ h : V → ℝ) (t : ℝ) :
    G.energy (fun x ↦ φ x + t * h x) =
      G.energy φ + 2 * t * ∑ x, h x * (G.laplacian φ x - G.b x * φ x) + t ^ 2 * G.energy h := by
  have h1 : ∀ x y, G.w x y * (φ x + t * h x - (φ y + t * h y)) ^ 2 =
      G.w x y * (φ x - φ y) ^ 2 + 2 * t * (G.w x y * (φ x - φ y) * (h x - h y)) +
        t ^ 2 * (G.w x y * (h x - h y) ^ 2) := fun x y ↦ by ring
  have h2 : ∀ x, G.b x * (φ x + t * h x) ^ 2 =
      G.b x * φ x ^ 2 + 2 * t * (h x * (G.b x * φ x)) + t ^ 2 * (G.b x * h x ^ 2) :=
    fun x ↦ by ring
  have h3 : ∑ x, h x * (G.laplacian φ x - G.b x * φ x) =
      ∑ x, h x * G.laplacian φ x - ∑ x, h x * (G.b x * φ x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  simp only [energy, h1, h2, h3, Finset.sum_add_distrib, ← Finset.mul_sum,
    G.sum_sum_mul_sub_mul_sub φ h]
  ring

/-- ∑ (φ + t·h)² = ∑ φ² + 2t·∑ φ·h + t²·∑ h². -/
theorem sum_sq_add_smul (φ h : V → ℝ) (t : ℝ) :
    ∑ x, (φ x + t * h x) ^ 2 = ∑ x, φ x ^ 2 + 2 * t * ∑ x, φ x * h x + t ^ 2 * ∑ x, h x ^ 2 := by
  have h1 : ∀ x, (φ x + t * h x) ^ 2 = φ x ^ 2 + 2 * t * (φ x * h x) + t ^ 2 * h x ^ 2 :=
    fun x ↦ by ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The energy is a quadratic form: E(c·u) = c²·E(u). -/
theorem energy_smul (c : ℝ) (u : V → ℝ) : G.energy (fun x ↦ c * u x) = c ^ 2 * G.energy u := by
  have h1 : ∀ x y, G.w x y * (c * u x - c * u y) ^ 2 = c ^ 2 * (G.w x y * (u x - u y) ^ 2) :=
    fun x y ↦ by ring
  have h2 : ∀ x, G.b x * (c * u x) ^ 2 = c ^ 2 * (G.b x * u x ^ 2) := fun x ↦ by ring
  simp only [energy, h1, h2, ← Finset.mul_sum]
  ring

/-- A function with ∑ u² = 0 is zero, so its energy is zero. -/
theorem energy_eq_zero_of_sum_sq_eq_zero {u : V → ℝ} (h : ∑ x, u x ^ 2 = 0) :
    G.energy u = 0 := by
  have hu : ∀ x, u x = 0 := fun x ↦ (pow_eq_zero_iff two_ne_zero).mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun y _ ↦ sq_nonneg (u y)).mp h x (Finset.mem_univ x))
  simp [energy, hu]

theorem continuous_energy : Continuous G.energy := by
  have h : G.energy = fun u ↦ (∑ x, ∑ y, G.w x y * (u x - u y) ^ 2) / 2 - ∑ x, G.b x * u x ^ 2 :=
    rfl
  rw [h]
  fun_prop

/-- Every value of a unit function lies in [-1, 1]. -/
theorem abs_le_one_of_mem_unitSphere {u : V → ℝ} (hu : u ∈ G.unitSphere) (x : V) :
    |u x| ≤ 1 := by
  have hx : u x ^ 2 ≤ 1 := (Finset.single_le_sum (fun y _ ↦ sq_nonneg (u y))
    (Finset.mem_univ x)).trans_eq (G.mem_unitSphere.mp hu).2
  exact abs_le_of_sq_le_sq (by rwa [one_pow]) zero_le_one

theorem isCompact_unitSphere : IsCompact G.unitSphere := by
  have hsub : G.unitSphere ⊆ Set.univ.pi fun _ ↦ Set.Icc (-1) 1 := fun u hu ↦
    Set.mem_univ_pi.mpr fun x ↦ Set.mem_Icc.mpr (abs_le.mp (G.abs_le_one_of_mem_unitSphere hu x))
  have hclosed : IsClosed G.unitSphere := by
    have h : G.unitSphere =
        (⋂ x ∈ G.boundary, {u : V → ℝ | u x = 0}) ∩ {u | ∑ x, u x ^ 2 = 1} := by
      ext u
      simp [mem_unitSphere]
    rw [h]
    refine IsClosed.inter (isClosed_biInter fun x _ ↦ ?_) ?_
    · exact isClosed_eq (continuous_apply x) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ ↦ isCompact_Icc) hclosed hsub

theorem unitSphere_nonempty (hne : ∃ x, x ∉ G.boundary) : G.unitSphere.Nonempty := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨fun x ↦ if x = x₀ then 1 else 0, G.mem_unitSphere.mpr ⟨fun x hx ↦ ?_, ?_⟩⟩
  · have hne : x ≠ x₀ := by
      rintro rfl
      exact hx₀ hx
    simp [hne]
  · simp

/-- If the interior is nonempty, the energy attains its minimum on the unit sphere. -/
theorem exists_isMinOn_energy (hne : ∃ x, x ∉ G.boundary) :
    ∃ φ ∈ G.unitSphere, IsMinOn G.energy G.unitSphere φ :=
  G.isCompact_unitSphere.exists_isMinOn (G.unitSphere_nonempty hne)
    G.continuous_energy.continuousOn

theorem principalEigenvalue_le {u : V → ℝ} (hu : u ∈ G.unitSphere) :
    G.principalEigenvalue ≤ G.energy u :=
  csInf_le (G.isCompact_unitSphere.bddBelow_image G.continuous_energy.continuousOn)
    (Set.mem_image_of_mem _ hu)

theorem principalEigenvalue_eq {φ : V → ℝ} (hφ : φ ∈ G.unitSphere)
    (hmin : IsMinOn G.energy G.unitSphere φ) : G.principalEigenvalue = G.energy φ := by
  rw [principalEigenvalue]
  refine IsLeast.csInf_eq ⟨Set.mem_image_of_mem _ hφ, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact isMinOn_iff.mp hmin u hu

/-- The Rayleigh bound: λ₁·∑ u² ≤ E(u) for every `u` vanishing on the boundary. -/
theorem principalEigenvalue_mul_le {u : V → ℝ} (hu : ∀ x ∈ G.boundary, u x = 0) :
    G.principalEigenvalue * ∑ x, u x ^ 2 ≤ G.energy u := by
  rcases (Finset.sum_nonneg fun x _ ↦ sq_nonneg (u x) : 0 ≤ ∑ x, u x ^ 2).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero, G.energy_eq_zero_of_sum_sq_eq_zero h0.symm]
  · have hs : (√(∑ y, u y ^ 2))⁻¹ ^ 2 * ∑ x, u x ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
    have hmem : (fun x ↦ (√(∑ y, u y ^ 2))⁻¹ * u x) ∈ G.unitSphere := by
      refine G.mem_unitSphere.mpr ⟨fun x hx ↦ by simp [hu x hx], ?_⟩
      simp only [mul_pow, ← Finset.mul_sum]
      exact hs
    have hle := G.principalEigenvalue_le hmem
    rw [G.energy_smul] at hle
    calc G.principalEigenvalue * ∑ x, u x ^ 2
        ≤ (√(∑ y, u y ^ 2))⁻¹ ^ 2 * G.energy u * ∑ x, u x ^ 2 :=
          mul_le_mul_of_nonneg_right hle hpos.le
      _ = G.energy u := by
          rw [mul_comm ((√(∑ y, u y ^ 2))⁻¹ ^ 2) (G.energy u), mul_assoc, hs, mul_one]

/-- λ₁ < 0 as soon as some function vanishing on the boundary has negative energy. -/
theorem principalEigenvalue_neg {u : V → ℝ} (hu : ∀ x ∈ G.boundary, u x = 0)
    (hneg : G.energy u < 0) : G.principalEigenvalue < 0 := by
  have hle := G.principalEigenvalue_mul_le hu
  have hS : 0 < ∑ x, u x ^ 2 := by
    rcases (Finset.sum_nonneg fun x _ ↦ sq_nonneg (u x) : 0 ≤ ∑ x, u x ^ 2).eq_or_lt with
      h0 | h0
    · rw [G.energy_eq_zero_of_sum_sq_eq_zero h0.symm] at hneg
      exact absurd hneg (lt_irrefl 0)
    · exact h0
  by_contra h
  have := mul_nonneg (not_lt.mp h) hS.le
  linarith

/-- First-order condition at a minimizer: ∑ h·(L φ - b·φ - E(φ)·φ) = 0 for every `h` vanishing
on the boundary. -/
theorem sum_mul_eigen_eq_zero {φ : V → ℝ} (hφ : φ ∈ G.unitSphere)
    (hmin : IsMinOn G.energy G.unitSphere φ) {h : V → ℝ} (hh : ∀ x ∈ G.boundary, h x = 0) :
    ∑ x, h x * (G.laplacian φ x - G.b x * φ x - G.energy φ * φ x) = 0 := by
  have heig := G.principalEigenvalue_eq hφ hmin
  have h1 : ∑ x, φ x ^ 2 = 1 := (G.mem_unitSphere.mp hφ).2
  have key : ∀ t : ℝ, 0 ≤ (G.energy h - G.energy φ * ∑ x, h x ^ 2) * (t * t) +
      (2 * ∑ x, h x * (G.laplacian φ x - G.b x * φ x) - 2 * G.energy φ * ∑ x, φ x * h x) * t +
      0 := by
    intro t
    have hle : G.principalEigenvalue * ∑ x, (φ x + t * h x) ^ 2 ≤
        G.energy (fun x ↦ φ x + t * h x) :=
      G.principalEigenvalue_mul_le (u := fun x ↦ φ x + t * h x) fun x hx ↦ by
        simp [(G.mem_unitSphere.mp hφ).1 x hx, hh x hx]
    rw [sum_sq_add_smul, G.energy_add_smul, h1, heig] at hle
    linarith
  have hd := discrim_le_zero key
  rw [discrim, mul_zero, sub_zero] at hd
  have hb : 2 * ∑ x, h x * (G.laplacian φ x - G.b x * φ x) -
      2 * G.energy φ * ∑ x, φ x * h x = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hd (sq_nonneg _))
  have hsplit : ∑ x, h x * (G.laplacian φ x - G.b x * φ x - G.energy φ * φ x) =
      ∑ x, h x * (G.laplacian φ x - G.b x * φ x) - G.energy φ * ∑ x, φ x * h x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [hsplit]
  linarith

/-- A minimizer is an eigenvector: (L φ)(x) = b(x)·φ(x) + E(φ)·φ(x) at every interior vertex. -/
theorem laplacian_eq_of_isMinOn {φ : V → ℝ} (hφ : φ ∈ G.unitSphere)
    (hmin : IsMinOn G.energy G.unitSphere φ) {x : V} (hx : x ∉ G.boundary) :
    G.laplacian φ x = G.b x * φ x + G.energy φ * φ x := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : V → ℝ, ∀ y, r y = G.laplacian φ y - G.b y * φ y - G.energy φ * φ y :=
    ⟨_, fun _ ↦ rfl⟩
  have h0 := G.sum_mul_eigen_eq_zero hφ hmin (h := fun y ↦ if y ∈ G.boundary then 0 else r y)
    fun y hy ↦ if_pos hy
  simp only [← hr] at h0
  have hnn : ∀ y ∈ Finset.univ, 0 ≤ (if y ∈ G.boundary then 0 else r y) * r y := by
    intro y _
    split_ifs
    · simp
    · exact mul_self_nonneg (r y)
  have hx0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 x (Finset.mem_univ x)
  rw [if_neg hx, mul_self_eq_zero, hr] at hx0
  linarith

theorem abs_mem_unitSphere {φ : V → ℝ} (hφ : φ ∈ G.unitSphere) :
    (fun x ↦ |φ x|) ∈ G.unitSphere := by
  obtain ⟨hb, h1⟩ := G.mem_unitSphere.mp hφ
  exact G.mem_unitSphere.mpr ⟨fun x hx ↦ by simp [hb x hx], by simpa only [sq_abs] using h1⟩

theorem energy_abs_le (φ : V → ℝ) : G.energy (fun x ↦ |φ x|) ≤ G.energy φ := by
  have hab : ∀ a b : ℝ, (|a| - |b|) ^ 2 ≤ (a - b) ^ 2 := fun a b ↦ by
    nlinarith [sq_abs a, sq_abs b, abs_mul a b, le_abs_self (a * b)]
  have hsum : ∑ x, ∑ y, G.w x y * (|φ x| - |φ y|) ^ 2 ≤ ∑ x, ∑ y, G.w x y * (φ x - φ y) ^ 2 :=
    Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦
      mul_le_mul_of_nonneg_left (hab (φ x) (φ y)) (G.w_nonneg x y)
  have hhalf := div_le_div_of_nonneg_right hsum (zero_le_two : (0 : ℝ) ≤ 2)
  simp only [energy, sq_abs]
  linarith

/-- If φ minimizes the energy on the unit sphere, so does |φ|. -/
theorem isMinOn_abs {φ : V → ℝ} (hmin : IsMinOn G.energy G.unitSphere φ) :
    IsMinOn G.energy G.unitSphere (fun x ↦ |φ x|) :=
  isMinOn_iff.mpr fun u hu ↦ (G.energy_abs_le φ).trans (isMinOn_iff.mp hmin u hu)

/-- A nonnegative eigenvector that vanishes at an interior vertex vanishes at its neighbours. -/
theorem eq_zero_of_adj {ψ : V → ℝ} {μ : ℝ} (hψ : ∀ y, 0 ≤ ψ y)
    (heq : ∀ x, x ∉ G.boundary → G.laplacian ψ x = G.b x * ψ x + μ * ψ x)
    {x y : {x // x ∉ G.boundary}} (hadj : G.interiorGraph.Adj x y) (hx : ψ x.1 = 0) :
    ψ y.1 = 0 := by
  have hL := heq x.1 x.2
  simp only [laplacian, hx, zero_sub, mul_neg, Finset.sum_neg_distrib, neg_eq_zero, mul_zero,
    add_zero] at hL
  simp only [interiorGraph, SimpleGraph.fromRel_adj] at hadj
  have hw : 0 < G.w x.1 y.1 := by
    rcases hadj.2 with h | h
    · exact h
    · rwa [G.w_symm]
  have hprod := (Finset.sum_eq_zero_iff_of_nonneg fun z _ ↦
    mul_nonneg (G.w_nonneg x.1 z) (hψ z)).mp hL y.1 (Finset.mem_univ _)
  exact (mul_eq_zero.mp hprod).resolve_left hw.ne'

/-- A nonnegative eigenvector that vanishes at an interior vertex vanishes on its component of
the interior graph. -/
theorem eq_zero_of_reachable {ψ : V → ℝ} {μ : ℝ} (hψ : ∀ y, 0 ≤ ψ y)
    (heq : ∀ x, x ∉ G.boundary → G.laplacian ψ x = G.b x * ψ x + μ * ψ x)
    {x y : {x // x ∉ G.boundary}} (hxy : G.interiorGraph.Reachable x y) (hx : ψ x.1 = 0) :
    ψ y.1 = 0 := by
  obtain ⟨p⟩ := hxy
  revert hx
  induction p with
  | nil => exact id
  | cons hadj _ ih => exact fun hx ↦ ih (G.eq_zero_of_adj hψ heq hadj hx)

/-- **Principal eigenvector.** If the interior graph is connected, there is a unit function that
vanishes on the boundary, is positive at every interior vertex, and satisfies
(L φ)(x) = b(x)·φ(x) + λ₁·φ(x) at every interior vertex. -/
theorem exists_pos_eigenvector (hconn : G.interiorGraph.Connected) :
    ∃ φ ∈ G.unitSphere, (∀ x, x ∉ G.boundary → 0 < φ x) ∧
      ∀ x, x ∉ G.boundary → G.laplacian φ x = G.b x * φ x + G.principalEigenvalue * φ x := by
  obtain ⟨x₀⟩ := hconn.nonempty
  obtain ⟨φ, hφ, hmin⟩ := G.exists_isMinOn_energy ⟨x₀.1, x₀.2⟩
  have hψ := G.abs_mem_unitSphere hφ
  have hψmin := G.isMinOn_abs hmin
  have heq : ∀ x, x ∉ G.boundary → G.laplacian (fun y ↦ |φ y|) x =
      G.b x * |φ x| + G.principalEigenvalue * |φ x| := fun x hx ↦ by
    rw [G.principalEigenvalue_eq hψ hψmin]
    exact G.laplacian_eq_of_isMinOn hψ hψmin hx
  refine ⟨fun y ↦ |φ y|, hψ, fun x hx ↦ ?_, heq⟩
  refine (abs_nonneg (φ x)).lt_of_ne fun h0 ↦ ?_
  have hall : ∀ z, |φ z| = 0 := by
    intro z
    by_cases hz : z ∈ G.boundary
    · rw [(G.mem_unitSphere.mp hφ).1 z hz, abs_zero]
    · exact G.eq_zero_of_reachable (ψ := fun y ↦ |φ y|) (fun y ↦ abs_nonneg (φ y)) heq
        (hconn.preconnected ⟨x, hx⟩ ⟨z, hz⟩) h0.symm
  have h1 := (G.mem_unitSphere.mp hψ).2
  simp only [hall] at h1
  norm_num at h1

end SemioticGraph
