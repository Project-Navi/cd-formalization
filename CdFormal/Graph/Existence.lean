/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Graph.Spectral
import CdFormal.Graph.FixedPoint

/-!
# A positive solution on a finite graph

If the interior graph is connected, the principal Dirichlet eigenvalue of L - diag(b) is negative,
and every edge of positive weight between distinct interior vertices satisfies
a(x) ≤ √w(x,y), then the problem of `CdFormal.Graph.Basic` has a solution that is positive at
every interior vertex (`SemioticGraph.exists_pos_graph`).

The subsolution is ε·φ for the positive principal eigenvector φ of
`SemioticGraph.exists_pos_eigenvector` and a small ε > 0; the supersolution is
`SemioticGraph.plateau` M for a large M; `SemioticGraph.exists_isSolution_between` gives a
solution between them. Every constant is constructed from the data.

On a graph with weights in {0, 1}, the edge-dominance condition follows from 0 ≤ a ≤ 1
(`SemioticGraph.exists_pos_graph_of_unweighted`).

## Main statements

- `SemioticGraph.exists_pos_graph` — existence of a solution positive at every interior vertex
- `SemioticGraph.exists_pos_graph_of_unweighted` — the same for weights in {0, 1}, without the
  edge-dominance hypothesis

## Implementation notes

The edge-dominance condition is used only to make the fixed-point map monotone; it is a sufficient
condition for this proof, not a necessary condition for existence. The discretization (unnormalized
weights, the symmetric gradient norm, zero boundary values entering through boundary edges) is the
one selected for this formalization.

## Acknowledgment

The finite-graph formulation of the problem and the proof route (finite-dimensional inverse
positivity, positive principal eigendata, then the order-theoretic fixed-point core
`monotone_fixed_point_between`) were proposed by Andrew Edmark (@aedmark). Here inverse positivity
takes the form of the Jacobi splitting in `CdFormal.Graph.FixedPoint`. The specific discretization
and the edge-dominance hypothesis were chosen for this formalization and are not claimed to be his.

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.

## Tags

graph Laplacian, positive solution, sub- and supersolutions, principal eigenvalue
-/

namespace SemioticGraph

variable {V : Type*} [Fintype V] (G : SemioticGraph V)

/-- **Positive solution on a finite graph.** If the interior graph is connected, a(x) ≤ √w(x,y)
for every edge of positive weight between distinct interior vertices x and y, and the principal
eigenvalue of L - diag(b) is negative, then there is a solution that is positive at every interior
vertex. -/
theorem exists_pos_graph (hconn : G.interiorGraph.Connected)
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    (hneg : G.principalEigenvalue < 0) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ x, x ∉ G.boundary → 0 < u x := by
  obtain ⟨φ, hφ, hφpos, hφeq⟩ := G.exists_pos_eigenvector hconn
  have hp1 : 0 < G.p - 1 := sub_pos.mpr G.one_lt_p
  have hφnn : ∀ y, 0 ≤ φ y := fun y ↦ by
    by_cases hy : y ∈ G.boundary
    · rw [(G.mem_unitSphere.mp hφ).1 y hy]
    · exact (hφpos y hy).le
  have hφ1 : ∀ y, φ y ≤ 1 := fun y ↦ (abs_le.mp (G.abs_le_one_of_mem_unitSphere hφ y)).2
  -- The subsolution: ε·φ with c(x)·ε^(p-1) ≤ -λ₁ for every x.
  have hm : 0 < -G.principalEigenvalue := neg_pos.mpr hneg
  have hC : 0 ≤ ∑ x, G.c x := Finset.sum_nonneg fun x _ ↦ (G.c_pos x).le
  obtain ⟨t, ht, ht1, htc⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ x, G.c x * t ≤ -G.principalEigenvalue := by
    refine ⟨-G.principalEigenvalue / (-G.principalEigenvalue + ∑ x, G.c x),
      div_pos hm (by linarith), (div_le_one (by linarith)).mpr (by linarith), fun x ↦ ?_⟩
    have hcx : G.c x ≤ ∑ y, G.c y :=
      Finset.single_le_sum (fun y _ ↦ (G.c_pos y).le) (Finset.mem_univ x)
    have h1 := mul_le_mul_of_nonneg_right hcx hm.le
    have h2 := mul_pos hm hm
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith
  obtain ⟨ε, hε, hε1, hεt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ^ (G.p - 1) = t :=
    ⟨t ^ (1 / (G.p - 1)), Real.rpow_pos_of_pos ht _,
      Real.rpow_le_one ht.le ht1 (one_div_pos.mpr hp1).le, by
        rw [← Real.rpow_mul ht.le, one_div_mul_cancel hp1.ne', Real.rpow_one]⟩
  have hεc : ∀ x, G.c x * ε ^ (G.p - 1) ≤ -G.principalEigenvalue := fun x ↦ by
    rw [hεt]
    exact htc x
  -- The supersolution: `G.plateau M` with a(x)²/4 + b(x) ≤ c(x)·M^(p-1) for every x.
  obtain ⟨M, hM1, hMc⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ x, G.a x ^ 2 / 4 + G.b x ≤ G.c x * M ^ (G.p - 1) := by
    have hR0 : 0 ≤ ∑ y, (|G.b y| + G.a y ^ 2 / 4) / G.c y :=
      Finset.sum_nonneg fun y _ ↦ div_nonneg (by positivity) (G.c_pos y).le
    have hR : ∀ x, G.a x ^ 2 / 4 + G.b x ≤
        G.c x * (1 + ∑ y, (|G.b y| + G.a y ^ 2 / 4) / G.c y) := by
      intro x
      have hcx := G.c_pos x
      have hterm : (|G.b x| + G.a x ^ 2 / 4) / G.c x ≤
          ∑ y, (|G.b y| + G.a y ^ 2 / 4) / G.c y :=
        Finset.single_le_sum (fun y _ ↦ div_nonneg (by positivity) (G.c_pos y).le)
          (Finset.mem_univ x)
      calc G.a x ^ 2 / 4 + G.b x ≤ |G.b x| + G.a x ^ 2 / 4 := by
            linarith [le_abs_self (G.b x)]
        _ = G.c x * ((|G.b x| + G.a x ^ 2 / 4) / G.c x) := (mul_div_cancel₀ _ hcx.ne').symm
        _ ≤ G.c x * ∑ y, (|G.b y| + G.a y ^ 2 / 4) / G.c y :=
            mul_le_mul_of_nonneg_left hterm hcx.le
        _ ≤ G.c x * (1 + ∑ y, (|G.b y| + G.a y ^ 2 / 4) / G.c y) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hcx.le
    refine ⟨(1 + ∑ y, (|G.b y| + G.a y ^ 2 / 4) / G.c y) ^ (1 / (G.p - 1)),
      Real.one_le_rpow (le_add_of_nonneg_right hR0) (one_div_pos.mpr hp1).le, fun x ↦ ?_⟩
    rw [← Real.rpow_mul (add_nonneg zero_le_one hR0), one_div_mul_cancel hp1.ne', Real.rpow_one]
    exact hR x
  -- The shift K of the fixed-point map.
  have hT : ∀ x, 0 ≤ G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) + |G.b x| :=
    fun x ↦ add_nonneg (add_nonneg (mul_nonneg (G.a_nonneg x)
      (Finset.sum_nonneg fun y _ ↦ Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (G.c_pos x).le (by linarith [G.one_lt_p]))
        (Real.rpow_nonneg (by linarith) _))) (abs_nonneg _)
  have hK : 0 < 1 + ∑ x, (G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) + |G.b x|) := by
    linarith [Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) ↦ hT x]
  have hKM : ∀ x, G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) - G.b x ≤
      1 + ∑ x, (G.a x * ∑ y, √(G.w x y) + G.c x * G.p * M ^ (G.p - 1) + |G.b x|) := fun x ↦ by
    have := Finset.single_le_sum (fun y _ ↦ hT y) (Finset.mem_univ x)
    linarith [neg_abs_le (G.b x)]
  obtain ⟨u, hu, hbounds⟩ := G.exists_isSolution_between hdom hK hKM (lo := fun y ↦ ε * φ y)
    (hi := G.plateau M) (fun y ↦ mul_nonneg hε.le (hφnn y))
    (fun y ↦ by
      by_cases hy : y ∈ G.boundary
      · simp [(G.mem_unitSphere.mp hφ).1 y hy, G.plateau_of_mem hy]
      · rw [G.plateau_of_notMem hy]
        exact (mul_le_one₀ hε1 (hφnn y) (hφ1 y)).trans hM1)
    (G.plateau_le (by linarith))
    (fun y hy ↦ by simp [(G.mem_unitSphere.mp hφ).1 y hy])
    (fun y hy ↦ G.plateau_of_mem hy)
    (fun x hx ↦ G.smul_subsolution hφnn hφ1 hφeq hε hεc hx)
    (fun x hx ↦ G.plateau_supersolution (by linarith) hMc hx)
  exact ⟨u, hu, fun x hx ↦ lt_of_lt_of_le (mul_pos hε (hφpos x hx)) (hbounds x).1⟩

/-- **Unweighted graphs.** If every weight is 0 or 1, the edge-dominance condition holds because
0 ≤ a ≤ 1, so connectivity of the interior and a negative principal eigenvalue suffice. -/
theorem exists_pos_graph_of_unweighted (hw : ∀ x y, G.w x y = 0 ∨ G.w x y = 1)
    (hconn : G.interiorGraph.Connected) (hneg : G.principalEigenvalue < 0) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ x, x ∉ G.boundary → 0 < u x := by
  refine G.exists_pos_graph hconn (fun x y _ _ _ hxy ↦ ?_) hneg
  rcases hw x y with h | h
  · exact absurd h hxy.ne'
  · rw [h, Real.sqrt_one]
    exact G.a_le_one x

end SemioticGraph
