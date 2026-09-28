/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Graph.Existence

/-!
# A concrete instance of the finite-graph theorem

`SemioticGraph.triangle` is the complete graph on three vertices with unit weights and vertex 0 as
the boundary, with κ = γ = μ = 1 (so a = 1), b = 2, c = 1 and p = 2. Its interior graph is
connected, its weights lie in {0, 1}, and the function (0, 1, 1) has energy -2, so its principal
eigenvalue is negative. `SemioticGraph.exists_pos_triangle` applies
`SemioticGraph.exists_pos_graph_of_unweighted` to it, which shows that the hypotheses of the graph
theorem can be met.

Separately, `SemioticGraph.triangle_isSolution` checks directly that (0, 2, 2), which is positive at
both interior vertices, is a solution. Its gradient norm there is 2
(`SemioticGraph.triangle_gradNorm`), so the gradient term of the equation is active.

## Main definitions

- `SemioticGraph.triangle` — the example

## Main statements

- `SemioticGraph.exists_pos_triangle` — a solution on the example that is positive at both
  interior vertices
- `SemioticGraph.triangle_isSolution` — (0, 2, 2) is a solution
- `SemioticGraph.triangle_gradNorm` — its gradient norm is 2 at both interior vertices

## Implementation notes

The weights are 1 on the diagonal too. Diagonal weights do not enter the Laplacian, the gradient
norm or the energy.

## Tags

graph Laplacian, example
-/

noncomputable section

namespace SemioticGraph

/-- The complete graph on `Fin 3` with unit weights and boundary {0}, with κ = γ = μ = 1, b = 2,
c = 1 and p = 2. -/
def triangle : SemioticGraph (Fin 3) where
  w _ _ := 1
  w_nonneg _ _ := zero_le_one
  w_symm _ _ := rfl
  boundary := {0}
  κ _ := 1
  γ _ := 1
  μ _ := 1
  b _ := 2
  c _ := 1
  p := 2
  κ_bounds _ := ⟨zero_le_one, le_rfl⟩
  γ_bounds _ := ⟨zero_le_one, le_rfl⟩
  μ_bounds _ := ⟨zero_le_one, le_rfl⟩
  c_pos _ := zero_lt_one
  one_lt_p := one_lt_two

theorem triangle_w (x y : Fin 3) : triangle.w x y = 1 := rfl

theorem triangle_b (x : Fin 3) : triangle.b x = 2 := rfl

theorem mem_triangle_boundary {x : Fin 3} : x ∈ triangle.boundary ↔ x = 0 :=
  Set.mem_singleton_iff

/-- The interior graph of the example is connected: its two vertices are joined by an edge. -/
theorem triangle_connected : triangle.interiorGraph.Connected := by
  have h1 : (1 : Fin 3) ∉ triangle.boundary := mem_triangle_boundary.not.mpr (by decide)
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨⟨1, h1⟩, fun v ↦ ?_⟩
  by_cases hv : (⟨1, h1⟩ : {x // x ∉ triangle.boundary}) = v
  · subst hv
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨hv, Or.inl zero_lt_one⟩

theorem triangle_energy : triangle.energy ![0, 1, 1] = -2 := by
  norm_num [energy, Fin.sum_univ_three, triangle_w, triangle_b, Matrix.cons_val_two]

/-- The principal eigenvalue of the example is negative. -/
theorem triangle_principalEigenvalue_neg : triangle.principalEigenvalue < 0 := by
  refine triangle.principalEigenvalue_neg (u := ![0, 1, 1]) (fun x hx ↦ ?_) ?_
  · simp [mem_triangle_boundary.mp hx]
  · rw [triangle_energy]
    norm_num

/-- The graph theorem applies to the example: there is a solution that is positive at both
interior vertices. -/
theorem exists_pos_triangle :
    ∃ u : Fin 3 → ℝ, triangle.IsSolution u ∧ ∀ x, x ∉ triangle.boundary → 0 < u x :=
  triangle.exists_pos_graph_of_unweighted (fun _ _ ↦ Or.inr rfl) triangle_connected
    triangle_principalEigenvalue_neg

theorem triangle_a (x : Fin 3) : triangle.a x = 1 := by
  change (1 : ℝ) * 1 * 1 = 1
  norm_num

theorem triangle_c (x : Fin 3) : triangle.c x = 1 := rfl

theorem triangle_p : triangle.p = 2 := rfl

/-- The function (0, 2, 2) equals 2 at both interior vertices. -/
private theorem sol_eq_two {x : Fin 3} (hx : x ∉ triangle.boundary) :
    (![0, 2, 2] : Fin 3 → ℝ) x = 2 := by
  have key : ∀ y : Fin 3, y ≠ 0 → y = 1 ∨ y = 2 := by decide
  rcases key x (mt mem_triangle_boundary.mpr hx) with rfl | rfl <;> rfl

/-- The gradient norm of (0, 2, 2) is 2 at both interior vertices. -/
theorem triangle_gradNorm {x : Fin 3} (hx : x ∉ triangle.boundary) :
    triangle.gradNorm ![0, 2, 2] x = 2 := by
  rw [gradNorm, Fin.sum_univ_three, sol_eq_two hx, Real.sqrt_eq_iff_mul_self_eq_of_pos two_pos]
  norm_num [triangle_w, Matrix.cons_val_two]

/-- **An explicit solution.** (0, 2, 2) solves the example. At each interior vertex the Laplacian
and the gradient norm are both 2, so the equation reads 2 = 1·2 + 2·2 - 1·2², with a nonzero
gradient term. -/
theorem triangle_isSolution : triangle.IsSolution ![0, 2, 2] := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ by simp [mem_triangle_boundary.mp hx]⟩
  have hu := sol_eq_two hx
  have hL : triangle.laplacian ![0, 2, 2] x = 2 := by
    rw [laplacian, Fin.sum_univ_three, hu]
    norm_num [triangle_w, Matrix.cons_val_two]
  rw [hL, triangle_gradNorm hx, hu, triangle_a, triangle_b, triangle_c, triangle_p,
    max_eq_left (zero_le_two : (0 : ℝ) ≤ 2), Real.rpow_two]
  norm_num

end SemioticGraph

end
