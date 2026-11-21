import GaloisForLFunctions.HTGeometry.WeightedGraphSpectralGap
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Boundary response of a subdivided network

Keep half of each designated boundary conductance and route the remaining
conductances through interior vertices. The ordered pair of endpoints
labels each interior vertex, so the two orientations contribute half of
the residual conductance each. Harmonic extension by the endpoint
midpoints preserves the full boundary response.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.WeightedGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Outward current of an unnormalized graph Laplacian. -/
def networkFlux (G : WeightedGraph V) (x : V → ℝ) (v : V) : ℝ :=
  ∑ u, G.w v u * (x v - x u)

omit [DecidableEq V] in
/-- Summing voltage times outward current gives the Dirichlet energy. -/
theorem dirichlet_self_eq_sum_mul_networkFlux (G : WeightedGraph V) (x : V → ℝ) :
    G.dirichlet x x = ∑ v, x v * G.networkFlux x v := by
  rw [G.dirichlet_self_eq, massInner, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [networkFlux, mass, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- The vertices of the interior are the ordered pairs of distinct
boundary vertices. -/
abbrev SeriesInterior (V : Type*) := {p : V × V // p.1 ≠ p.2}

/-- Direct boundary edges retain half of their designated conductance. -/
def retainedBoundary (G : WeightedGraph V) (B : SimpleGraph V) : WeightedGraph V := by
  classical
  refine ⟨fun v u => if B.Adj v u then G.w v u / 2 else 0, ?_, ?_, ?_⟩
  · intro v u
    by_cases h : B.Adj v u
    · rw [if_pos h, if_pos h.symm, G.w_symm v u]
    · have hr : ¬ B.Adj u v := fun h' => h h'.symm
      rw [if_neg h, if_neg hr]
  · intro v u
    change 0 ≤ (if B.Adj v u then G.w v u / 2 else 0)
    split_ifs
    · exact div_nonneg (G.w_nonneg v u) (by norm_num)
    · exact le_rfl
  · intro v
    exact if_neg (fun h => h.ne rfl)

/-- The conductance left to route through the interior. -/
def residualBoundary (G : WeightedGraph V) (B : SimpleGraph V) : WeightedGraph V where
  w v u := G.w v u - (G.retainedBoundary B).w v u
  w_symm v u := by rw [G.w_symm v u, (G.retainedBoundary B).w_symm v u]
  w_nonneg v u := by
    classical
    have h := G.w_nonneg v u
    change 0 ≤ G.w v u - (if B.Adj v u then G.w v u / 2 else 0)
    split_ifs <;> linarith only [h]
  w_diag v := by rw [G.w_diag, (G.retainedBoundary B).w_diag, sub_zero]

private def wireWeight (H : WeightedGraph V) (v : V) (p : V × V) : ℝ :=
  (if v = p.1 then H.w p.1 p.2 else 0) + (if v = p.2 then H.w p.1 p.2 else 0)

omit [Fintype V] in
private theorem wireWeight_nonneg (H : WeightedGraph V) (v : V) (p : V × V) :
    0 ≤ wireWeight H v p := by
  unfold wireWeight
  apply add_nonneg <;> split_ifs <;> first | exact H.w_nonneg .. | exact le_rfl

/-- A network with the prescribed direct boundary edges and all remaining
conductance carried by the ordered interior paths. -/
def seriesNetwork (G : WeightedGraph V) (B : SimpleGraph V) : WeightedGraph (V ⊕ SeriesInterior V) where
  w
    | .inl v, .inl u => (G.retainedBoundary B).w v u
    | .inl v, .inr p => wireWeight (G.residualBoundary B) v p.1
    | .inr p, .inl u => wireWeight (G.residualBoundary B) u p.1
    | .inr _, .inr _ => 0
  w_symm
    | .inl v, .inl u => (G.retainedBoundary B).w_symm v u
    | .inl _, .inr _ | .inr _, .inl _ | .inr _, .inr _ => rfl
  w_nonneg
    | .inl v, .inl u => (G.retainedBoundary B).w_nonneg v u
    | .inl v, .inr p => wireWeight_nonneg (G.residualBoundary B) v p.1
    | .inr p, .inl u => wireWeight_nonneg (G.residualBoundary B) u p.1
    | .inr _, .inr _ => le_rfl
  w_diag
    | .inl v => (G.retainedBoundary B).w_diag v
    | .inr _ => rfl

/-- The direct boundary edges of the realization are precisely the
designated edges that carry positive conductance. -/
theorem seriesNetwork_boundary_weight_pos_iff (G : WeightedGraph V) (B : SimpleGraph V) (v u : V) :
    0 < (G.seriesNetwork B).w (.inl v) (.inl u) ↔ B.Adj v u ∧ 0 < G.w v u := by
  classical
  change (0 < if B.Adj v u then G.w v u / 2 else 0) ↔ _
  by_cases h : B.Adj v u
  · rw [if_pos h]
    simp only [h, true_and]
    exact ⟨fun hp => by linarith only [hp], fun hp => div_pos hp (by norm_num)⟩
  · rw [if_neg h]
    simp only [lt_irrefl, h, false_and]

/-- Extend boundary values by their arithmetic mean at each interior
vertex. -/
def seriesMidpointExtension (x : V → ℝ) : V ⊕ SeriesInterior V → ℝ
  | .inl v => x v
  | .inr p => (x p.1.1 + x p.1.2) / 2

private theorem sum_seriesInterior (F : V × V → ℝ) (hdiag : ∀ v, F (v, v) = 0) :
    (∑ p : SeriesInterior V, F p.1) = ∑ p : V × V, F p := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun p : V × V => p.1 ≠ p.2) F
  have hz : (∑ p : {p : V × V // ¬ p.1 ≠ p.2}, F p.1) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨⟨a, b⟩, hp⟩ _
    change F (a, b) = 0
    have he : a = b := not_ne_iff.mp hp
    rw [he, hdiag]
  rwa [hz, add_zero] at h

private theorem sum_wireWeight_mul (H : WeightedGraph V)
    (v : V) (F : V × V → ℝ) :
    (∑ p : V × V, wireWeight H v p * F p) =
      (∑ u, H.w v u * F (v, u)) + (∑ u, H.w u v * F (u, v)) := by
  simp only [wireWeight, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, Fintype.sum_prod_type]
  congr 1
  · rw [Finset.sum_comm]
    simp only [Fintype.sum_ite_eq]
  · simp only [Fintype.sum_ite_eq]

/-- Interior current depends only on the two endpoints of that wire. -/
theorem seriesNetwork_interior_flux (G : WeightedGraph V) (B : SimpleGraph V)
    (x : V ⊕ SeriesInterior V → ℝ) (p : SeriesInterior V) :
    (G.seriesNetwork B).networkFlux x (.inr p) = (G.residualBoundary B).w p.1.1 p.1.2 *
      (2 * x (.inr p) - (x (.inl p.1.1) + x (.inl p.1.2))) := by
  rw [networkFlux, Fintype.sum_sum_type]
  change (∑ v, wireWeight (G.residualBoundary B) v p.1 * (x (.inr p) - x (.inl v))) +
    (∑ q : SeriesInterior V, 0 * (x (.inr p) - x (.inr q))) = _
  simp only [wireWeight, zero_mul, Finset.sum_const_zero, add_zero, add_mul, ite_mul,
    Finset.sum_add_distrib, Fintype.sum_ite_eq']
  ring

/-- Midpoint extension is harmonic at all interior vertices. -/
theorem seriesMidpointExtension_harmonic (G : WeightedGraph V) (B : SimpleGraph V)
    (x : V → ℝ) (p : SeriesInterior V) :
    (G.seriesNetwork B).networkFlux (seriesMidpointExtension x) (.inr p) = 0 := by
  rw [G.seriesNetwork_interior_flux B]
  simp only [seriesMidpointExtension]
  ring

omit [DecidableEq V] in
private theorem retained_add_residual_flux (G : WeightedGraph V) (B : SimpleGraph V)
    (x : V → ℝ) (v : V) :
    (G.retainedBoundary B).networkFlux x v + (G.residualBoundary B).networkFlux x v =
      G.networkFlux x v := by
  simp only [networkFlux, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  change (G.retainedBoundary B).w v u * (x v - x u) +
    (G.w v u - (G.retainedBoundary B).w v u) * (x v - x u) = _
  ring

/-- The Dirichlet-to-Neumann response of the subdivided network is exactly
the original weighted Laplacian. -/
theorem seriesNetwork_boundary_flux (G : WeightedGraph V) (B : SimpleGraph V)
    (x : V → ℝ) (v : V) :
    (G.seriesNetwork B).networkFlux (seriesMidpointExtension x) (.inl v) = G.networkFlux x v := by
  let H := G.residualBoundary B
  let F (p : V × V) := x v - (x p.1 + x p.2) / 2
  have hdiag (u : V) : wireWeight H v (u, u) * F (u, u) = 0 := by
    simp only [wireWeight, H.w_diag, ite_self, add_zero, zero_mul]
  have hfirst : (∑ u, H.w v u * F (v, u)) = (1 / 2 : ℝ) * H.networkFlux x v := by
    rw [networkFlux, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by dsimp only [F]; ring
  have hsecond : (∑ u, H.w u v * F (u, v)) = (∑ u, H.w v u * F (v, u)) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [H.w_symm u v]
    dsimp only [F]
    rw [add_comm (x u) (x v)]
  rw [networkFlux, Fintype.sum_sum_type]
  change (G.retainedBoundary B).networkFlux x v +
    (∑ p : SeriesInterior V, wireWeight H v p.1 * F p.1) = _
  rw [sum_seriesInterior (fun p => wireWeight H v p * F p) hdiag, sum_wireWeight_mul,
    hsecond, hfirst, ← G.retained_add_residual_flux B x v]
  change (G.retainedBoundary B).networkFlux x v + ((1 / 2 : ℝ) * H.networkFlux x v +
    (1 / 2 : ℝ) * H.networkFlux x v) = (G.retainedBoundary B).networkFlux x v + H.networkFlux x v
  ring

/-- Harmonic extension preserves the boundary energy. -/
theorem seriesNetwork_dirichlet_midpoints (G : WeightedGraph V) (B : SimpleGraph V) (x : V → ℝ) :
    (G.seriesNetwork B).dirichlet (seriesMidpointExtension x) (seriesMidpointExtension x) =
      G.dirichlet x x := by
  rw [dirichlet_self_eq_sum_mul_networkFlux, dirichlet_self_eq_sum_mul_networkFlux,
    Fintype.sum_sum_type]
  simp only [G.seriesMidpointExtension_harmonic B, G.seriesNetwork_boundary_flux B,
    seriesMidpointExtension, mul_zero, Finset.sum_const_zero, add_zero]

#print axioms seriesNetwork_boundary_weight_pos_iff
#print axioms seriesMidpointExtension_harmonic
#print axioms seriesNetwork_boundary_flux
#print axioms seriesNetwork_dirichlet_midpoints

end

end GaloisForLFunctions.HTGeometry.WeightedGraph
