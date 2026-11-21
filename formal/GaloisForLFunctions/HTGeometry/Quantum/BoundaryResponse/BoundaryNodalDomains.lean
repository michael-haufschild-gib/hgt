import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.LayeredModes
import GaloisForLFunctions.HTGeometry.FiniteGraphTemporalCurvatureLaw

/-!
# Many boundary nodal domains in a finite network

This is a finite-network counterpart to the boundary-nodal construction of
Enciso, Pistoia and Provenzano (arXiv:2611.24195, Theorem 1.1). A connected
boundary graph is preserved by the direct edges of the realization. Its
low response eigenvectors are simple and each has a discrete signed support
graph with arbitrarily many vertices.
-/

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

open WeightedGraph

noncomputable section

/-- Horizontal edges join opposite signs within a color. Vertical edges
join different colors at the same layer. -/
def layerBoundaryGraph (K N : ℕ) : SimpleGraph (LayeredBoundary K N) where
  Adj v u := (v.2 = u.2 ∧ v.1 ≠ u.1) ∨ (v.1 = u.1 ∧ v.2.1 ≠ u.2.1)
  symm := ⟨by
    intro v u h
    rcases h with ⟨h, hne⟩ | ⟨h, hne⟩
    · exact Or.inl ⟨h.symm, Ne.symm hne⟩
    · exact Or.inr ⟨h.symm, Ne.symm hne⟩⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.2 rfl) (fun h => h.2 rfl)⟩

/-- The chosen direct boundary graph is connected. -/
theorem layerBoundaryGraph_preconnected (K N : ℕ) : (layerBoundaryGraph K N).Preconnected := by
  rintro ⟨i, r⟩ ⟨j, s⟩
  let G := layerBoundaryGraph K N
  have hcolor : G.Reachable (i, r) (j, r) := by
    by_cases h : i = j
    · subst j
      exact SimpleGraph.Reachable.refl _
    · exact (show G.Adj (i, r) (j, r) from Or.inl ⟨rfl, h⟩).reachable
  have hrow : G.Reachable (j, r) (j, s) := by
    by_cases h : r.1 = s.1
    · let t := (!r.1, r.2)
      have ht : r.1 ≠ t.1 := by
        change r.1 ≠ !r.1
        cases r.1 <;> simp
      have ht' : t.1 ≠ s.1 := fun e => ht (h.trans e.symm)
      exact (show G.Adj (j, r) (j, t) from Or.inr ⟨rfl, ht⟩).reachable.trans
        (show G.Adj (j, t) (j, s) from Or.inr ⟨rfl, ht'⟩).reachable
    · exact (show G.Adj (j, r) (j, s) from Or.inr ⟨rfl, h⟩).reachable
  exact hcolor.trans hrow

private theorem colorMode_at_color (K : ℕ) {N : ℕ} (i : Fin (N + 1)) (r : Bool × Fin (K + 1)) :
    colorMode i (i, r) = if r.1 then (-1 : ℝ) else 1 := by
  unfold colorMode
  rw [if_pos rfl]
  cases r.1 <;> rfl

/-- The nonzero sites of a low eigenmode are exactly the layers of its color. -/
abbrev ColorSupport (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :=
  {v : LayeredBoundary K N // colorMode i v ≠ 0}

private theorem support_color {K N : ℕ} {i : Fin (N + 1)} (v : ColorSupport K i) : v.1.1 = i := by
  by_contra h
  exact v.2 (if_neg h)

private def colorSupportEquiv (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    (Bool × Fin (K + 1)) ≃ ColorSupport K i where
  toFun r := ⟨(i, r), by
    rw [colorMode_at_color]
    cases r.1 <;> norm_num⟩
  invFun v := v.1.2
  left_inv _ := rfl
  right_inv v := Subtype.ext (Prod.ext (support_color v).symm rfl)

/-- The strong nodal graph keeps only edges joining nonzero values of
the same sign. -/
def colorNodalGraph (K : ℕ) {N : ℕ} (i : Fin (N + 1)) : SimpleGraph (ColorSupport K i) where
  Adj v u := (layerBoundaryGraph K N).Adj v.1 u.1 ∧ 0 < colorMode i v.1 * colorMode i u.1
  symm := ⟨by
    intro v u h
    exact ⟨h.1.symm, by rw [mul_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private theorem colorMode_mul_of_opposite_sign {K N : ℕ} {i : Fin (N + 1)}
    (v u : ColorSupport K i) (h : v.1.2.1 ≠ u.1.2.1) :
    colorMode i v.1 * colorMode i u.1 = -1 := by
  rcases v with ⟨⟨j, r⟩, hj⟩
  rcases u with ⟨⟨k, s⟩, hk⟩
  have hji : j = i := support_color ⟨(j, r), hj⟩
  have hki : k = i := support_color ⟨(k, s), hk⟩
  subst j
  subst k
  change colorMode i (i, r) * colorMode i (i, s) = -1
  rw [colorMode_at_color, colorMode_at_color]
  change r.1 ≠ s.1 at h
  generalize r.1 = a at h ⊢
  generalize s.1 = b at h ⊢
  cases a <;> cases b <;> simp_all

theorem colorNodalGraph_eq_bot (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    colorNodalGraph K i = ⊥ := by
  ext v u
  change ((layerBoundaryGraph K N).Adj v.1 u.1 ∧ 0 < colorMode i v.1 * colorMode i u.1) ↔ False
  constructor
  · rintro ⟨h, hp⟩
    rcases h with ⟨_, hne⟩ | ⟨_, hne⟩
    · exact hne ((support_color v).trans (support_color u).symm)
    · rw [colorMode_mul_of_opposite_sign v u hne] at hp
      exact (not_lt_of_ge (by norm_num : (-1 : ℝ) ≤ 0)) hp
  · exact False.elim

/-- Every low mode has one boundary nodal domain per layer in each sign. -/
theorem card_colorNodalDomains (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    Nat.card (colorNodalGraph K i).ConnectedComponent = 2 * (K + 1) := by
  rw [colorNodalGraph_eq_bot]
  let e := (colorSupportEquiv K i).trans (botConnectedComponentEquiv (ColorSupport K i))
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-- The physical network realizing the layered response. -/
def layeredSeriesNetwork (K N : ℕ) : WeightedGraph (LayeredBoundary K N ⊕ SeriesInterior (LayeredBoundary K N)) :=
  (layeredBoundaryGraph K N).seriesNetwork (layerBoundaryGraph K N)

theorem layeredSeriesNetwork_boundaryEdges (K N : ℕ) (v u : LayeredBoundary K N) :
    0 < (layeredSeriesNetwork K N).w (.inl v) (.inl u) ↔ (layerBoundaryGraph K N).Adj v u := by
  rw [layeredSeriesNetwork, seriesNetwork_boundary_weight_pos_iff]
  exact ⟨And.left, fun h => ⟨h, layeredBoundaryGraph_weight_pos h.ne⟩⟩

private theorem residualWeight_pos {K N : ℕ} (p : SeriesInterior (LayeredBoundary K N)) :
    0 < ((layeredBoundaryGraph K N).residualBoundary (layerBoundaryGraph K N)).w p.1.1 p.1.2 := by
  classical
  let G := layeredBoundaryGraph K N
  let B := layerBoundaryGraph K N
  have h : 0 < G.w p.1.1 p.1.2 := layeredBoundaryGraph_weight_pos p.2
  change 0 < G.w p.1.1 p.1.2 - (if B.Adj p.1.1 p.1.2 then G.w p.1.1 p.1.2 / 2 else 0)
  split_ifs <;> linarith only [h]

/-- The simple graph of positive physical conductances. -/
def positiveNetworkSupport {V : Type*} (G : WeightedGraph V) : SimpleGraph V where
  Adj v u := 0 < G.w v u
  symm := ⟨fun v u h => by rw [G.w_symm u v]; exact h⟩
  loopless := ⟨fun v h => by rw [G.w_diag] at h; exact (lt_irrefl 0) h⟩

/-- Every interior vertex is attached to its endpoints, and every two
distinct boundary vertices are joined through an interior vertex. -/
theorem layeredSeriesNetwork_preconnected (K N : ℕ) :
    (positiveNetworkSupport (layeredSeriesNetwork K N)).Preconnected := by
  let V := LayeredBoundary K N
  let G := positiveNetworkSupport (layeredSeriesNetwork K N)
  let H := (layeredBoundaryGraph K N).residualBoundary (layerBoundaryGraph K N)
  have hfirst (p : SeriesInterior V) : G.Adj (.inl p.1.1) (.inr p) := by
    change 0 < (if p.1.1 = p.1.1 then H.w p.1.1 p.1.2 else 0) +
      (if p.1.1 = p.1.2 then H.w p.1.1 p.1.2 else 0)
    rw [if_pos rfl, if_neg p.2, add_zero]
    exact residualWeight_pos p
  have hsecond (p : SeriesInterior V) : G.Adj (.inl p.1.2) (.inr p) := by
    change 0 < (if p.1.2 = p.1.1 then H.w p.1.1 p.1.2 else 0) +
      (if p.1.2 = p.1.2 then H.w p.1.1 p.1.2 else 0)
    rw [if_neg (Ne.symm p.2), if_pos rfl, zero_add]
    exact residualWeight_pos p
  have hboundary (v u : V) : G.Reachable (.inl v) (.inl u) := by
    by_cases h : v = u
    · subst u
      exact SimpleGraph.Reachable.refl _
    · let p : SeriesInterior V := ⟨(v, u), h⟩
      exact (hfirst p).reachable.trans (hsecond p).reachable.symm
  let endpoint : V ⊕ SeriesInterior V → V := fun
    | .inl v => v
    | .inr p => p.1.1
  have hattach (z : V ⊕ SeriesInterior V) : G.Reachable z (.inl (endpoint z)) := by
    cases z with
    | inl v => exact SimpleGraph.Reachable.refl _
    | inr p => exact (hfirst p).reachable.symm
  intro x y
  exact (hattach x).trans ((hboundary (endpoint x) (endpoint y)).trans (hattach y).symm)

/-- Outward boundary current of the harmonic midpoint extension. -/
def layeredBoundaryResponse (K N : ℕ) (x : LayeredBoundary K N → ℝ) (v : LayeredBoundary K N) : ℝ :=
  (layeredSeriesNetwork K N).networkFlux (seriesMidpointExtension x) (.inl v)

theorem layeredBoundaryResponse_harmonic (K N : ℕ) (x : LayeredBoundary K N → ℝ)
    (p : SeriesInterior (LayeredBoundary K N)) :
    (layeredSeriesNetwork K N).networkFlux (seriesMidpointExtension x) (.inr p) = 0 :=
  (layeredBoundaryGraph K N).seriesMidpointExtension_harmonic (layerBoundaryGraph K N) x p

/-- The harmonic extension of any boundary profile in this network is unique. -/
theorem layeredSeriesNetwork_harmonic_unique (K N : ℕ) (x : LayeredBoundary K N → ℝ)
    (y : LayeredBoundary K N ⊕ SeriesInterior (LayeredBoundary K N) → ℝ) :
    ((∀ v, y (.inl v) = x v) ∧ (∀ p, (layeredSeriesNetwork K N).networkFlux y (.inr p) = 0)) →
      y = seriesMidpointExtension x := by
  rintro ⟨hbound, hint⟩
  funext z
  cases z with
  | inl v => exact hbound v
  | inr p =>
    have h := hint p
    rw [layeredSeriesNetwork, seriesNetwork_interior_flux, hbound, hbound] at h
    have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (residualWeight_pos p).ne')
    change y (.inr p) = (x p.1.1 + x p.1.2) / 2
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    rw [mul_comm (y (.inr p))]
    exact he

private theorem layeredBoundaryResponse_eq (K N : ℕ) (x : LayeredBoundary K N → ℝ)
    (v : LayeredBoundary K N) :
    layeredBoundaryResponse K N x v = (layeredBoundaryGraph K N).networkFlux x v :=
  (layeredBoundaryGraph K N).seriesNetwork_boundary_flux (layerBoundaryGraph K N) x v

/-- There are exactly the listed simple positive response eigenvalues below
the upper level. -/
theorem layeredBoundaryResponse_smallPositiveEigenpair_iff (K N : ℕ)
    (level : Set.Ioo (0 : ℝ) (upperBoundaryLevel K N)) (x : LayeredBoundary K N → ℝ) :
    (x ≠ 0 ∧ ∀ v, layeredBoundaryResponse K N x v = (level : ℝ) * x v) ↔
      ∃ i : Fin (N + 1), (level : ℝ) = colorEigenvalue K i ∧
        ∃ c : ℝ, c ≠ 0 ∧ x = fun v => c * colorMode i v := by
  simpa only [layeredBoundaryResponse_eq] using smallPositiveEigenpair_iff K N level x

/-- Each of the first `N+1` positive eigenvalues is simple, and its color
mode has `2(K+1)` boundary nodal domains. -/
theorem layeredBoundaryResponse_manyNodalDomains (K N : ℕ) (i : Fin (N + 1)) :
    0 < colorEigenvalue K i ∧ colorEigenvalue K i < upperBoundaryLevel K N ∧
      (colorMode i : LayeredBoundary K N → ℝ) ≠ 0 ∧
      (∀ v, layeredBoundaryResponse K N (colorMode i) v = colorEigenvalue K i * colorMode i v) ∧
      Nat.card (colorNodalGraph K i).ConnectedComponent = 2 * (K + 1) := by
  refine ⟨(colorEigenvalue_bounds K i).1, (colorEigenvalue_bounds K i).2, colorMode_ne_zero K i,
    ?_, card_colorNodalDomains K i⟩
  intro v
  rw [layeredBoundaryResponse_eq, layeredBoundaryGraph_flux_colorMode]

#print axioms layerBoundaryGraph_preconnected
#print axioms card_colorNodalDomains
#print axioms layeredSeriesNetwork_boundaryEdges
#print axioms layeredSeriesNetwork_preconnected
#print axioms layeredSeriesNetwork_harmonic_unique
#print axioms layeredBoundaryResponse_smallPositiveEigenpair_iff
#print axioms layeredBoundaryResponse_manyNodalDomains

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
