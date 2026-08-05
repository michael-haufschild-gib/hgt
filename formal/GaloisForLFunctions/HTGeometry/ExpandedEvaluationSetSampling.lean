import GaloisForLFunctions.HTGeometry.ExpandedEvaluationRelationIdeal
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

/-!
# Sampling the expanded evaluation matrix inside a prescribed region

The sampling reduction places the nodes anywhere in the plane, but every consumer of the full-rank
datum must place them inside a region — an upper half-plane, a disc, a chart.  Confinement costs
nothing:

* linear independence of the *restricted* family already produces a node packet inside the set;
* and for an entire family the restriction is free at any accumulation point, because a vanishing
  linear combination on a set with an accumulation point is a vanishing entire function.

Hence a nonempty open region — in particular the upper half-plane — never obstructs the full-rank
datum: the exact obstruction remains the relation ideal, unchanged by where one is allowed to look.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-! ## Confining the nodes -/

/-- **Nodes can be taken inside any set on which the family remains independent.** -/
theorem exists_node_packet_mem_mulVec_injective {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n q : ℕ} (F : Fin n → ℂ → ℂ) (exponent : κ → (Fin n →₀ ℕ)) (S : Set ℂ)
    (h : LinearIndependent ℂ
      (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c))) :
    ∃ z : κ × Fin (q + 1) → ℂ, (∀ p, z p ∈ S) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  classical
  obtain ⟨φ, hdet⟩ := exists_coordinateMinor_det_ne_zero _ h
  have hmat :
      expandedDifferentialEvaluationMatrix q n (fun p => ((φ p : ℂ))) exponent
          (fun p => F p.2 ((φ p.1 : ℂ)))
        = coordinateMinor
            (fun c : κ × Fin (q + 1) =>
              Set.restrict S (expandedMonomialFamily F exponent q c)) φ := by
    ext b c
    rfl
  have hdet' :
      (expandedDifferentialEvaluationMatrix q n (fun p => ((φ p : ℂ))) exponent
        (fun p => F p.2 ((φ p.1 : ℂ)))).det ≠ 0 := by
    rw [hmat]; exact hdet
  exact ⟨fun p => ((φ p : ℂ)), fun p => (φ p).2,
    injective_of_expandedEvaluation_det_ne_zero hdet',
    mulVec_injective_of_det_ne_zero hdet'⟩

/-! ## Restriction is free for entire families -/

/-- **An analytic family stays independent on any subset with an accumulation point.**  A vanishing
combination on such a subset is an analytic function vanishing frequently near the accumulation
point, hence identically on the region. -/
theorem linearIndependent_restrict_of_analyticOnNhd {N : Type*} [Fintype N] [DecidableEq N]
    {Ω : Set ℂ} (hΩ : IsPreconnected Ω) (g : N → ℂ → ℂ)
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) Ω)
    (hind : LinearIndependent ℂ (fun j => Set.restrict Ω (g j)))
    {S : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hacc : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ S) :
    LinearIndependent ℂ (fun j => Set.restrict S (g j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hfun : ∀ w ∈ S, ∑ j, c j * g j w = 0 := by
    intro w hw
    have := congrFun hc ⟨w, hw⟩
    simpa [Set.restrict] using this
  have hanalytic : AnalyticOnNhd ℂ (fun w => ∑ j, c j * g j w) Ω := by
    have hsum : (fun w : ℂ => ∑ j, c j * g j w)
        = ∑ j ∈ Finset.univ, (fun w : ℂ => c j * g j w) := by
      funext w; simp
    rw [hsum]
    exact Finset.analyticOnNhd_sum _ fun j _ => analyticOnNhd_const.mul (hg j)
  have hfreq : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), (fun w => ∑ j, c j * g j w) z = 0 :=
    hacc.mono fun z hz => hfun z hz
  have hzero : Set.EqOn (fun w => ∑ j, c j * g j w) 0 Ω :=
    hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩ hz₀ hfreq
  have hglobal : ∑ j, c j • (fun w : ↥Ω => g j w) = 0 := by
    funext w
    have := hzero w.2
    simpa [Finset.sum_apply] using this
  exact (Fintype.linearIndependent_iff.mp hind) c hglobal

/-- **An entire family stays independent on any set with an accumulation point.** -/
theorem linearIndependent_restrict_of_entire {N : Type*} [Fintype N] [DecidableEq N]
    (g : N → ℂ → ℂ) (hg : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ)
    (hind : LinearIndependent ℂ g) {S : Set ℂ} {z₀ : ℂ}
    (hacc : ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ S) :
    LinearIndependent ℂ (fun j => Set.restrict S (g j)) := by
  refine linearIndependent_restrict_of_analyticOnNhd isPreconnected_univ g hg ?_
    (Set.mem_univ z₀) hacc
  rw [Fintype.linearIndependent_iff]
  intro c hc
  refine (Fintype.linearIndependent_iff.mp hind) c ?_
  funext w
  have := congrFun hc ⟨w, Set.mem_univ w⟩
  simpa using this

/-- A nonempty open set has an accumulation point inside itself. -/
theorem frequently_mem_of_isOpen {S : Set ℂ} (hS : IsOpen S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) :
    ∃ᶠ z in nhdsWithin z₀ ({z₀}ᶜ), z ∈ S :=
  Filter.Eventually.frequently (eventually_nhdsWithin_of_eventually_nhds (hS.mem_nhds hz₀))

/-! ## The regional discharge -/

/-- **Every nonempty open region carries a full-rank node packet.**  Entirety of the jets and linear
independence of the expanded monomial family — no more — place the nodes wherever one wants. -/
theorem exists_node_packet_mem_isOpen_mulVec_injective {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n q : ℕ} (F : Fin n → ℂ → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (hF : ∀ k, AnalyticOnNhd ℂ (F k) Set.univ)
    (hind : LinearIndependent ℂ (expandedMonomialFamily F exponent q))
    {S : Set ℂ} (hS : IsOpen S) {z₀ : ℂ} (hz₀ : z₀ ∈ S) :
    ∃ z : κ × Fin (q + 1) → ℂ, (∀ p, z p ∈ S) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  classical
  have hg : ∀ c : κ × Fin (q + 1),
      AnalyticOnNhd ℂ (expandedMonomialFamily F exponent q c) Set.univ := by
    intro c
    have hbase : AnalyticOnNhd ℂ (fun w : ℂ => w ^ (c.2 : ℕ)) Set.univ :=
      analyticOnNhd_id.pow _
    have hprod : AnalyticOnNhd ℂ
        (fun w : ℂ => ∏ k ∈ (exponent c.1).support, (F k w) ^ (exponent c.1 k)) Set.univ := by
      have hpe : (fun w : ℂ => ∏ k ∈ (exponent c.1).support, (F k w) ^ (exponent c.1 k))
          = ∏ k ∈ (exponent c.1).support, (fun w : ℂ => (F k w) ^ (exponent c.1 k)) := by
        funext w; simp
      rw [hpe]
      exact Finset.analyticOnNhd_prod _ fun k _ => (hF k).pow _
    have hEq : expandedMonomialFamily F exponent q c
        = fun w : ℂ => w ^ (c.2 : ℕ) * ∏ k ∈ (exponent c.1).support, (F k w) ^ (exponent c.1 k) :=
      funext (expandedMonomialFamily_apply F exponent c)
    rw [hEq]
    exact hbase.mul hprod
  exact exists_node_packet_mem_mulVec_injective F exponent S
    (linearIndependent_restrict_of_entire _ hg hind (frequently_mem_of_isOpen hS hz₀))


/-- **The regional discharge from algebraic independence.**  Once the node coordinate and the jets
are algebraically independent *on the region*, the full-rank node packet exists inside the region —
no analyticity, no node separation, no nonvanishing hypothesis is needed on top. -/
theorem exists_node_packet_mem_of_algebraicIndependent_restrict {κ : Type*} [Fintype κ]
    [DecidableEq κ] {n q : ℕ} {F : Fin n → ℂ → ℂ} {S : Set ℂ}
    (halg : AlgebraicIndependent ℂ (fun i => Set.restrict S (jetEvaluationFamily F i)))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    ∃ z : κ × Fin (q + 1) → ℂ, (∀ p, z p ∈ S) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec :=
  exists_node_packet_mem_mulVec_injective F exponent S
    (linearIndependent_restrict_expandedMonomialFamily_of_algebraicIndependent halg hexp)

/-- **The upper half-plane carries the full-rank datum.**  This is the exact shape demanded by the
translation-rank genericity laws: nodes with positive imaginary part, pairwise distinct, on which
the expanded evaluation map is injective. -/
theorem exists_node_packet_upperHalfPlane_of_algebraicIndependent {κ : Type*} [Fintype κ]
    [DecidableEq κ] {n q : ℕ} {F : Fin n → ℂ → ℂ}
    (halg : AlgebraicIndependent ℂ
      (fun i => Set.restrict upperHalfPlane (jetEvaluationFamily F i)))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    ∃ z : κ × Fin (q + 1) → ℂ, (∀ p, 0 < (z p).im) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec :=
  exists_node_packet_mem_of_algebraicIndependent_restrict halg hexp

end GaloisForLFunctions.HTGeometry
