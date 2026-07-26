import GaloisForLFunctions.HTGeometry.EllipticNormalFormConstant
import GaloisForLFunctions.HTGeometry.EllipticMonomialRelation
import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# A lattice-periodic meromorphic function is differentially algebraic

The counting argument, assembled.  Let `f` be meromorphic in normal form on `ℂ` and invariant under
a full lattice.  If its derivative vanishes identically it satisfies `y₁ = 0`.  Otherwise:

* the poles of `f` inside the fundamental parallelogram form a finite set `S`, and a single bound `m`
  controls the pole orders of `f` and `f'` there;
* at the degree `N` supplied by the count there is a nonzero coefficient vector `c` whose
  principal-part data and value at a regular point `z₀` all vanish;
* by linearity of the principal jets, the combination `G = ∑ c_q fⁱ (f')ʲ` has no principal part at
  any point of `S`, hence no pole there; every pole is a lattice translate of a point of `S`, so `G`
  has no pole anywhere;
* a pole-free lattice-periodic function is constant on its regular locus, and `G z₀ = 0`, so `G`
  vanishes wherever it is analytic;
* at a pole the normal form gives `f = 0`, so `G · f` vanishes identically — an algebraic
  differential equation of order one.

* **`differentiallyAlgebraic_of_lattice_periodic_meromorphicNF`**;
* **`ellipticHypertranscendenceFree`** — the named analytic input of the facet-codimension law,
  discharged;
* **`facetComplementRankOne_of_scalarSRRealization`** — hence the facet-codimension law itself, for
  meromorphic carriers, unconditionally.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

private theorem nonneg_meromorphicOrderAt_of_analyticAt {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) : 0 ≤ meromorphicOrderAt g z := by
  rw [hg.meromorphicOrderAt_eq]
  have hmono : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) :=
    ENat.monotone_map_iff.mpr (fun a b hab => by exact_mod_cast hab)
  have _h0 := hmono (show (0 : ℕ∞) ≤ analyticOrderAt g z by simp)
  simp

/-- **A lattice-periodic meromorphic function is differentially algebraic.** -/
theorem differentiallyAlgebraic_of_lattice_periodic_meromorphicNF (L : PeriodPair) {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    DifferentiallyAlgebraic f := by
  classical
  by_cases hd0 : ∀ z, deriv f z = 0
  · exact differentiallyAlgebraic_of_deriv_eq_zero hd0
  have hindep : LinearIndependent ℝ ![L.ω₁, L.ω₂] := L.indep
  have hmer : MeromorphicOn f Set.univ := hNF.meromorphicOn
  have hmerAt : ∀ z : ℂ, MeromorphicAt f z := fun z => hmer z (Set.mem_univ z)
  have hp₁ : Function.Periodic f L.ω₁ := hper _ L.ω₁_mem_lattice
  have hp₂ : Function.Periodic f L.ω₂ := hper _ L.ω₂_mem_lattice
  set S := (finite_poles_fundamentalParallelogram hmer L.ω₁ L.ω₂).toFinset with hSdef
  set m := max (orderBound f S) (orderBound (deriv f) S) with hmdef
  obtain ⟨z₀, hz₀ord⟩ := exists_nonneg_meromorphicOrderAt hmer
  have hz₀an : AnalyticAt ℂ f z₀ := analyticAt_of_nonneg_meromorphicOrderAt hNF hz₀ord
  obtain ⟨N, c, hN1, hcne, hc0⟩ := exists_ne_zero_jetValueMap_eq_zero f S m z₀
  set d := 2 * m * N with hddef
  set G : ℂ → ℂ :=
    fun z => ∑ q : Fin (N + 1) × Fin (N + 1), c q * diffMonomial f (q.1 : ℕ) (q.2 : ℕ) z with hGdef
  -- the bounds available at a pole representative
  have hbound : ∀ p ∈ S, (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p ∧
      (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (deriv f) p := by
    intro p hp
    exact ⟨neg_le_meromorphicOrderAt_of_le (le_max_left _ _) (neg_orderBound_le f hp),
      neg_le_meromorphicOrderAt_of_le (le_max_right _ _) (neg_orderBound_le (deriv f) hp)⟩
  -- meromorphy of the cleared monomials and of the cleared combination
  have hmerPow : ∀ (p : ℂ) (i j : ℕ),
      MeromorphicOn (fun z => (z - p) ^ d * diffMonomial f i j z) Set.univ := by
    intro p i j z _
    exact (by fun_prop : MeromorphicAt (fun z : ℂ => (z - p) ^ d) z).mul
      (meromorphicAt_diffMonomial (hmerAt z) i j)
  have hmerPowG : ∀ p : ℂ, MeromorphicOn (fun z => (z - p) ^ d * G z) Set.univ := by
    intro p z _
    exact (by fun_prop : MeromorphicAt (fun z : ℂ => (z - p) ^ d) z).mul
      (meromorphicAt_monomialCombination (hmerAt z) c)
  -- the jets of the combination vanish at every pole representative
  have hjet : ∀ p ∈ S, ∀ k, k < d → principalJet G p d k = 0 := by
    intro p hp k hk
    obtain ⟨hof, hod⟩ := hbound p hp
    have hsum := principalJet_finset_sum (p := p) (d := d) (k := k) Finset.univ
      (fun q : Fin (N + 1) × Fin (N + 1) => diffMonomial f (q.1 : ℕ) (q.2 : ℕ)) c
      (fun q _ => hmerPow p _ _)
      (fun q _ => nonneg_order_poleFactor_monomial (hmerAt p) hof hod
        (Nat.lt_succ_iff.mp q.1.isLt) (Nat.lt_succ_iff.mp q.2.isLt))
      (hmerPowG p)
      (nonneg_order_poleFactor_combination (hmerAt p) hof hod c)
    rw [hGdef, hsum]
    have hval := congrFun hc0 (Sum.inl (⟨p, hp⟩, ⟨k, hk⟩))
    simpa using hval
  -- hence the combination has no pole at any representative
  have hordS : ∀ p ∈ S, 0 ≤ meromorphicOrderAt G p := by
    intro p hp
    obtain ⟨hof, hod⟩ := hbound p hp
    exact nonneg_order_of_principalJet_eq_zero (meromorphicAt_monomialCombination (hmerAt p) c)
      (hmerPowG p) (nonneg_order_poleFactor_combination (hmerAt p) hof hod c) (hjet p hp)
  -- periodicity of the combination
  have hG₁ : Function.Periodic G L.ω₁ := periodic_monomialCombination hp₁ c
  have hG₂ : Function.Periodic G L.ω₂ := periodic_monomialCombination hp₂ c
  -- no pole anywhere
  have hordAll : ∀ z, 0 ≤ meromorphicOrderAt G z := by
    intro z
    rcases le_or_gt 0 (meromorphicOrderAt f z) with hz | hz
    · exact nonneg_meromorphicOrderAt_of_analyticAt
        (analyticAt_monomialCombination (analyticAt_of_nonneg_meromorphicOrderAt hNF hz) c)
    · obtain ⟨C, _, hcov⟩ := exists_bounded_intCombination hindep
      obtain ⟨a, b, hmem, _, _⟩ := hcov z
      have hfp : meromorphicOrderAt f (z - (a • L.ω₁ + b • L.ω₂)) = meromorphicOrderAt f z :=
        meromorphicOrderAt_sub_latticeCombination hp₁ hp₂ a b z
      have hGp : meromorphicOrderAt G (z - (a • L.ω₁ + b • L.ω₂)) = meromorphicOrderAt G z :=
        meromorphicOrderAt_sub_latticeCombination hG₁ hG₂ a b z
      have hpS : (z - (a • L.ω₁ + b • L.ω₂)) ∈ S := by
        rw [hSdef, Set.Finite.mem_toFinset]
        exact ⟨hmem, by rw [hfp]; exact hz⟩
      rw [← hGp]
      exact hordS _ hpS
  -- the combination vanishes on its regular locus
  have hGmer : MeromorphicOn G Set.univ := fun z _ => meromorphicAt_monomialCombination (hmerAt z) c
  have hGz₀ : G z₀ = 0 := by
    have hval := congrFun hc0 (Sum.inr ())
    simpa [hGdef] using hval
  have hGreg : ∀ z, AnalyticAt ℂ G z → G z = 0 := by
    intro z hz
    have hz₀G : AnalyticAt ℂ G z₀ := analyticAt_monomialCombination hz₀an c
    rw [eq_of_nonneg_order_of_lattice_periodic L hGmer hG₁ hG₂ hordAll hz hz₀G, hGz₀]
  -- the relation, valid everywhere
  refine differentiallyAlgebraic_of_monomial_relation c hcne (fun z => ?_)
  rcases le_or_gt 0 (meromorphicOrderAt f z) with hz | hz
  · have hfz : AnalyticAt ℂ f z := analyticAt_of_nonneg_meromorphicOrderAt hNF hz
    have := hGreg z (analyticAt_monomialCombination hfz c)
    rw [hGdef] at this
    simp only [diffMonomial] at this
    rw [this, zero_mul]
  · have hfz : f z = 0 := eq_zero_of_meromorphicOrderAt_neg (hNF (Set.mem_univ z)) hz
    rw [hfz, mul_zero]

/-- **The named analytic input of the facet-codimension law, discharged.** -/
theorem ellipticHypertranscendenceFree : EllipticHypertranscendenceFree :=
  fun L _f hNF hper hHT =>
    hHT (differentiallyAlgebraic_of_lattice_periodic_meromorphicNF L hNF hper)

/-- **The facet-codimension law for a one-variable meromorphic realization, unconditionally.**
Every facet omits at most one ambient vertex. -/
theorem facetComplementRankOne_of_scalarSRRealization {α : Type*} [DecidableEq α]
    {facets : Finset (Finset α)} (hanti : FacetAntichain (↑facets : Set (Finset α)))
    (R : ScalarSRRealization facets) {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V (↑facets : Set (Finset α)) :=
  facetComplementRankOne_of_ellipticFree ellipticHypertranscendenceFree hanti R hsub


/-! ### The principalization capstone for meromorphic carriers -/

open Finset MvPolynomial in
/-- **Structural classification from a one-variable meromorphic realization.**  Such a facet
antichain is the full simplex or a single-vertex deletion family. -/
theorem principalization_of_scalarSRRealization {α : Type*} [DecidableEq α]
    {facets : Finset (Finset α)} (hanti : FacetAntichain (↑facets : Set (Finset α)))
    (R : ScalarSRRealization facets) {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V)
    (hne : facets.Nonempty) :
    (↑facets : Set (Finset α)) = {V} ∨
      ∃ U : Finset α, U.Nonempty ∧ U ⊆ V ∧
        (↑facets : Set (Finset α)) = deletionFacets V U := by
  refine facetAntichain_eq_singleton_or_deletionFacets ?_ hanti
    (facetComplementRankOne_of_scalarSRRealization hanti R hsub)
  obtain ⟨F, hF⟩ := hne
  exact ⟨F, Finset.mem_coe.mpr hF⟩

open Finset MvPolynomial in
/-- **Principalization for meromorphic carriers.**  On a finite ambient vertex type, a facet
antichain that is not the full simplex and admits a one-variable meromorphic realization has
principal Stanley–Reisner ideal, generated by the squarefree monomial of its deleted block. -/
theorem stanleyReisnerIdeal_principal_of_scalarSRRealization {α : Type*} [DecidableEq α]
    [Fintype α] {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ScalarSRRealization facets)
    (hne : facets.Nonempty)
    (hnotsimplex : (↑facets : Set (Finset α)) ≠ {(Finset.univ : Finset α)}) :
    ∃ U : Finset α, U.Nonempty ∧
      stanleyReisnerIdeal ℂ facets
        = Ideal.span ({∏ u ∈ U, X u} : Set (MvPolynomial α ℂ)) := by
  rcases principalization_of_scalarSRRealization hanti R
    (V := (Finset.univ : Finset α)) (fun F _ => Finset.subset_univ F) hne with
    hsimp | ⟨U, hUne, _, hUeq⟩
  · exact absurd hsimp hnotsimplex
  · refine ⟨U, hUne, ?_⟩
    have hfin : facets = deletionFacetFinset U := by
      apply Finset.coe_injective
      rw [hUeq, coe_deletionFacetFinset]
    rw [hfin, stanleyReisnerIdeal_deletionFacetFinset_eq_span_product]

end GaloisForLFunctions.HTGeometry
