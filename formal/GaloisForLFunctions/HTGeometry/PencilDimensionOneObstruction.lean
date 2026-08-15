import GaloisForLFunctions.HTGeometry.PencilHTDimension
import GaloisForLFunctions.HTGeometry.ScalarSRRealizationBridge

/-!
# One variable cannot realize a facet that omits three vertices

A facet monomial is annihilated by exactly the vertex coordinates its facet omits, so in one variable
its carrier acquires one period per omitted vertex.  Three `ℚ`-independent periods make the period
group non-discrete, which forces a meromorphic function to be constant; but the facet monomial is a
nonzero class, and constancy of its carrier would make the class annihilated by a coordinate of its
own facet.  Hence no complex with a facet omitting three vertices is realized in one variable.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The facet monomial. -/
def facetMonomial (A : Finset α) : MvPolynomial α ℂ := ∏ u ∈ A, MvPolynomial.X u

omit [Fintype α] in
theorem facetRestrict_facetMonomial_self (A : Finset α) :
    facetRestrict A (facetMonomial A) = facetMonomial A := by
  rw [facetMonomial, map_prod]
  exact Finset.prod_congr rfl fun u hu => facetRestrict_X_mem hu

omit [Fintype α] [DecidableEq α] in
theorem facetMonomial_ne_zero (A : Finset α) : facetMonomial A ≠ 0 := by
  rw [facetMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun u _ => MvPolynomial.X_ne_zero u

omit [Fintype α] in
/-- **A vertex outside a facet annihilates that facet's monomial.** -/
theorem X_mul_facetMonomial_mem (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {A : Finset α} (hA : A ∈ facets)
    {v : α} (hv : v ∉ A) :
    MvPolynomial.X v * facetMonomial A ∈ stanleyReisnerIdeal ℂ facets := by
  rw [mem_stanleyReisnerIdeal_iff_facetRestrict]
  intro B hB
  rw [map_mul, facetMonomial, map_prod]
  by_cases hvB : v ∈ B
  · have hex : ∃ u ∈ A, u ∉ B := by
      by_contra hcon
      push Not at hcon
      have hAB : A = B := hanti (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hB) hcon
      exact hv (hAB ▸ hvB)
    obtain ⟨u, huA, huB⟩ := hex
    rw [Finset.prod_eq_zero huA (facetRestrict_X_notMem huB), mul_zero]
  · rw [facetRestrict_X_notMem hvB, zero_mul]

omit [Fintype α] in
/-- **A vertex inside a facet does not annihilate that facet's monomial.** -/
theorem X_mul_facetMonomial_notMem (facets : Finset (Finset α)) {A : Finset α}
    (hA : A ∈ facets) {u : α} (hu : u ∈ A) :
    MvPolynomial.X u * facetMonomial A ∉ stanleyReisnerIdeal ℂ facets := by
  rw [mem_stanleyReisnerIdeal_iff_facetRestrict]
  push Not
  refine ⟨A, hA, ?_⟩
  rw [map_mul, facetRestrict_X_mem hu, facetRestrict_facetMonomial_self]
  exact mul_ne_zero (MvPolynomial.X_ne_zero u) (facetMonomial_ne_zero A)

/-- **Zero variables realize nothing on a nonempty vertex set.** -/
theorem not_htRealizableDim_zero [Nonempty α] (facets : Finset (Finset α)) :
    ¬ HTRealizableDim facets 0 := by
  rintro ⟨ω, w, Y, hY, hindep, -, -, -⟩
  exact hindep.ne_zero (Classical.arbitrary α) (Subsingleton.elim _ _)

/-! ### One variable is impossible past three omitted vertices -/

set_option maxHeartbeats 4000000 in
/-- **No complex with a facet omitting three vertices is realized in one variable.** -/
theorem not_htRealizableDim_one_of_three_omitted (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {V A : Finset α}
    (hA : A ∈ facets) (hAne : A.Nonempty) (hcard : 3 ≤ (V \ A).card) :
    ¬ HTRealizableDim facets 1 := by
  classical
  rintro ⟨ω, w, Y, hY, hindep, hper, hann, -⟩
  set F : (Fin 1 → ℂ) → ℂ := fun y => ∑ B : facets, Y B y with hFdef
  have hFa : AnalyticOnNhd ℂ F Set.univ := Finset.analyticOnNhd_fun_sum _ fun B _ => hY B
  set P := facetMonomial A with hP
  set carrier : ℂ → ℂ := fun t => seedCarrierPoly ω F P (fun _ => t) with hcarrier
  have hproj : Function.Injective (fun x : Fin 1 → ℂ => x 0) := by
    intro x y h
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  have hindep' : LinearIndependent ℚ (fun v => ω v 0) :=
    hindep.map' (LinearMap.proj (R := ℚ) (0 : Fin 1)) (LinearMap.ker_eq_bot.mpr hproj)
  have hdiff : Differentiable ℂ carrier := by
    have h1 : Differentiable ℂ (seedCarrierPoly ω F P) := fun z =>
      ((analyticOnNhd_seedCarrierPoly ω hFa P) z (Set.mem_univ z)).differentiableAt
    exact h1.comp (differentiable_pi.mpr fun _ => differentiable_id)
  have hmer : MeromorphicNFOn carrier Set.univ := fun z _ =>
    ((hdiff.analyticAt z)).meromorphicNFAt
  have hconstpt : ∀ (u : α) (t : ℂ),
      seedCarrierPoly ω F (MvPolynomial.X u * P) (fun _ => t)
        = carrier (t + ω u 0) - carrier t := by
    intro u t
    have hx := congrFun (seedCarrierPoly_X_mul ω F u P) (fun _ => t)
    rw [hx]
    have hsum : ((fun _ => t) + ω u : Fin 1 → ℂ) = fun _ => t + ω u 0 := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [hsum]
  have hperiod : ∀ v ∈ V \ A, Function.Periodic carrier (ω v 0) := by
    intro v hv t
    have hvA : v ∉ A := (Finset.mem_sdiff.mp hv).2
    have hzero : seedCarrierPoly ω F (MvPolynomial.X v * P) = 0 :=
      (hann _).mpr (X_mul_facetMonomial_mem facets hanti hA hvA)
    have := hconstpt v t
    rw [hzero] at this
    have h0 : (0 : ℂ) = carrier (t + ω v 0) - carrier t := this
    exact (sub_eq_zero.mp h0.symm)
  have hnonconst : ¬ (∀ x y, carrier x = carrier y) := by
    intro hconst
    obtain ⟨u, huA⟩ := hAne
    refine X_mul_facetMonomial_notMem facets hA huA ((hann _).mp ?_)
    funext z
    have hz : z = fun _ => z 0 := by
      funext i
      rw [Subsingleton.elim i 0]
    rw [hz, hconstpt u (z 0), hconst (z 0 + ω u 0) (z 0), sub_self]
    rfl
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  set g := Finset.equivFinOfCardEq htcard with hg
  set e : Fin 3 → α := fun i => (g.symm i : α) with he
  have hinj : Function.Injective e := by
    intro i j hij
    have hsub : (g.symm i : { x // x ∈ t }) = g.symm j := Subtype.ext hij
    simpa using congrArg g hsub
  have hmem : ∀ i, e i ∈ V \ A := fun i => hts (g.symm i).2
  have hindepe : LinearIndependent ℚ ((fun v => ω v 0) ∘ e) := hindep'.comp e hinj
  have hpere : ∀ i, Function.Periodic carrier (((fun v => ω v 0) ∘ e) i) :=
    fun i => hperiod (e i) (hmem i)
  have hspan := periodic_of_mem_span_range (f := carrier) ((fun v => ω v 0) ∘ e) hpere
  exact hnonconst (meromorphicNF_constant_of_rankThree_periods carrier hmer
    ((fun v => ω v 0) ∘ e) hindepe hspan)

end

end GaloisForLFunctions.HTGeometry
