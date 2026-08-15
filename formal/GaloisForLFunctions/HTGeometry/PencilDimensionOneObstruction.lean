import GaloisForLFunctions.HTGeometry.PencilHTDimension
import GaloisForLFunctions.HTGeometry.ScalarSRRealizationBridge
import GaloisForLFunctions.HTGeometry.EntireFacetRealizationCodimension
import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods
import GaloisForLFunctions.HTGeometry.EllipticLiouvilleFacetCodimension

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
/-- **The facet carrier of a one-variable realization.**  Each facet monomial has an entire scalar
carrier, periodic under every step its facet omits, and nonconstant. -/
theorem exists_facetCarrier_of_htRealizableDim_one (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {A : Finset α}
    (hA : A ∈ facets) (hAne : A.Nonempty) (h : HTRealizableDim facets 1) :
    ∃ (ω' : α → ℂ) (carrier : ℂ → ℂ), LinearIndependent ℚ ω' ∧ Differentiable ℂ carrier ∧
      (∀ v ∉ A, Function.Periodic carrier (ω' v)) ∧ ¬ (∀ x y, carrier x = carrier y) := by
  classical
  obtain ⟨ω, w, Y, hY, hindep, hper, hann, -⟩ := h
  set F : (Fin 1 → ℂ) → ℂ := fun y => ∑ B : facets, Y B y with hFdef
  have hFa : AnalyticOnNhd ℂ F Set.univ := Finset.analyticOnNhd_fun_sum _ fun B _ => hY B
  set P := facetMonomial A with hP
  set carrier : ℂ → ℂ := fun t => seedCarrierPoly ω F P (fun _ => t) with hcarrier
  have hproj : Function.Injective (fun x : Fin 1 → ℂ => x 0) := by
    intro x y hxy
    funext i
    rw [Subsingleton.elim i 0]
    exact hxy
  have hindep' : LinearIndependent ℚ (fun v => ω v 0) :=
    hindep.map' (LinearMap.proj (R := ℚ) (0 : Fin 1)) (LinearMap.ker_eq_bot.mpr hproj)
  have hdiff : Differentiable ℂ carrier := by
    have h1 : Differentiable ℂ (seedCarrierPoly ω F P) := fun z =>
      ((analyticOnNhd_seedCarrierPoly ω hFa P) z (Set.mem_univ z)).differentiableAt
    exact h1.comp (differentiable_pi.mpr fun _ => differentiable_id)
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
  have hperiod : ∀ v ∉ A, Function.Periodic carrier (ω v 0) := by
    intro v hvA t
    have hzero : seedCarrierPoly ω F (MvPolynomial.X v * P) = 0 :=
      (hann _).mpr (X_mul_facetMonomial_mem facets hanti hA hvA)
    have hval := hconstpt v t
    rw [hzero] at hval
    have h0 : (0 : ℂ) = carrier (t + ω v 0) - carrier t := hval
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
  exact ⟨fun v => ω v 0, carrier, hindep', hdiff, hperiod, hnonconst⟩

/-- **No complex with a facet omitting two vertices is realized in one variable.**  Two
`ℚ`-independent periods make an entire carrier constant: by non-discreteness of the period group if
the steps are `ℝ`-dependent, and by Liouville's theorem if they are not. -/
theorem not_htRealizableDim_one_of_two_omitted (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {V A : Finset α}
    (hA : A ∈ facets) (hAne : A.Nonempty) (hcard : 2 ≤ (V \ A).card) :
    ¬ HTRealizableDim facets 1 := by
  classical
  intro h
  obtain ⟨ω', carrier, hindep, hdiff, hperiod, hnonconst⟩ :=
    exists_facetCarrier_of_htRealizableDim_one facets hanti hA hAne h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (V \ A).card)
  have haA : a ∉ A := (Finset.mem_sdiff.mp ha).2
  have hbA : b ∉ A := (Finset.mem_sdiff.mp hb).2
  have hspan : ∀ p ∈ Submodule.span ℤ (Set.range ![ω' a, ω' b]),
      Function.Periodic carrier p := by
    refine periodic_of_mem_span_range ![ω' a, ω' b] (fun i => ?_)
    fin_cases i
    · exact hperiod a haA
    · exact hperiod b hbA
  by_cases hdep : LinearIndependent ℝ ![ω' a, ω' b]
  · set L : PeriodPair := ⟨ω' a, ω' b, hdep⟩ with hL
    have hlat : ∀ p ∈ L.lattice, Function.Periodic carrier p := by
      intro p hp
      refine hspan p ?_
      rw [range_cons_two]
      exact hp
    exact hnonconst (const_of_lattice_periodic_differentiable L hdiff hlat)
  · have hinj : Function.Injective ![a, b] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hQ : LinearIndependent ℚ ![ω' a, ω' b] := by
      have hcomp := hindep.comp ![a, b] hinj
      rwa [comp_cons_two] at hcomp
    have hmer : MeromorphicNFOn carrier Set.univ := fun z _ =>
      ((hdiff.analyticAt z)).meromorphicNFAt
    exact hnonconst (meromorphicNF_constant_of_rankTwo_realDependent_periods carrier hmer
      ![ω' a, ω' b] hQ hdep hspan)

/-- **No complex with a facet omitting three vertices is realized in one variable.** -/
theorem not_htRealizableDim_one_of_three_omitted (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {V A : Finset α}
    (hA : A ∈ facets) (hAne : A.Nonempty) (hcard : 3 ≤ (V \ A).card) :
    ¬ HTRealizableDim facets 1 :=
  not_htRealizableDim_one_of_two_omitted facets hanti hA hAne (V := V) (by omega)

/-- **The facet-codimension law in one variable.**  Every facet of a one-variable realization omits
at most one ambient vertex. -/
theorem facetComplementRankOne_of_htRealizableDim_one (facets : Finset (Finset α))
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (V : Finset α)
    (hsub : ∀ F ∈ facets, F ⊆ V) (hnef : ∀ F ∈ facets, F.Nonempty)
    (h : HTRealizableDim facets 1) :
    FacetComplementRankOne V (↑facets : Set (Finset α)) := by
  intro F hF
  refine ⟨hsub F (Finset.mem_coe.mp hF), ?_⟩
  by_contra hcon
  exact not_htRealizableDim_one_of_two_omitted facets hanti (Finset.mem_coe.mp hF)
    (hnef F (Finset.mem_coe.mp hF)) (V := V) (by omega) h

end

end GaloisForLFunctions.HTGeometry
