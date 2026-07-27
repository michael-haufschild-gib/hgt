import GaloisForLFunctions.HTGeometry.UpperEndStanleyReisnerRealization
import GaloisForLFunctions.HTGeometry.WedgeTwoThick

/-!
# Facet-sewn Herglotz Stanley--Reisner realization

This file closes the facet-sewn capstone.  A single bounded prime-log Herglotz source has a
collision-free, differentially independent complete facet--Laurent orbit.  For the explicit
nonpure two-thick wedge complex, its compatible structural face output vanishes exactly on
nonfaces, and every finite Laurent structural family has full nonlinear differential matroid equal
to the localized Stanley--Reisner matroid.  The prime-log pole carrier has infinite rational rank,
excluding every finite-period multiple-Gamma divisor geometry.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- The squarefree indicator exponent has exactly its prescribed support. -/
theorem indicatorExponent_support
    {α : Type*} [DecidableEq α] (J : Finset α) :
    (indicatorExponent J).support = J := by
  rw [indicatorExponent]
  exact GaloisForLFunctions.VeroneseIdeal.support_sum_single J

/-- A squarefree face monomial vanishes in the Stanley--Reisner quotient exactly for nonfaces. -/
theorem quotient_indicatorMonomial_eq_zero_iff_nonface
    {R α : Type*} [CommRing R] [Nontrivial R] [DecidableEq α]
    (facets : Finset (Finset α)) (J : Finset α) :
    Ideal.Quotient.mk (stanleyReisnerIdeal R facets)
        (MvPolynomial.monomial (indicatorExponent J) (1 : R)) = 0 ↔
      ¬ IsFaceOf (↑facets : Set (Finset α)) J := by
  rw [Ideal.Quotient.eq_zero_iff_mem,
    mem_stanleyReisnerIdeal_iff]
  simp [indicatorExponent_support]

/-- A singleton Stanley--Reisner class is linearly independent exactly when it is nonzero. -/
theorem linearIndependent_unit_stanleyReisner_iff
    {R α : Type*} [CommRing R] [IsDomain R] [DecidableEq α]
    (facets : Finset (Finset α))
    (P : MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    LinearIndependent R (fun _ : Unit => P) ↔ P ≠ 0 := by
  constructor
  · intro h hzero
    have hn := h.ne_zero Unit.unit
    exact hn hzero
  · intro hP
    let f := (stanleyReisnerFacetTranslationCoordinates (R := R) facets).toLinearMap
    have hcoord : stanleyReisnerFacetTranslationCoordinates facets P ≠ 0 := by
      intro hzero
      apply hP
      apply stanleyReisnerFacetTranslationCoordinates_injective (R := R) facets
      simpa using hzero
    have hli : LinearIndependent R
        (fun _ : Unit => stanleyReisnerFacetTranslationCoordinates facets P) :=
      linearIndependent_unique_iff.mpr hcoord
    exact hli.of_comp f

/-- The quotient class of the squarefree structural monomial attached to a vertex set. -/
def stanleyReisnerFaceClass
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) (J : Finset α) :
    MvPolynomial α R ⧸ stanleyReisnerIdeal R facets :=
  Ideal.Quotient.mk (stanleyReisnerIdeal R facets)
    (MvPolynomial.monomial (indicatorExponent J) (1 : R))

/-- The singleton structural family attached to one vertex set. -/
def stanleyReisnerFaceFamily
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Finset (Finset α)) (J : Finset α) :
    Unit → MvPolynomial α R ⧸ stanleyReisnerIdeal R facets :=
  fun _ => stanleyReisnerFaceClass facets J

/-- The finite upper-end source packet used by one structural face output. -/
def upperEndFaceStructuralSource
    {α : Type*} [Fintype α] [DecidableEq α]
    (u : PrimeLogBoundedGauge) (facets : Finset (Finset α)) (J : Finset α) :
    FiniteFinsuppRowIndex
        (stanleyReisnerLaurentRows
          (1 : translationSubmonoid (Polynomial ℂ) α) facets
          (stanleyReisnerFaceFamily facets J)) → upperEndMeroField :=
  fun q => boundedGaugeTranslatedPrimeLogUpperEnd
    (facetOrbitShift facets (rationalIndependentWeights α)) u q.1

/-- The concrete upper-end Herglotz structural output attached to a vertex set. -/
def upperEndFaceStructuralOutput
    {α : Type*} [Fintype α] [DecidableEq α]
    (u : PrimeLogBoundedGauge) (facets : Finset (Finset α))
    (J : Finset α) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact differentialOperatorRowApply
    (finiteFinsuppOperatorRows
      (stanleyReisnerLaurentRows
        (1 : translationSubmonoid (Polynomial ℂ) α) facets
        (stanleyReisnerFaceFamily facets J)))
    (upperEndFaceStructuralSource u facets J) Unit.unit

set_option maxHeartbeats 800000 in
/-- **Structural face output vanishes exactly on nonfaces.**  Let `source` be any family indexed by
the Stanley–Reisner Laurent rows of `J` whose applied rows are differentially independent exactly
when the face family is linearly independent.  Then the structural output — the single row sum at
`Unit.unit` — vanishes precisely when `J` is not a face of `facets`.  Forward: a face gives a
nonzero Stanley–Reisner class, hence a linearly independent family, hence a differentially
independent one, whose members are nonzero. Backward: a nonface makes every Laurent row vanish, so
the sum is zero termwise. -/
theorem structuralFaceOutput_eq_zero_iff_nonface
    {α : Type*} [Fintype α] [DecidableEq α]
    (facets : Finset (Finset α)) (J : Finset α)
    (source : FiniteFinsuppRowIndex
        (stanleyReisnerLaurentRows (1 : translationSubmonoid (Polynomial ℂ) α) facets
          (stanleyReisnerFaceFamily facets J)) → upperEndMeroField)
    (hmat :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent ℂ
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows
              (stanleyReisnerLaurentRows (1 : translationSubmonoid (Polynomial ℂ) α) facets
                (stanleyReisnerFaceFamily facets J))) source) ↔
        LinearIndependent (Polynomial ℂ)
          (stanleyReisnerFaceFamily (R := Polynomial ℂ) facets J)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialOperatorRowApply
        (finiteFinsuppOperatorRows
          (stanleyReisnerLaurentRows (1 : translationSubmonoid (Polynomial ℂ) α) facets
            (stanleyReisnerFaceFamily facets J))) source Unit.unit = 0 ↔
      ¬ IsFaceOf (↑facets : Set (Finset α)) J := by

  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let N := stanleyReisnerFaceFamily (R := Polynomial ℂ) facets J
  let d : translationSubmonoid (Polynomial ℂ) α := 1
  constructor
  · intro hout
    by_contra hface
    have hclass : stanleyReisnerFaceClass (R := Polynomial ℂ) facets J ≠ 0 := by
      intro hzero
      exact (quotient_indicatorMonomial_eq_zero_iff_nonface
        (R := Polynomial ℂ) facets J).mp hzero hface
    have hN : LinearIndependent (Polynomial ℂ) N := by
      exact (linearIndependent_unit_stanleyReisner_iff facets _).mpr hclass
    have hDI : DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) :=
      hmat.mpr hN
    have hn := hDI.algebraicIndependent.linearIndependent.ne_zero Unit.unit
    apply hn
    simpa [d, N] using hout
  · intro hnonface
    have hclass : stanleyReisnerFaceClass (R := Polynomial ℂ) facets J = 0 :=
      (quotient_indicatorMonomial_eq_zero_iff_nonface
        (R := Polynomial ℂ) facets J).mpr hnonface
    let Q := stanleyReisnerLaurentRows
      (1 : translationSubmonoid (Polynomial ℂ) α) facets
      (stanleyReisnerFaceFamily facets J)
    have hQzero : Q = 0 := by
      apply _root_.funext
      intro i
      apply _root_.funext
      intro F
      apply Finsupp.ext
      intro g
      simp [Q, stanleyReisnerLaurentRows, stanleyReisnerFaceFamily, hclass]
    change differentialOperatorRowApply (finiteFinsuppOperatorRows Q)
      source Unit.unit = 0
    unfold differentialOperatorRowApply
    apply Finset.sum_eq_zero
    intro q hq
    have hc : finiteFinsuppOperatorRows Q Unit.unit q = 0 := by
      change Q Unit.unit q.1.1 q.1.2 = 0
      have hc0 := congrArg
        (fun rows : Unit → (F : facets) → (α → ℤ) →₀ Polynomial ℂ =>
          rows Unit.unit q.1.1 q.1.2) hQzero
      simpa using hc0
    rw [hc]
    simp [differentialOperatorApply]

set_option maxHeartbeats 800000 in
/-- **Exact analytic compatible-relation law.**  For a source with free complete facet orbit, the
structural face output is zero exactly when the vertex set is a nonface. -/
theorem upperEndFaceStructuralOutput_eq_zero_iff_nonface
    {α : Type*} [Fintype α] [DecidableEq α]
    (u : PrimeLogBoundedGauge) (facets : Finset (Finset α))
    (hu :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent ℂ
        (boundedGaugeTranslatedPrimeLogUpperEnd
          (facetOrbitShift facets (rationalIndependentWeights α)) u))
    (J : Finset α) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    upperEndFaceStructuralOutput u facets J = 0 ↔
      ¬ IsFaceOf (↑facets : Set (Finset α)) J := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact structuralFaceOutput_eq_zero_iff_nonface facets J
    (upperEndFaceStructuralSource u facets J)
    (upperEnd_stanleyReisnerLaurentDifferentialMatroid u facets hu 1
      (stanleyReisnerFaceFamily facets J))

/-- Complete combinatorial and quotient-relation certificate for the nonpure two-thick wedge. -/
def WedgeFacetSewnGeometry : Prop :=
  FacetAntichain wedgeFacetSet ∧
    (¬ ∃ d, PureOfCard wedgeFacetSet d) ∧
    TwoThick wedgeFacetSet ∧
    (∀ J : Finset WedgeVertex,
      MinimalNonface wedgeFacetSet J ↔ J ∈ wedgeMinimalNonfaces) ∧
    ∀ J : Finset WedgeVertex,
      Ideal.Quotient.mk
          (stanleyReisnerIdeal (Polynomial ℂ) wedgeFacets)
          (MvPolynomial.monomial (indicatorExponent J) (1 : Polynomial ℂ)) = 0 ↔
        ¬ IsFaceOf wedgeFacetSet J

/-- The explicit six-vertex wedge satisfies the complete facet-sewn geometry certificate. -/
theorem wedgeFacetSewnGeometry : WedgeFacetSewnGeometry := by
  refine ⟨wedge_facetAntichain, wedge_not_pure, wedge_twoThick,
    wedge_minimalNonface_iff, ?_⟩
  intro J
  exact quotient_indicatorMonomial_eq_zero_iff_nonface wedgeFacets J

/-- **Facet-sewn Herglotz--Stanley--Reisner realization theorem.**

There exists one bounded prime-log upper-end Herglotz source such that:

* its exact simple-pole carrier has infinite rational rank;
* its complete collision-free facet--Laurent orbit is differentially independent over `C(z)`;
* the explicit relation complex is nonpure and two-thick, with the certified minimal
  nonfaces of degrees two, three, and four;
* its analytic structural face output vanishes exactly on nonfaces; and
* simultaneously for every finite Laurent structural family, the full nonlinear differential
  matroid is exactly the `C[D]`-linear Stanley--Reisner matroid of its common-denominator numerator
  classes.

The infinite-rank exact pole carrier is the positive obstruction to membership in any finite-period
multiple-Gamma divisor hierarchy.
-/
theorem exists_wedgeFacetSewnUpperEndSystem :
    ∃ u : PrimeLogBoundedGauge,
      WedgeFacetSewnGeometry ∧
      (¬ ∃ s : Set ℝ, s.Finite ∧
        Set.range primeLogSupport ⊆ Submodule.span ℚ s) ∧
      (∀ p : Nat.Primes,
        HasSimplePoleAt (primeLogHerglotz (fun q => u q))
          (primeLogSupport p : ℂ) (-(primeDyadicWeight (fun q => u q) p : ℂ))) ∧
      (letI := isDomain_upperEndAnalyticSubring
       letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
       letI := upperEndMeroFieldDifferential
       DifferentialIndependent (RatFunc ℂ)
         (boundedGaugeTranslatedPrimeLogUpperEnd
           (facetOrbitShift wedgeFacets
             (rationalIndependentWeights WedgeVertex)) u)) ∧
      (∀ J : Finset WedgeVertex,
        letI := isDomain_upperEndAnalyticSubring
        letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
        letI := upperEndMeroFieldDifferential
        upperEndFaceStructuralOutput u wedgeFacets J = 0 ↔
          ¬ IsFaceOf wedgeFacetSet J) ∧
      ∀ (m : ℕ)
        (d : translationSubmonoid (Polynomial ℂ) WedgeVertex)
        (N : Fin m → MvPolynomial WedgeVertex (Polynomial ℂ) ⧸
          stanleyReisnerIdeal (Polynomial ℂ) wedgeFacets),
        letI := isDomain_upperEndAnalyticSubring
        letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
        letI := upperEndMeroFieldDifferential
        let source : FiniteFinsuppRowIndex
            (stanleyReisnerLaurentRows d wedgeFacets N) → upperEndMeroField :=
          fun q => boundedGaugeTranslatedPrimeLogUpperEnd
            (facetOrbitShift wedgeFacets
              (rationalIndependentWeights WedgeVertex)) u q.1
        DifferentialIndependent ℂ
            (differentialOperatorRowApply
              (finiteFinsuppOperatorRows
                (stanleyReisnerLaurentRows d wedgeFacets N)) source) ↔
          LinearIndependent (Polynomial ℂ) N := by
  obtain ⟨u, huRat⟩ :=
    exists_upperEndFacetOrbit_differentialIndependent_ratfunc wedgeFacets
  have hu :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent ℂ
        (boundedGaugeTranslatedPrimeLogUpperEnd
          (facetOrbitShift wedgeFacets
            (rationalIndependentWeights WedgeVertex)) u) := by
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    exact differentialIndependent_upperEnd_restrictComplex _ huRat
  refine ⟨u, wedgeFacetSewnGeometry,
    primeLogSupport_not_contained_finite_span, ?_, huRat, ?_, ?_⟩
  · intro p
    exact hasSimplePoleAt_primeLogHerglotz (fun q => u q) ‖u‖
      (fun q => (le_abs_self (u q)).trans (u.norm_coe_le_norm q)) p
  · intro J
    exact upperEndFaceStructuralOutput_eq_zero_iff_nonface u wedgeFacets hu J
  · intro m d N
    exact upperEnd_stanleyReisnerLaurentDifferentialMatroid
      u wedgeFacets hu d N

end

end GaloisForLFunctions.HTGeometry
