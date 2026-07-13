import GaloisForLFunctions.HTGeometry.UniversalFiniteConstraintCarrier
import GaloisForLFunctions.HTGeometry.SummablePrimeCauchyCompactOpen

/-!
# The canonical residual phase of universal facet sources

The universal constraint geometry does not require a distinguished Baire-generic gauge.  Its
intrinsic source object is the full dense residual phase of gauges whose universal facet-orbit
palette is polynomial-differentially free.  Every point of this phase has a genuinely
differentially independent translation palette, carries every finite localized Stanley--Reisner
differential matroid, and retains the positive Herglotz orientation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- Genuine differential independence of the complete universal facet-orbit palette. -/
def UniversalFacetSourceProperty (u : PrimeLogBoundedGauge) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  DifferentialIndependent (RatFunc ℂ)
    (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u)

/-- The intrinsic phase of all bounded gauges whose universal facet-orbit palette is genuinely
differentially independent. -/
def universalFacetSourcePhase : Set PrimeLogBoundedGauge :=
  {u | UniversalFacetSourceProperty u}

/-- The universal source phase is dense residual; it is the canonical point-free replacement for
choosing one Baire-generic gauge. -/
theorem universalFacetSourcePhase_dense_residual :
    Dense universalFacetSourcePhase ∧
      universalFacetSourcePhase ∈ residual PrimeLogBoundedGauge := by
  let F : Set PrimeLogBoundedGauge :=
    {u | CountableShiftPolynomialDifferentialFree universalFacetOrbitShift u}
  have hF := countableShiftPolynomialDifferentialFree_dense_residual
    universalFacetOrbitShift universalFacetOrbitShift_injective
  have hsub : F ⊆ universalFacetSourcePhase := by
    intro u hu
    exact upperEndShift_differentialIndependent universalFacetOrbitShift u hu
  exact ⟨hF.1.mono hsub, Filter.mem_of_superset hF.2 hsub⟩

/-- A source is a gauge together with membership in the intrinsic universal phase. -/
abbrev UniversalFacetSource := universalFacetSourcePhase

/-- Every point of the canonical source phase has a genuinely differentially independent complete
universal translation palette. -/
theorem UniversalFacetSource.differentialIndependent (u : UniversalFacetSource) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1) := by
  exact u.property

/-- Every point of the source phase carries every finite localized Stanley--Reisner differential
matroid.  Thus constraint universality belongs to the whole phase, not to a selected gauge. -/
theorem UniversalFacetSource.stanleyReisnerLaurentDifferentialMatroid
    (u : UniversalFacetSource)
    {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let e := finiteVertexNatEmbedding α
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        u.1 (finiteFacetOrbitUniversalIndex e facets q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
      LinearIndependent (Polynomial ℂ) N := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let e := finiteVertexNatEmbedding α
  let fullSource := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    fullSource (finiteFacetOrbitUniversalIndex e facets q.1)
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := u.differentialIndependent.comp
      (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) =>
        finiteFacetOrbitUniversalIndex e facets q.1)
      ((finiteFacetOrbitUniversalIndex_injective e facets).comp Subtype.val_injective)
    simpa [source, fullSource, Function.comp_def] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
    LinearIndependent (Polynomial ℂ) N
  exact differentialIndependent_stanleyReisnerLaurentRows_iff
    (C := ℂ) (K := upperEndMeroField)
    upperEndMero_deriv_complexConstant d facets N source hsource

/-- Every point of the source phase retains positive Herglotz orientation. -/
theorem UniversalFacetSource.primeLogHerglotz_im_nonneg
    (u : UniversalFacetSource) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (primeLogHerglotz (fun q => u.1 q) z).im :=
  primeLogHerglotz_im_nonneg (fun q => u.1 q) ‖u.1‖
    (fun q => (le_abs_self (u.1 q)).trans
      (u.1.norm_coe_le_norm q)) z hz

/-- The signed prime residues determined by a phase source and an arbitrary orientation. -/
def UniversalFacetSource.orientationWeight
    (u : UniversalFacetSource) (ε : Nat.Primes → Bool) (p : Nat.Primes) : ℝ :=
  if ε p = true then -primeDyadicWeight (fun q => u.1 q) p
  else primeDyadicWeight (fun q => u.1 q) p

theorem UniversalFacetSource.norm_orientationWeight
    (u : UniversalFacetSource) (ε : Nat.Primes → Bool) (p : Nat.Primes) :
    ‖(u.orientationWeight ε p : ℂ)‖ =
      ‖(primeDyadicWeight (fun q => u.1 q) p : ℂ)‖ := by
  simp only [UniversalFacetSource.orientationWeight]
  split_ifs <;> simp

/-- Every source-orientation residue sequence in the canonical phase is absolutely summable. -/
theorem UniversalFacetSource.summable_norm_orientationWeight
    (u : UniversalFacetSource) (ε : Nat.Primes → Bool) :
    Summable fun p => ‖(u.orientationWeight ε p : ℂ)‖ := by
  have h := summable_norm_primeDyadicWeight (fun q => u.1 q)
    ‖u.1‖
    (fun q => (le_abs_self (u.1 q)).trans
      (u.1.norm_coe_le_norm q))
  exact h.congr fun p => (u.norm_orientationWeight ε p).symm

/-- The completed rational Cauchy ring attached to one phase source and one orientation. -/
def UniversalFacetSource.completedOrientationRing
    (u : UniversalFacetSource) (ε : Nat.Primes → Bool) :
    Subring C(PrimeOrientationDomain, ℂ) :=
  summablePrimeCauchyCompletedRing (u.orientationWeight ε)
    (u.summable_norm_orientationWeight ε)

/-- **Source--orientation completion invariance.** The compact-open completed rational Cauchy
ring is independent simultaneously of the Baire-generic source and of every finite or infinite
orientation sequence. -/
theorem UniversalFacetSource.completedOrientationRing_eq
    (u v : UniversalFacetSource) (ε δ : Nat.Primes → Bool) :
    u.completedOrientationRing ε = v.completedOrientationRing δ :=
  summablePrimeCauchyCompletedRing_eq
    (u.orientationWeight ε) (v.orientationWeight δ)
    (u.summable_norm_orientationWeight ε)
    (v.summable_norm_orientationWeight δ)

end

end GaloisForLFunctions.HTGeometry
