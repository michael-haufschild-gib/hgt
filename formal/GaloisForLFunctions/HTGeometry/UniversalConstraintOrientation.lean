import GaloisForLFunctions.HTGeometry.UniversalFiniteConstraintCarrier
import GaloisForLFunctions.HTGeometry.UpperEndRationalGauge

/-!
# Universal constraint--orientation product geometry

Finite rational residue surgery changes only the rational gauge representative of the universal
prime-log source.  The whole universal facet palette therefore remains differentially independent,
and every finite Stanley--Reisner differential matroid persists in every finite residue-sign
chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- A finite real change of the prime-log residue sequence. -/
abbrev PrimeResidueSurgery := Nat.Primes →₀ ℝ

/-- The rational correction obtained by translating a finite prime-log residue surgery by `h`. -/
def primeResidueSurgeryRatFunc (a : PrimeResidueSurgery) (h : ℂ) : RatFunc ℂ :=
  a.sum fun p delta =>
    RatFunc.C (delta : ℂ) *
      (RatFunc.C (primeLogSupport p : ℂ) - (RatFunc.X + RatFunc.C h))⁻¹

/-- The universal translated source after one finite residue surgery of the underlying generator. -/
def universalFacetOrbitSurgerySource
    (a : PrimeResidueSurgery) (q : UniversalFacetOrbitIndex) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  exact boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
      universalFacetOrbitGauge q +
    algebraMap (RatFunc ℂ) upperEndMeroField
      (primeResidueSurgeryRatFunc a (universalFacetOrbitShift q))

/-- Every finite residue surgery preserves differential independence of the complete universal
facet palette. -/
theorem universalFacetOrbitSurgerySource_differentialIndependent
    (a : PrimeResidueSurgery) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (universalFacetOrbitSurgerySource a) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  have h := DifferentialIndependent.addUpperEndRatfunc
    universalFacetOrbitGauge_differentialIndependent
    (fun q => primeResidueSurgeryRatFunc a (universalFacetOrbitShift q))
  simpa [universalFacetOrbitSurgerySource] using h

/-- Flip exactly the residue signs indexed by a finite prime set. -/
def universalSignFlipSurgery (J : Finset Nat.Primes) : PrimeResidueSurgery :=
  Finsupp.onFinset J
    (fun p => if p ∈ J then
      -2 * primeDyadicWeight (fun q => universalFacetOrbitGauge q) p else 0)
    (by
      intro p hp
      by_contra hmem
      simp [hmem] at hp)

/-- The signed residue mass after surgery. -/
def universalSurgeryResidueMass (a : PrimeResidueSurgery) (p : Nat.Primes) : ℝ :=
  primeDyadicWeight (fun q => universalFacetOrbitGauge q) p + a p

@[simp]
theorem universalSignFlipSurgery_apply (J : Finset Nat.Primes) (p : Nat.Primes) :
    universalSignFlipSurgery J p = if p ∈ J then
      -2 * primeDyadicWeight (fun q => universalFacetOrbitGauge q) p else 0 := by
  classical
  exact Finsupp.onFinset_apply

@[simp]
theorem universalSurgeryResidueMass_signFlip
    (J : Finset Nat.Primes) (p : Nat.Primes) :
    universalSurgeryResidueMass (universalSignFlipSurgery J) p =
      if p ∈ J then -primeDyadicWeight (fun q => universalFacetOrbitGauge q) p
      else primeDyadicWeight (fun q => universalFacetOrbitGauge q) p := by
  classical
  simp only [universalSurgeryResidueMass, universalSignFlipSurgery_apply]
  split <;> ring

/-- The negative residue set of the sign-flipped representative is exactly the chosen chamber
vertex. -/
theorem universalSurgeryResidueMass_signFlip_neg_iff
    (J : Finset Nat.Primes) (p : Nat.Primes) :
    universalSurgeryResidueMass (universalSignFlipSurgery J) p < 0 ↔ p ∈ J := by
  classical
  rw [universalSurgeryResidueMass_signFlip]
  split_ifs with hp
  · simp [hp, primeDyadicWeight_pos]
  · exact iff_of_false (not_lt_of_ge (primeDyadicWeight_pos _ _).le) hp

/-- **Constraint--orientation product law.**  For every finite residue surgery, every finite
simplicial facet family, and every finite localized structural family, the surgically modified
universal source realizes exactly the same Stanley--Reisner nonlinear differential matroid. -/
theorem universalFacetOrbitSurgery_stanleyReisnerLaurentDifferentialMatroid
    (a : PrimeResidueSurgery)
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
      universalFacetOrbitSurgerySource a
        (finiteFacetOrbitUniversalIndex e facets q.1)
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
  let fullSource := universalFacetOrbitSurgerySource a
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    fullSource (finiteFacetOrbitUniversalIndex e facets q.1)
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := (universalFacetOrbitSurgerySource_differentialIndependent a).comp
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

end

end GaloisForLFunctions.HTGeometry
