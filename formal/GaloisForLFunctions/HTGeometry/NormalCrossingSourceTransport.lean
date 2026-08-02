import GaloisForLFunctions.HTGeometry.MultiplicativeRealizationComparison
import GaloisForLFunctions.HTGeometry.PhysicalTangencyNaturalSource

/-!
# The physical package is a function of the annihilator alone

A source realization of order `r` is one whose differential-algebraic translation annihilator is
the squarefree degree-`r` ideal.  Everything the physical comparison produces — source height,
arc-contact order, powered period-incidence level, convergent fat-point length, polarizing
half-density — is computed from that ideal and from nothing else about the realization.

Two consequences pull in opposite directions.  Positively, any two realizations with the same
normal-crossing annihilator have literally the same package, so the comparison transports without
further analytic input.  Negatively, the package is blind: it does not see the period frame at all,
only its order, so it cannot separate two families that share the ideal.

What is retained is the bounded symbol spectrum, which reconstructs the embedded period module
exactly.  The conservative invariant is therefore the pair, not the package alone.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators ENNReal

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-! ## Normal-crossing source realizations -/

/-- A source realization of order `r`: its differential-algebraic translation annihilator is
exactly the squarefree degree-`r` ideal. -/
def IsNormalCrossingSource {ι : Type*} [DecidableEq ι]
    (A : Set (MvPolynomial ι ℂ)) (r : ℕ) : Prop :=
  A = (veroneseIdeal ℂ ι r : Set (MvPolynomial ι ℂ))

/-- **Transport.**  Two realizations of the same order have the same annihilator. -/
theorem IsNormalCrossingSource.eq {ι : Type*} [DecidableEq ι]
    {A B : Set (MvPolynomial ι ℂ)} {r : ℕ}
    (hA : IsNormalCrossingSource A r) (hB : IsNormalCrossingSource B r) : A = B :=
  hA.trans hB.symm

/-- **The complete physical package of a normal-crossing source.**  Source height, arc-contact
order, powered period-incidence level and the polarizing half-density are all determined by the
order `r`. -/
theorem physicalPackage_of_isNormalCrossingSource
    {ι : Type*} [DecidableEq ι] {A : Set (MvPolynomial ι ℂ)} {r : ℕ}
    (hA : IsNormalCrossingSource A r) (hr : 1 ≤ r)
    (τ : ι → ℂ) (hτ : ∀ j, τ j ≠ 0) {S : Finset ι} (hS : S.card = r)
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    IsLeast {n | ∃ P ∈ A, P ≠ 0 ∧ augDegree P = n} r ∧
      (∏ j ∈ S, MvPolynomial.X j) ∈ A ∧
      ((∀ P ∈ A, (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ P) ∧
        ¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
          physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) ∧
      ((∀ P ∈ A, arcEvalVector L (physicalArcPullback τ P) ∈
          Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
        arcEvalVector L (physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j)) ∉
          Set.range (poweredPeriodIncidenceMultiplier L (r + 1))) ∧
      (poweredPeriodIncidenceHalfDensity L r ∈
          closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
        poweredPeriodIncidenceHalfDensity L r ∉
          Set.range (poweredPeriodIncidenceMultiplier L r)) := by
  subst hA
  exact ⟨isLeast_augDegrees_veroneseIdeal hS, Ideal.subset_span ⟨S, hS, rfl⟩,
    ⟨fun _ hP => pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hP,
      (physicalArcPullback_generator_ne_zero τ hτ hS).2⟩,
    veroneseIdeal_arcEval_poweredRange_exact L hL τ hτ hS,
    poweredPeriodIncidenceHalfDensity_closureOnly L hL r hr⟩

/-! ## The two realizations of the multiple elliptic gamma -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The additive realization is a normal-crossing source. -/
theorem isNormalCrossingSource_daTranslationAnnihilator
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (r : ℕ) (hcard : Fintype.card ι = r + 1) :
    IsNormalCrossingSource (daTranslationAnnihilator τ hτ) r :=
  daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r hcard

/-- The multiplicative realization is the pullback of the same source along the exponent-operator
map. -/
theorem multiplicativeDaAnnihilator_eq_preimage
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (r : ℕ) (hcard : Fintype.card ι = r + 1) :
    multiplicativeDaAnnihilator τ hτ =
      translateProductOperator ⁻¹' (veroneseIdeal ℂ ι r : Set (MvPolynomial ι ℂ)) := by
  ext c
  rw [Set.mem_preimage, mem_multiplicativeDaAnnihilator_iff τ hτ hQ r hcard,
    daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r hcard]

/-! ## The package does not see the period frame -/

/-- **`[NO-GO]` Frame blindness.**  Any two nonvanishing period frames of the same order give the
same arc-contact order and the same convergent fat-point length, so the physical package cannot
separate two sources sharing the normal-crossing annihilator. -/
theorem physicalPackage_frame_blind (r : ℕ)
    (τ τ' : Fin (r + 1) → ℂ) (hτ : ∀ j, τ j ≠ 0) (hτ' : ∀ j, τ' j ≠ 0)
    {S : Finset (Fin (r + 1))} (hS : S.card = r) :
    Module.length ConvergentGerm (ConvergentGerm ⧸ convergentCofaceIdeal r τ) =
        Module.length ConvergentGerm (ConvergentGerm ⧸ convergentCofaceIdeal r τ') ∧
      (∀ P ∈ veroneseIdeal ℂ (Fin (r + 1)) r,
          (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ P ∧
            (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ' P) ∧
      (¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
          physicalArcPullback τ (∏ j ∈ S, MvPolynomial.X j) ∧
        ¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
          physicalArcPullback τ' (∏ j ∈ S, MvPolynomial.X j)) := by
  refine ⟨?_, fun P hP => ⟨pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hP,
      pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ' hP⟩,
    (physicalArcPullback_generator_ne_zero τ hτ hS).2,
    (physicalArcPullback_generator_ne_zero τ' hτ' hS).2⟩
  rw [convergentCofaceIdeal_quotient_length r τ hτ,
    convergentCofaceIdeal_quotient_length r τ' hτ']

/-! ## What the symbol spectrum retains -/

/-- **The conservative invariant is the pair.**  The physical package is the same for every
nonvanishing frame of a given order, while the bounded symbol spectrum determines the embedded
period module exactly.  So a source theory that keeps only the package loses the period data, and
a source theory that keeps the pair does not. -/
theorem physicalPackage_blind_symbolSpectrum_separates (r : ℕ)
    (τ τ' : Fin (r + 1) → ℂ) (hτ : ∀ j, τ j ≠ 0) (hτ' : ∀ j, τ' j ≠ 0) :
    Module.length ConvergentGerm (ConvergentGerm ⧸ convergentCofaceIdeal r τ) =
        Module.length ConvergentGerm (ConvergentGerm ⧸ convergentCofaceIdeal r τ') ∧
      ∀ L K : Submodule ℤ ℂ,
        regularizedPeriodSpectrum L = regularizedPeriodSpectrum K ↔ L = K := by
  refine ⟨?_, fun L K => regularizedPeriodSpectrum_eq_iff L K⟩
  rw [convergentCofaceIdeal_quotient_length r τ hτ,
    convergentCofaceIdeal_quotient_length r τ' hτ']

end

end GaloisForLFunctions
