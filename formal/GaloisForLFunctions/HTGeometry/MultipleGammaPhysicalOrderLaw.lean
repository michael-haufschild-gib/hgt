import GaloisForLFunctions.HTGeometry.VeroneseSourceHeightIncidence
import GaloisForLFunctions.HTGeometry.RelativeLogCharacteristicSourceBridge
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDepthValue
import GaloisForLFunctions.HTGeometry.ConvergentGermPhysicalArc

/-!
# One order for the generic multiple elliptic gamma

The differential-algebraic translation annihilator of a generic order-`r` multiple elliptic gamma
logarithmic derivative is the squarefree degree-`r` ideal, so its source height — the least total
degree of a nonzero annihilating operator — is exactly `r`.

That integer is simultaneously the transverse differential-algebraic depth, the order of contact of
the annihilator along the physical exponential arc, the length of the convergent physical fat point,
and the level of the powered period-incidence filtration at which the arc image is detected.  Each
is computed from a different structure — differential algebra, filtered operator degree, arc
geometry, local intersection theory in `ℂ{λ}`, and the bounded incidence space of the period
symbol — and all five return `r`.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

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

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The source height of the genuine annihilator -/

/-- **`ht_src(Ψ_r) = r`.**  The least total degree of a nonzero difference operator carrying the
generic order-`r` multiple elliptic gamma logarithmic derivative into the differentially algebraic
locus is exactly `r`. -/
theorem isLeast_sourceDegrees_daTranslationAnnihilator
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (r : ℕ) (hcard : Fintype.card ι = r + 1) {J : Finset ι} (hJ : J.card = r) :
    IsLeast {n | ∃ P ∈ daTranslationAnnihilator τ hτ, P ≠ 0 ∧ P.totalDegree = n} r := by
  have hset : {n | ∃ P ∈ daTranslationAnnihilator τ hτ, P ≠ 0 ∧ P.totalDegree = n} =
      VeroneseIdeal.sourceDegrees ℂ ι r := by
    rw [daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r hcard]
    rfl
  rw [hset]
  exact VeroneseIdeal.isLeast_sourceDegrees hJ

/-! ## The order law -/

/-- A period in the upper half plane is nonzero. -/
theorem ne_zero_of_im_pos {t : ℂ} (ht : 0 < t.im) : t ≠ 0 := by
  rintro rfl
  simp at ht

/-- **The order law of the generic multiple elliptic gamma.**  For a generic order-`r` family and a
nondiscrete integral period source, five independently defined integers all equal `r`:

* the transverse differential-algebraic depth;
* the source height of the differential-algebraic translation annihilator;
* the order of contact of that annihilator along the physical exponential arc;
* the length of the convergent physical fat point in `ℂ{λ}`;
* the level of the powered period-incidence filtration detecting the arc image.
-/
theorem multipleGamma_physicalOrderLaw
    (r : ℕ) (hr : 1 ≤ r) (τ : Fin (r + 1) → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ)
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    multipleEllipticGammaTransverseDADepth τ hτ = r ∧
      IsLeast {n | ∃ P ∈ daTranslationAnnihilator τ hτ, P ≠ 0 ∧ P.totalDegree = n} r ∧
      ((∀ P ∈ daTranslationAnnihilator τ hτ,
          (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ P) ∧
        ¬ (Polynomial.X : Polynomial ℂ) ^ (r + 1) ∣
          physicalArcPullback τ
            (∏ j ∈ Finset.univ.erase (0 : Fin (r + 1)), MvPolynomial.X j)) ∧
      Module.length ConvergentGerm (ConvergentGerm ⧸ convergentCofaceIdeal r τ) = r ∧
      ((∀ P ∈ daTranslationAnnihilator τ hτ,
          arcEvalVector L (physicalArcPullback τ P) ∈
            Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
        arcEvalVector L (physicalArcPullback τ
            (∏ j ∈ Finset.univ.erase (0 : Fin (r + 1)), MvPolynomial.X j)) ∉
          Set.range (poweredPeriodIncidenceMultiplier L (r + 1))) := by
  classical
  have hcard : Fintype.card (Fin (r + 1)) = r + 1 := Fintype.card_fin _
  have hne : ∀ j, τ j ≠ 0 := fun j => ne_zero_of_im_pos (hτ j)
  have hJ : (Finset.univ.erase (0 : Fin (r + 1))).card = r := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hann : daTranslationAnnihilator τ hτ =
      (veroneseIdeal ℂ (Fin (r + 1)) r : Set (MvPolynomial (Fin (r + 1)) ℂ)) :=
    daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r hcard
  have hmem : ∀ P, P ∈ daTranslationAnnihilator τ hτ →
      P ∈ veroneseIdeal ℂ (Fin (r + 1)) r := by
    intro P hP
    rw [hann] at hP
    exact hP
  refine ⟨multipleEllipticGammaTransverseDADepth_eq_order τ hτ hQ r hr hcard,
    isLeast_sourceDegrees_daTranslationAnnihilator τ hτ hQ r hcard hJ,
    ⟨fun P hP => pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ (hmem P hP), ?_⟩,
    convergentCofaceIdeal_quotient_length r τ hne,
    ⟨fun P hP => veroneseIdeal_arcEval_mem_poweredRange L τ (hmem P hP), ?_⟩⟩
  · exact (physicalArcPullback_generator_ne_zero τ hne hJ).2
  · exact (veroneseIdeal_arcEval_poweredRange_exact L hL τ hne hJ).2

end

end GaloisForLFunctions
