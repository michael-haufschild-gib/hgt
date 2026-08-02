import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTransverseDADepth
import GaloisForLFunctions.HTGeometry.PeriodIntegralIndependenceWitness

/-!
# The transverse differential-algebraic depth of a generic multiple elliptic gamma

For a period family with no integral relation to `1`, a deleted face is differentially algebraic
exactly when at most one period survives: two surviving periods are rationally independent together
with `1`, hence give a rank-three minor and hypertranscendence.

The least admissible deletion is therefore the complement of a single period, so the transverse
differential-algebraic depth is one less than the number of periods — for an order-`r` family,
exactly `r`.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Deleting all but one period reaches the differentially algebraic locus. -/
theorem differentialAlgebraicOver_face_compl_singleton
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (q : ι) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ ({q}ᶜ)) := by
  classical
  refine differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_unique_survivor
    τ hτ ({q}ᶜ) (q := q) (by simp) ?_
  intro i hi
  simpa using hi

/-- A face keeping two periods of a generic family is hypertranscendental. -/
theorem not_differentialAlgebraicOver_face_of_two_survivors
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) (hJ : 2 ≤ (Jᶜ).card) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  classical
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp (by omega : 1 < (Jᶜ).card)
  exact not_differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_of_independentPair
    τ hτ J (Finset.mem_compl.mp hq) (Finset.mem_compl.mp hr) hqr
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hqr)

/-- **Exact transverse depth.**  A generic multiple elliptic gamma has transverse
differential-algebraic depth one less than its number of periods. -/
theorem multipleEllipticGammaTransverseDADepth_eq_card_sub_one
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hι : 2 ≤ Fintype.card ι) :
    multipleEllipticGammaTransverseDADepth τ hτ = Fintype.card ι - 1 := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨q⟩ := (inferInstance : Nonempty ι)
  refine multipleEllipticGammaTransverseDADepth_eq_of_min τ hτ _ ?_ ?_
  · refine ⟨({q}ᶜ : Finset ι), ?_, differentialAlgebraicOver_face_compl_singleton τ hτ q⟩
    have hcard := Finset.card_add_card_compl ({q} : Finset ι)
    simp only [Finset.card_singleton] at hcard
    omega
  · intro J hJ
    refine not_differentialAlgebraicOver_face_of_two_survivors τ hτ hQ J ?_
    have hcard := Finset.card_add_card_compl J
    omega

/-- **Order-`r` form.**  A generic order-`r` multiple elliptic gamma, carried by `r + 1` periods,
has transverse differential-algebraic depth exactly `r`. -/
theorem multipleEllipticGammaTransverseDADepth_eq_order
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card ι = r + 1) :
    multipleEllipticGammaTransverseDADepth τ hτ = r := by
  rw [multipleEllipticGammaTransverseDADepth_eq_card_sub_one τ hτ hQ (by omega), hcard]
  omega

end

end GaloisForLFunctions
