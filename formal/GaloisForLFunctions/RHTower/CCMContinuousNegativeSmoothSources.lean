import GaloisForLFunctions.RHTower.CCMContinuousLocalizationInvariant
import GaloisForLFunctions.RHTower.CCMOddContinuousNegativeTail

/-!
# Negative continuous arithmetic on actual smooth sources

The odd pole's negative continuous energy survives approximation in the
complete archimedean form norm. Thus compact smooth sources, and their exact
finite localization invariants, attain continuous values below any prescribed
real level. The full arithmetic sign still includes the prime correlation.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProduct SchwartzMap

namespace RHTower

open ThetaSourceWard

/-- The continuous quadratic extended to the complete form domain by adding back primes. -/
def ccmContinuousFormQuadratic (a : SuzukiPositiveAperture)
    (v : CCMArchimedeanFormDomain a) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a v +
    (inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a v))
      (ccmArchimedeanFormToAperture a v)).re

theorem continuous_ccmContinuousFormQuadratic (a : SuzukiPositiveAperture) :
    Continuous (ccmContinuousFormQuadratic a) := by
  apply (continuous_ccmRestrictedWeilSourceQuadratic a).add
  exact Complex.continuous_re.comp
    (((ccmFinitePrimeOperator a).continuous.comp (ccmArchimedeanFormToAperture a).continuous).inner
      (ccmArchimedeanFormToAperture a).continuous)

theorem ccmFinitePrimeOperator_ccmSource_eq_thetaPrime {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    (inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u.toCCMFormVector))
      (ccmArchimedeanFormToAperture a u.toCCMFormVector)).re =
      2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction := by
  rw [thetaPrimeScalingCross_ccmProfile_twoSided]
  apply congrArg Complex.re
  rw [inner_ccmFinitePrimeOperator]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_ccmPrimeTransportOperator]
  simp_rw [inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation, neg_neg]
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1
  rw [criticalMellinAtomWeight_eq_primePairWeight hnpos]
  unfold GaloisForLFunctions.HTGeometry.primePairWeight
  push_cast
  ring

theorem ccmContinuousFormQuadratic_ccmSmooth {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmContinuousFormQuadratic a u.toCCMFormVector = ccmContinuousArithmeticQuadratic u := by
  rw [ccmContinuousArithmeticQuadratic_eq_weil_add_prime, ccmContinuousFormQuadratic,
    ccmFinitePrimeOperator_ccmSource_eq_thetaPrime]

theorem ccmContinuousFormQuadratic_oddPole (a : SuzukiPositiveAperture) :
    ccmContinuousFormQuadratic a (ccmPolarParityFormVector a (-1)) =
      ccmOddPoleGammaPolarBalance a := by
  have hp := ccmFinitePrimeOperator_polar_odd_eq_budgets a
  rw [ccmContinuousFormQuadratic, ccmWeilOddPole_eq_prime_budgets,
    ccmArchimedeanFormToAperture_polarParity]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, ← sub_eq_add_neg]
  linarith only [hp]

/-- Density transfers the strict continuous inequality to literal compact smooth sources. -/
theorem exists_ccmSmoothSource_continuous_below (R : ℝ) :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      ccmContinuousArithmeticQuadratic u < R := by
  obtain ⟨a, ha⟩ := ccmOddPoleGammaPolarBalance_unbounded_below R
  have hmem : {v : CCMArchimedeanFormDomain a | ccmContinuousFormQuadratic a v < R} ∈
      nhds (ccmPolarParityFormVector a (-1)) := by
    have hi : Iio R ∈ nhds (ccmContinuousFormQuadratic a (ccmPolarParityFormVector a (-1))) :=
      Iio_mem_nhds (by rwa [ccmContinuousFormQuadratic_oddPole])
    exact (continuous_ccmContinuousFormQuadratic a).continuousAt hi
  obtain ⟨u, hu⟩ := (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds hmem
  refine ⟨a, u, ?_⟩
  change ccmContinuousFormQuadratic a u.toCCMFormVector < R at hu
  rwa [ccmContinuousFormQuadratic_ccmSmooth] at hu

/-- Fine localization's exact continuous invariant has no universal lower bound. -/
theorem exists_ccmFineLocalization_continuous_invariant_below (R : ℝ) :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (angles : List 𝓢(ℝ, ℝ)),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ,
        tsupport v ⊆ Metric.ball c (Real.log 2 / 4)) ∧
      (∀ x, ccmLocalizationRemainder u angles x = 0) ∧
      ccmLocalizationCompensatedEnergy u angles = ccmContinuousArithmeticQuadratic u ∧
      ccmLocalizationCompensatedEnergy u angles < R := by
  obtain ⟨a, u, hu⟩ := exists_ccmSmoothSource_continuous_below R
  obtain ⟨angles, hc, hs, hz, he, _⟩ := exists_ccmFiniteLocalization_continuous_invariant a u
  exact ⟨a, u, angles, hc, hs, hz, he, he.trans_lt hu⟩

end RHTower
