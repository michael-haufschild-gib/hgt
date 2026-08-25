import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveVacuumFusion

/-!
# Contiguity forces aperture evacuation away from the adaptive fixed point

This module isolates a route-independent source law: asymptotically separating responses cannot
be observed on two fixed contiguous probability laws unless the observation aperture loses all
forward mass.  The adaptive prime occupation orbit then gives an exact alternative: horizontal
grade is neutral, or every such coefficient-faithful realization evacuates its aperture.

Unlike a uniform-admission selector, the contrapositive needs only failure of convergence to zero;
a positive subsequence already selects the critical fixed point.
-/

open Real Set MeasureTheory InformationTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-- A reflected response that asymptotically separates two contiguous fixed sources can survive
only on an admission aperture whose forward mass tends to zero. -/
theorem tendsto_forwardAdmission_zero_of_contiguous_asymptoticSeparation
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (hPR : P ≪ R) (forward reverse : ℕ → ℝ)
    (hforward : Tendsto forward atTop (𝓝 1))
    (hreverse : Tendsto reverse atTop (𝓝 0))
    (hreverse_nonneg : ∀ n, 0 ≤ reverse n)
    (admitted success : ℕ → Set Ω)
    (hPconditional : ∀ n,
      (P (success n)).toReal = forward n * (P (admitted n)).toReal)
    (hRconditional : ∀ n,
      (R (success n)).toReal = reverse n * (R (admitted n)).toReal) :
    Tendsto (fun n => (P (admitted n)).toReal) atTop (𝓝 0) := by
  have hRbound (n : ℕ) : (R (success n)).toReal ≤ reverse n := by
    rw [hRconditional n]
    have hmass : (R (admitted n)).toReal ≤ 1 := by
      have hmono : R (admitted n) ≤ R Set.univ := measure_mono (subset_univ _)
      have hreal := ENNReal.toReal_mono (measure_ne_top R Set.univ) hmono
      simpa using hreal
    exact mul_le_of_le_one_right (hreverse_nonneg n) hmass
  have hRzeroReal : Tendsto (fun n => (R (success n)).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) hRbound hreverse
  have hRzero : Tendsto (fun n => R (success n)) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => measure_ne_top R (success n))).mp hRzeroReal
  have hPzero := tendsto_measure_zero_of_absolutelyContinuous_finite
    P R hPR hRzero
  have hPzeroReal : Tendsto (fun n => (P (success n)).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => measure_ne_top P (success n))).mpr hPzero
  have hforwardHalf : ∀ᶠ n : ℕ in atTop, 1 / 2 < forward n :=
    hforward (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hbound : ∀ᶠ n : ℕ in atTop,
      (P (admitted n)).toReal ≤ 2 * (P (success n)).toReal := by
    filter_upwards [hforwardHalf] with n hn
    rw [hPconditional n]
    nlinarith [show 0 ≤ (P (admitted n)).toReal from ENNReal.toReal_nonneg]
  have hdouble : Tendsto (fun n => 2 * (P (success n)).toReal) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hPzeroReal
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    hbound hdouble

/-- Under fixed-source contiguity, every nonneutral adaptive RG orbit can survive only by
evacuating its forward admission aperture. -/
theorem tendsto_sourceHorizontalPrimeAdaptive_forwardAdmission_zero_of_nonzero_contiguity
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d) (ht : t ≠ 0) (hPR : P ≪ R)
    (admitted success : ℕ → Set Ω)
    (hPconditional : ∀ n,
      (P (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) *
          (P (admitted n)).toReal)
    (hRconditional : ∀ n,
      (R (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) *
          (R (admitted n)).toReal) :
    Tendsto (fun n => (P (admitted n)).toReal) atTop (𝓝 0) := by
  exact tendsto_forwardAdmission_zero_of_contiguous_asymptoticSeparation
    P R hPR
    (fun n => sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|))
    (fun n => sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)))
    (tendsto_sourceHorizontalPrimeAdaptiveOccupation_scale_one (p := p) hd ht)
    (tendsto_sourceHorizontalPrimeAdaptiveOccupation_reflectedScale_zero (p := p) hd ht)
    (fun n => (sourceHorizontalPrimeAdaptiveOccupation_pos p
      (-(d ^ n * |t|))).le)
    admitted success hPconditional hRconditional

/-- Fixed point or aperture evacuation: exhaustive contiguity dichotomy for a reflected
adaptive RG realization. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_or_forwardAdmission_evacuation
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d) (hPR : P ≪ R)
    (admitted success : ℕ → Set Ω)
    (hPconditional : ∀ n,
      (P (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) *
          (P (admitted n)).toReal)
    (hRconditional : ∀ n,
      (R (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) *
          (R (admitted n)).toReal) :
    t = 0 ∨ Tendsto (fun n => (P (admitted n)).toReal) atTop (𝓝 0) := by
  by_cases ht : t = 0
  · exact Or.inl ht
  · exact Or.inr
      (tendsto_sourceHorizontalPrimeAdaptive_forwardAdmission_zero_of_nonzero_contiguity
        P R p hd ht hPR admitted success hPconditional hRconditional)

/-- Any failure of aperture evacuation rules out a nonneutral relevant coupling.  This strictly
weakens a uniform positive aperture bound: a positive subsequential aperture already suffices. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_not_forwardAdmission_evacuation
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d) (hPR : P ≪ R)
    (admitted success : ℕ → Set Ω)
    (hPconditional : ∀ n,
      (P (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) *
          (P (admitted n)).toReal)
    (hRconditional : ∀ n,
      (R (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) *
          (R (admitted n)).toReal)
    (hnonEvacuation : ¬ Tendsto (fun n => (P (admitted n)).toReal) atTop (𝓝 0)) :
    t = 0 := by
  rcases sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_or_forwardAdmission_evacuation
      P R p hd hPR admitted success hPconditional hRconditional with ht | hevac
  · exact ht
  · exact (hnonEvacuation hevac).elim

/-- Actual convergent abelian class laws obey the same fixed-point/evacuation alternative without
any separately assumed source-information bound. -/
theorem sourceHorizontalPrimeAdaptive_abelianClassLaw_fixedPoint_or_forwardAdmission_evacuation
    (thetaP thetaR : AbelianZetaConvergentParameters)
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d)
    (admitted success : ℕ → Set AbelianZetaGroupClass)
    (hPconditional : ∀ n,
      ((classLaw thetaP.toAbelianZetaParameters) (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) *
          ((classLaw thetaP.toAbelianZetaParameters) (admitted n)).toReal)
    (hRconditional : ∀ n,
      ((classLaw thetaR.toAbelianZetaParameters) (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) *
          ((classLaw thetaR.toAbelianZetaParameters) (admitted n)).toReal) :
    t = 0 ∨ Tendsto (fun n =>
      ((classLaw thetaP.toAbelianZetaParameters) (admitted n)).toReal)
        atTop (𝓝 0) := by
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_or_forwardAdmission_evacuation
    (classLaw thetaP.toAbelianZetaParameters)
    (classLaw thetaR.toAbelianZetaParameters) p hd
    (classLaw_absolutelyContinuous thetaR thetaP)
    admitted success hPconditional hRconditional

/-- At a multiplicity-labelled Xi zero, a contiguous coefficient-faithful reflected realization
has only two phases: critical real part, or forward source aperture evacuation. -/
theorem sourceHorizontalXi_abelianClassLaw_re_eq_half_or_forwardAdmission_evacuation
    (q : XiZeroCopy) (thetaP thetaR : AbelianZetaConvergentParameters)
    (p : Nat.Primes) {d : ℝ} (hd : 1 < d)
    (admitted success : ℕ → Set AbelianZetaGroupClass)
    (hPconditional : ∀ n,
      ((classLaw thetaP.toAbelianZetaParameters) (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p
            (d ^ n * |primeDepthBVWoldXiCenteredRate q.1|) *
          ((classLaw thetaP.toAbelianZetaParameters) (admitted n)).toReal)
    (hRconditional : ∀ n,
      ((classLaw thetaR.toAbelianZetaParameters) (success n)).toReal =
        sourceHorizontalPrimeAdaptiveOccupation p
            (-(d ^ n * |primeDepthBVWoldXiCenteredRate q.1|)) *
          ((classLaw thetaR.toAbelianZetaParameters) (admitted n)).toReal) :
    (q.1 : ℂ).re = 1 / 2 ∨ Tendsto (fun n =>
      ((classLaw thetaP.toAbelianZetaParameters) (admitted n)).toReal)
        atTop (𝓝 0) := by
  rcases sourceHorizontalPrimeAdaptive_abelianClassLaw_fixedPoint_or_forwardAdmission_evacuation
      thetaP thetaR p hd admitted success hPconditional hRconditional with hzero | hevac
  · exact Or.inl ((primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hzero)
  · exact Or.inr hevac

end

end RHTower
