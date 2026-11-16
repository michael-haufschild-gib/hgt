import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubicThetaCorrectionHasAHolomorphicRepresentative
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedContinuationHasNoMellinPoles
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheCubeZetaReciprocalHasPolynomialGrowth
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedSquarefreeSeriesIsHolomorphicInitially

/-!
# The squarefree continuation across the real axis

Meromorphic normal form fills the removable real values of the Eisenstein
correction. Cube removal is nonvanishing on `Re s>5/4`, and the Bessel Mellin
factor is nonvanishing there. The resulting squarefree continuation is
holomorphic on `5/8<Re w<13/6` away from `2/3`, with the original nonzero residue.
The identity theorem identifies it with the arithmetic series on `Re w>1`.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent.CubicEisenstein

/-- The unramified completed square with removable spectral values filled in. -/
def regularizedCompletedUnramified (s : ℂ) : ℂ :=
  (2 / 3) * periodArea⁻¹ * (seedPair s - transSeedPair s +
    (levelPairing renormalizedThetaSq renormalizedThetaSq_memLp -
      levelPairing translatedRenormalized translatedRenormalized_memLp)
        (regularizedEisensteinCorrection s) +
      thetaCoeff ^ 2 * (clearedScatterTotal s - clearedTransScatter s) *
        ((2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2))

private theorem regularizedCompletedUnramified_eq_of_correction_eq (s : ℂ)
    (hc : regularizedEisensteinCorrection s = eisensteinCorrection s) :
    regularizedCompletedUnramified s = completedUnramified s := by
  simp only [regularizedCompletedUnramified, hc, ContinuousLinearMap.sub_apply,
    completedUnramified, completedThetaSq, completedTranslated, corrPair, transCorrPair]
  ring

theorem regularizedCompletedUnramified_differentiableAt (s : ℂ) (hs : 1 < s.re)
    (hB : s.re < 13 / 3) (hp : s ≠ 4 / 3) :
    DifferentiableAt ℂ regularizedCompletedUnramified s := by
  have hseed := (seedPair_differentiableAt s (by linarith) hB).sub
    (transSeedPair_differentiableAt s (by linarith) hB)
  have hcorr := ((levelPairing renormalizedThetaSq renormalizedThetaSq_memLp -
      levelPairing translatedRenormalized translatedRenormalized_memLp).analyticAt
      (regularizedEisensteinCorrection s)).comp
        (regularizedEisensteinCorrection_analyticAt s hs hp)
  have hscatter := (clearedScatterTotal_differentiableAt s hs).sub
    (clearedTransScatter_differentiableAt s hs)
  have hpow : DifferentiableAt ℂ (fun s : ℂ =>
      (2 : ℂ) ^ (4 / 3 - s) / (s - 4 / 3) ^ 2) s :=
    (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl two_ne_zero)).div
      ((differentiableAt_id.sub_const _).pow 2) (pow_ne_zero 2 (sub_ne_zero.mpr hp))
  exact ((hseed.add hcorr.differentiableAt).add
    ((hscatter.const_mul _).mul hpow)).const_mul _

/-- The actual squarefree continuation, with its removable real values filled in. -/
def regularizedUntwistedTheta (w : ℂ) : ℂ :=
  ((2 * w - 4 / 3) * regularizedCompletedUnramified (2 * w) /
    (2 * unitFrequencyWeight (2 * w) * star rationalSourceThetaScalar ^ 2 * (2 / 3) *
      clearedCubeZeta (2 * w))) / besselSqMellin (2 * w)

private theorem regularizedUntwistedTheta_eq_of_correction_eq (w : ℂ)
    (hc : regularizedEisensteinCorrection (2 * w) = eisensteinCorrection (2 * w)) :
    regularizedUntwistedTheta w = continuedUntwistedTheta w := by
  rw [regularizedUntwistedTheta, regularizedCompletedUnramified_eq_of_correction_eq _ hc]
  rfl

theorem regularizedUntwistedTheta_eq_nonreal (w : ℂ) (hw : 5 / 8 < w.re)
    (hi : w.im ≠ 0) : regularizedUntwistedTheta w = continuedUntwistedTheta w := by
  apply regularizedUntwistedTheta_eq_of_correction_eq
  apply regularizedEisensteinCorrection_eq_nonreal
  · simp
    linarith
  · simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hi

/-- The filled continuation is holomorphic throughout the strip except at `2/3`. -/
theorem regularizedUntwistedTheta_differentiableAt (w : ℂ) (hw : 5 / 8 < w.re)
    (hB : w.re < 13 / 6) (hp : w ≠ 2 / 3) :
    DifferentiableAt ℂ regularizedUntwistedTheta w := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 2 * w) w := differentiableAt_id.const_mul 2
  have hr : 5 / 4 < (2 * w).re := by simp; linarith
  have hM : 2 / 3 < (2 * w).re := by linarith
  have hp' : 2 * w ≠ 4 / 3 := by
    intro h
    apply hp
    linear_combination h / 2
  have hΛ := (regularizedCompletedUnramified_differentiableAt (2 * w)
    (by linarith) (by simp; linarith) hp').comp w hlin
  have hfreq := (unitFrequencyWeight_differentiable (2 * w)).comp w hlin
  have hcube := (clearedCubeZeta_differentiable (2 * w)).comp w hlin
  have hden : 2 * unitFrequencyWeight (2 * w) * star rationalSourceThetaScalar ^ 2 * (2 / 3) *
      clearedCubeZeta (2 * w) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (unitFrequencyWeight_ne_zero _)) (pow_ne_zero 2 scalar_star_ne_zero)) (by norm_num))
        (clearedCubeZeta_ne_zero_right_of_five_fourths _ hr)
  exact (((hlin.sub_const _).mul hΛ).div
    ((((hfreq.const_mul _).mul_const _).mul_const _).mul hcube) hden).div
      ((besselSqMellin_differentiableAt _ hM).comp w hlin) (besselSqMellin_ne_zero _ hM)

private theorem double_parameter_tendsto_punctured :
    Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] (2 / 3 : ℂ)) (𝓝[≠] (4 / 3 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have ht : Tendsto (fun w : ℂ => 2 * w) (𝓝 (2 / 3 : ℂ)) (𝓝 (2 * (2 / 3 : ℂ))) :=
      (continuous_const.mul continuous_id).tendsto (2 / 3 : ℂ)
    rw [show (2 : ℂ) * (2 / 3) = 4 / 3 by norm_num] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw he
    apply hw
    change w = 2 / 3
    change 2 * w = 4 / 3 at he
    linear_combination he / 2

theorem regularizedUntwistedTheta_eventually_eq_center :
    regularizedUntwistedTheta =ᶠ[𝓝[≠] (2 / 3 : ℂ)] continuedUntwistedTheta := by
  filter_upwards [double_parameter_tendsto_punctured.eventually
    regularizedEisensteinCorrection_eventually_eq_center] with w hw
  exact regularizedUntwistedTheta_eq_of_correction_eq w hw

theorem regularizedUntwistedTheta_simple_pole :
    Tendsto (fun w => (w - 2 / 3) * regularizedUntwistedTheta w) (𝓝[≠] (2 / 3 : ℂ))
      (𝓝 untwistedThetaResidue) := by
  refine continuedUntwistedTheta_simple_pole.congr' ?_
  filter_upwards [regularizedUntwistedTheta_eventually_eq_center] with w hw
  rw [hw]

/-- The filled continuation agrees with the convergent series on both halves of the initial strip. -/
theorem regularizedUntwistedTheta_eq_series (w : ℂ) (hw : 1 < w.re)
    (hB : w.re < 13 / 6) : regularizedUntwistedTheta w = twistedSquarefreeSeries 1 w := by
  let U : Set ℂ := {z | 1 < z.re ∧ z.re < 13 / 6}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hconv : Convex ℝ U :=
    (convex_halfSpace_gt ⟨fun _ _ => rfl, fun c z => by simp⟩ (1 : ℝ)).inter
      (convex_halfSpace_lt ⟨fun _ _ => rfl, fun c z => by simp⟩ (13 / 6 : ℝ))
  have hf : AnalyticOnNhd ℂ regularizedUntwistedTheta U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    apply (regularizedUntwistedTheta_differentiableAt z (by linarith only [hz.1]) hz.2 ?_).differentiableWithinAt
    intro he
    have hre := hz.1
    rw [he] at hre
    norm_num at hre
  have hg : AnalyticOnNhd ℂ (twistedSquarefreeSeries 1) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (twistedSquarefreeSeries_one_differentiableAt z hz.1).differentiableWithinAt
  have hc : (25 / 12 + Complex.I : ℂ) ∈ U := by norm_num [U]
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected hc _ ⟨hw, hB⟩
  have hopen : IsOpen {z : ℂ | 2 < z.re ∧ z.re < 13 / 6 ∧ 0 < z.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))
  filter_upwards [hopen.mem_nhds (by norm_num)] with z hz
  rw [regularizedUntwistedTheta_eq_nonreal z (by linarith only [hz.1]) hz.2.2.ne']
  exact continuedUntwistedTheta_eq_series z hz.1 hz.2.1 hz.2.2

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
