import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalSourceQuantitative

/-!
# Concrete sources realizing both critical Nyquist alternatives

The fixed smooth bump has positive mean. Its difference with its translate by
four has zero mean and normalized correlation exactly minus one half at lag four.
Both stretched families have vanishing normalized archimedean energy.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

/-- The original unit-radius bump as a compact continuous source. -/
def nyquistPositiveMeanWitness : C_c(ℝ, ℝ) :=
  ⟨⟨nyquistWideBump, nyquistWideBump.continuous⟩, nyquistWideBump.hasCompactSupport⟩

theorem contDiff_nyquistPositiveMeanWitness (r : ℕ∞) :
    ContDiff ℝ (r : WithTop ℕ∞) (nyquistPositiveMeanWitness : ℝ → ℝ) :=
  nyquistWideBump.contDiff (n := r)

theorem nyquistPositiveMeanWitness_integral_pos : 0 < ∫ u, nyquistPositiveMeanWitness u := by
  exact nyquistWideBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    nyquistWideBump.hasCompactSupport (fun u => nyquistWideBump.nonneg)
    (x := 0) (by change nyquistWideBump 0 ≠ 0; rw [nyquistWideBump_zero]; norm_num)

theorem nyquistPositiveMeanWitness_ne_zero : nyquistPositiveMeanWitness ≠ 0 := by
  intro h
  have hh := congrArg (fun f : C_c(ℝ, ℝ) => f 0) h
  change nyquistWideBump 0 = 0 at hh
  rw [nyquistWideBump_zero] at hh
  exact one_ne_zero hh

private theorem nyquistWideBump_zero_of_one_le_abs (u : ℝ) (hu : 1 ≤ |u|) :
    nyquistWideBump u = 0 := by
  apply nyquistWideBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, nyquistWideBump] using hu

theorem nyquistZeroMeanWitness_zero : nyquistZeroMeanWitness 0 = 1 := by
  change nyquistWideBump 0 - nyquistWideBump (0 - 4) = 1
  rw [nyquistWideBump_zero, nyquistWideBump_zero_of_one_le_abs (0 - 4) (by norm_num), sub_zero]

theorem nyquistZeroMeanWitness_ne_zero : nyquistZeroMeanWitness ≠ 0 := by
  intro h
  have hh := congrArg (fun f : C_c(ℝ, ℝ) => f 0) h
  change nyquistZeroMeanWitness 0 = 0 at hh
  rw [nyquistZeroMeanWitness_zero] at hh
  exact one_ne_zero hh

theorem contDiff_nyquistZeroMeanWitness (r : ℕ∞) :
    ContDiff ℝ (r : WithTop ℕ∞) (nyquistZeroMeanWitness : ℝ → ℝ) := by
  change ContDiff ℝ (r : WithTop ℕ∞)
    (fun u => nyquistWideBump u - nyquistWideBump (u - 4))
  exact (nyquistWideBump.contDiff (n := r)).sub
    ((nyquistWideBump.contDiff (n := r)).comp (contDiff_id.sub contDiff_const))

/-- The bump correlation vanishes at and beyond the full support diameter. -/
theorem nyquistWideBump_autocorr_zero_of_two_le_abs {x : ℝ} (hx : 2 ≤ |x|) :
    autocorr (nyquistWideBump : ℝ → ℝ) x = 0 := by
  unfold autocorr
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun u => by
    change nyquistWideBump u * nyquistWideBump (u + x) = 0
    by_cases hu : 1 ≤ |u|
    · rw [nyquistWideBump_zero_of_one_le_abs u hu, zero_mul]
    · have hv : 1 ≤ |u + x| := by
        by_contra hv
        have hu' := lt_of_not_ge hu
        have hv' := lt_of_not_ge hv
        have ht := abs_add_le (-u) (u + x)
        rw [neg_add_cancel_left, abs_neg] at ht
        linarith only [hx, hu', hv', ht]
      rw [nyquistWideBump_zero_of_one_le_abs (u + x) hv, mul_zero]

/-- The actual signed witness has twice the bump mass and a negative correlation at lag four. -/
theorem nyquistZeroMeanWitness_mass_and_lag :
    autocorr nyquistZeroMeanWitness 0 = 2 * autocorr (nyquistWideBump : ℝ → ℝ) 0 ∧
      autocorr nyquistZeroMeanWitness 4 = -autocorr (nyquistWideBump : ℝ → ℝ) 0 := by
  exact autocorr_shiftedCopyDifference_at_zero_and_shift
    nyquistWideBump.hasCompactSupport nyquistWideBump.continuous
    (nyquistWideBump_autocorr_zero_of_two_le_abs (by norm_num : (2 : ℝ) ≤ |4|))
    (nyquistWideBump_autocorr_zero_of_two_le_abs (by norm_num : (2 : ℝ) ≤ |2 * 4|))

/-- Signed cancellation is realized by an actual smooth source with a negative normalized lag. -/
theorem nyquistZeroMeanWitness_normalized_at_four :
    nyquistNormalizedCorrelation nyquistZeroMeanWitness 4 = -(1 / 2 : ℝ) := by
  change autocorr nyquistZeroMeanWitness 4 / autocorr nyquistZeroMeanWitness 0 = _
  rw [nyquistZeroMeanWitness_mass_and_lag.1, nyquistZeroMeanWitness_mass_and_lag.2]
  field_simp [nyquistWideBump_mass_pos.ne']

/-- Dilation transports the negative normalized correlation to lag `4L`. -/
theorem nyquistZeroMeanWitness_broad_normalized_at_four_mul {L : ℝ} (hL : 0 < L) :
    autocorr (sourceRescale nyquistZeroMeanWitness L⁻¹) (4 * L) /
      autocorr (sourceRescale nyquistZeroMeanWitness L⁻¹) 0 = -(1 / 2 : ℝ) := by
  rw [normalized_sourceRescale_eq_nyquistNormalizedCorrelation
    nyquistZeroMeanWitness nyquistZeroMeanWitness_ne_zero hL,
    mul_div_cancel_right₀ 4 hL.ne', nyquistZeroMeanWitness_normalized_at_four]

/-- Two fixed smooth sources realize both mean alternatives while their normalized energies vanish. -/
theorem nyquistCritical_fixedSource_mean_dichotomy (m : ℕ) :
    (Tendsto (nyquistCriticalSourceResidual m nyquistPositiveMeanWitness) atTop atTop ∧
      Tendsto (fun L : ℝ => normalizedArchEnergy (sourceRescale nyquistPositiveMeanWitness L⁻¹))
        atTop (𝓝 0)) ∧
    (Tendsto (nyquistCriticalSourceResidual m nyquistZeroMeanWitness) atTop
        (𝓝 (nyquistCriticalFinitePart m)) ∧
      Tendsto (fun L : ℝ => normalizedArchEnergy (sourceRescale nyquistZeroMeanWitness L⁻¹))
        atTop (𝓝 0) ∧
      nyquistNormalizedCorrelation nyquistZeroMeanWitness 4 = -(1 / 2 : ℝ)) := by
  have hp : ContDiff ℝ 2 (nyquistPositiveMeanWitness : ℝ → ℝ) :=
    contDiff_nyquistPositiveMeanWitness 2
  have hg : ContDiff ℝ 2 (nyquistZeroMeanWitness : ℝ → ℝ) :=
    contDiff_nyquistZeroMeanWitness 2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, nyquistZeroMeanWitness_normalized_at_four⟩⟩
  · exact tendsto_nyquistCriticalSourceResidual_atTop_of_mean_ne_zero m nyquistPositiveMeanWitness hp
      nyquistPositiveMeanWitness_ne_zero nyquistPositiveMeanWitness_integral_pos.ne'
  · exact tendsto_normalizedArchEnergy_broadSource nyquistPositiveMeanWitness hp
      nyquistPositiveMeanWitness_ne_zero
  · exact tendsto_nyquistCriticalSourceResidual_of_mean_zero m nyquistZeroMeanWitness hg
      nyquistZeroMeanWitness_ne_zero nyquistZeroMeanWitness_integral_and_autocorr_mass_eq_zero.1
  · exact tendsto_normalizedArchEnergy_broadSource nyquistZeroMeanWitness hg nyquistZeroMeanWitness_ne_zero

end GaloisForLFunctions.BiScaleUncertainty
