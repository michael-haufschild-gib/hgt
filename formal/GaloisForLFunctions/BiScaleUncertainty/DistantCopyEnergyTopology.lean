import GaloisForLFunctions.BiScaleUncertainty.DistantCopyCorrelationTopology

/-!
# Uniform energy convergence for arbitrary distant-copy amplitudes

The mixing coefficient is always at most one half in absolute value. The
translated-packet envelope therefore controls energy independently of amplitude.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def copyEnergyErrorBound (f : ℝ → ℝ) (D T : ℝ) : ℝ :=
  copyTailFactor D T * (∫ x, |autocorr f x|) / (2 * autocorr f 0)

theorem copyEnergyErrorBound_nonneg {f : ℝ → ℝ} (hR : 0 < autocorr f 0) (D T : ℝ) :
    0 ≤ copyEnergyErrorBound f D T :=
  div_nonneg (mul_nonneg (copyTailFactor_nonneg D T) (integral_nonneg fun x => abs_nonneg _))
    (by positivity)

theorem copyEnergyErrorBound_antitone {f : ℝ → ℝ} (hR : 0 < autocorr f 0)
    (D : ℝ) {S T : ℝ} (hST : S ≤ T) :
    copyEnergyErrorBound f D T ≤ copyEnergyErrorBound f D S := by
  have hd : 0 ≤ 1 - Real.exp (-2) :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))).le
  have he : Real.exp (-(T - D) / 2) ≤ Real.exp (-(S - D) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hw : copyTailFactor D T ≤ copyTailFactor D S :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hd
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hw (integral_nonneg fun x => abs_nonneg _)) (by positivity)

/-- Every amplitude has the same exponentially vanishing normalized energy envelope. -/
theorem normalizedArchEnergy_subtractCopy_abs_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    |normalizedArchEnergy (subtractCopy f a T) - normalizedArchEnergy f| ≤
      copyEnergyErrorBound f D T := by
  have hI := abs_integral_shifted_autocorr_arch_le hf hfc hs hT
  have hc : a / ((1 + a ^ 2) * autocorr f 0) = copyMixingCoefficient a / autocorr f 0 := by
    unfold copyMixingCoefficient
    have hd : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [hR.ne', hd]
  rw [normalizedArchEnergy_subtractCopy_sub hf hfc hR hs hT, hc,
    abs_mul, abs_div, abs_of_pos hR]
  calc
    _ ≤ ((1 / 2 : ℝ) / autocorr f 0) *
        (copyTailFactor D T * ∫ x, |autocorr f x|) :=
      mul_le_mul (div_le_div_of_nonneg_right (abs_copyMixingCoefficient_le_half a) hR.le)
        hI (abs_nonneg _) (by positivity)
    _ = _ := by unfold copyEnergyErrorBound; ring

theorem tendsto_copyEnergyErrorBound_zero (f : ℝ → ℝ) (D : ℝ) (T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => copyEnergyErrorBound f D (T n)) atTop (𝓝 0) := by
  have hz : Tendsto (fun n => -(T n - D) / 2) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [hT.eventually (eventually_ge_atTop (D - 2 * b))] with n hn
    linarith
  have he := Real.tendsto_exp_atBot.comp hz
  simpa only [copyEnergyErrorBound, copyTailFactor, Function.comp_def, mul_zero, zero_mul, zero_div]
    using (((he.const_mul 2).div_const (1 - Real.exp (-2))).mul_const
      (∫ x, |autocorr f x|)).div_const (2 * autocorr f 0)

/-- Escaping centers force energy convergence for every sequence of real amplitudes. -/
theorem tendsto_normalizedArchEnergy_subtractCopy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D : ℝ} (hs : ∀ x, D < |x| → autocorr f x = 0)
    (a T : ℕ → ℝ) (hsep : ∀ n, D + 1 ≤ T n) (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => normalizedArchEnergy (subtractCopy f (a n) (T n))) atTop
      (𝓝 (normalizedArchEnergy f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp (tendsto_copyEnergyErrorBound_zero f D T hT)).2 ε hε] with n hn
  rw [Real.dist_eq]
  exact (normalizedArchEnergy_subtractCopy_abs_le hf hfc hR hs (hsep n) (a n)).trans_lt hn

def copyEnergyCeiling (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  normalizedArchEnergy f + copyEnergyErrorBound f D (D + 1)

theorem normalizedArchEnergy_le_copyEnergyCeiling {f : ℝ → ℝ}
    (hR : 0 < autocorr f 0) (D : ℝ) : normalizedArchEnergy f ≤ copyEnergyCeiling f D := by
  have h := copyEnergyErrorBound_nonneg hR D (D + 1)
  unfold copyEnergyCeiling
  linarith

theorem copyEnergyCeiling_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) (D : ℝ) :
    0 ≤ copyEnergyCeiling f D :=
  add_nonneg (div_nonneg (biScaleLevyEnergy_nonneg hfc hf) hR.le)
    (copyEnergyErrorBound_nonneg hR D (D + 1))

/-- A single ceiling contains the seed and every sufficiently separated copy. -/
theorem normalizedArchEnergy_subtractCopy_le_copyEnergyCeiling {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D T : ℝ} (hs : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    normalizedArchEnergy (subtractCopy f a T) ≤ copyEnergyCeiling f D := by
  have he := (normalizedArchEnergy_subtractCopy_abs_le hf hfc hR hs hT a).trans
    (copyEnergyErrorBound_antitone hR D hT)
  have hl := le_abs_self (normalizedArchEnergy (subtractCopy f a T) - normalizedArchEnergy f)
  unfold copyEnergyCeiling
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
