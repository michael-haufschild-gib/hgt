import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixMomentNeutralIndexAmplification
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniFluxPolarization

/-!
# Gamma-six conditioning Lyapunov exponent and theta boundary flux

The coefficient-faithful Gamma-six block is similar to its critical Hermitian block through a
positive diagonal gauge.  This file retains the datum discarded by that Hermitianization: the
absolute logarithmic distortion of the gauge.  On shell `m` it is exactly

`m * log 6 * |delta|`.

The same number is the absolute inverse-Cayley rapidity of the fixed-frame reflection idempotent.
After specialization to an actual multiplicity-labelled Xi divisor, its normalized value is
exactly the absolute Hedenmalm theta boundary flux divided by the strictly positive theta
mass-energy.  Thus Gamma-six trace amplification, Route-P/R fixed-frame non-self-adjointness, and
the genuine compact-source boundary current are not merely zero-set equivalent: they have one
common coefficient-faithful Lyapunov exponent.

All statements are unconditional.  The global vanishing statement is proved equivalent to RH;
no source bound or vanishing premise is asserted.
-/

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Absolute logarithmic distortion of the diagonal gauge which Hermitianizes one Gamma-six
shell block.  This is the logarithm of its diagonal condition ratio. -/
def deningerGammaSixBalancingLogDistortion (delta : ℝ) (m : ℕ) : ℝ :=
  |Real.log ((((1 / 6 : ℝ) ^ m) ^ delta))|

private theorem log_one_div_six : Real.log (1 / 6 : ℝ) = -Real.log 6 := by
  rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num, Real.log_inv]

/-- Exact shell law: logarithmic nonunitary distortion grows linearly in shell depth, with slope
`log 6 * |delta|`. -/
theorem deningerGammaSixBalancingLogDistortion_eq
    (delta : ℝ) (m : ℕ) :
    deningerGammaSixBalancingLogDistortion delta m =
      (m : ℝ) * Real.log 6 * |delta| := by
  rw [deningerGammaSixBalancingLogDistortion,
    Real.log_rpow (by positivity : 0 < (1 / 6 : ℝ) ^ m),
    Real.log_pow, log_one_div_six]
  have hmabs : |(m : ℝ)| = (m : ℝ) := abs_of_nonneg (Nat.cast_nonneg m)
  have hlogabs : |Real.log 6| = Real.log 6 :=
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 6))
  rw [abs_mul, abs_mul, hmabs, abs_neg, hlogabs]
  ring

/-- Unnormalized two-orientation shell mass is exactly five times the exponential of the
Hermitianizing gauge distortion.  Trace amplification and non-normal conditioning are therefore
the same quantitative invariant, not two independent RH receivers. -/
theorem deningerGammaSixTwoOrientationShellTraceMass_eq_five_mul_exp_distortion
    {m : ℕ} (hm : 3 ≤ m) (delta : ℝ) :
    deningerGammaSixTwoOrientationShellTraceMass delta m =
      5 * Real.exp (deningerGammaSixBalancingLogDistortion delta m) := by
  rw [deningerGammaSixTwoOrientationShellTraceMass,
    deningerGammaSixForwardShellTraceMass_eq hm,
    deningerGammaSixReflectedShellTraceMass_eq hm]
  have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmono : Monotone (fun x : ℝ => (6 : ℝ) ^ x) :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 6)).monotone
  by_cases hdelta : 0 ≤ delta
  · have hexponents : -(m : ℝ) * delta ≤ (m : ℝ) * delta := by
      nlinarith
    have hpowers : (6 : ℝ) ^ (-(m : ℝ) * delta) ≤
        (6 : ℝ) ^ ((m : ℝ) * delta) := hmono hexponents
    rw [max_eq_left (mul_le_mul_of_nonneg_left hpowers (by norm_num)),
      deningerGammaSixBalancingLogDistortion_eq, abs_of_nonneg hdelta,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
    congr 2
    ring
  · have hdeltaNeg : delta < 0 := lt_of_not_ge hdelta
    have hexponents : (m : ℝ) * delta ≤ -(m : ℝ) * delta := by
      nlinarith
    have hpowers : (6 : ℝ) ^ ((m : ℝ) * delta) ≤
        (6 : ℝ) ^ (-(m : ℝ) * delta) := hmono hexponents
    rw [max_eq_right (mul_le_mul_of_nonneg_left hpowers (by norm_num)),
      deningerGammaSixBalancingLogDistortion_eq,
      abs_of_neg hdeltaNeg,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
    congr 2
    ring

/-- Shell-normalized logarithmic distortion is independent of shell and recovers the complete
horizontal magnitude. -/
theorem deningerGammaSixBalancingLogDistortion_normalized_eq
    (delta : ℝ) {m : ℕ} (hm : 0 < m) :
    deningerGammaSixBalancingLogDistortion delta m /
        ((m : ℝ) * Real.log 6) =
      |delta| := by
  rw [deningerGammaSixBalancingLogDistortion_eq]
  have hm0 : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hlog0 : Real.log 6 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 6)).ne'
  field_simp [hm0, hlog0]

/-- The same distortion is the absolute inverse-Cayley rapidity.  Combined with the existing
`sourceHorizontalGammaSixFixedMetricSkewRatio_eq_tanh`, this identifies it with fixed-frame
non-self-adjointness without importing that larger transitive module here. -/
theorem deningerGammaSixBalancingLogDistortion_eq_abs_artanh_tanh_rapidity
    (delta : ℝ) (m : ℕ) :
    deningerGammaSixBalancingLogDistortion delta m =
      |Real.artanh (Real.tanh ((m : ℝ) * Real.log 6 * delta))| := by
  rw [Real.artanh_tanh, deningerGammaSixBalancingLogDistortion_eq]
  have hmabs : |(m : ℝ)| = (m : ℝ) := abs_of_nonneg (Nat.cast_nonneg m)
  have hlogabs : |Real.log 6| = Real.log 6 :=
    abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 6))
  rw [abs_mul, abs_mul, hmabs, hlogabs]

/-- On an actual Xi divisor copy, the normalized Gamma-six condition exponent is the absolute
genuine theta boundary flux divided by its strictly positive mass-energy calibration. -/
theorem deningerXiGammaSixBalancingLogDistortion_normalized_eq_thetaFlux
    (q : XiZeroCopy) {m : ℕ} (hm : 0 < m) :
    deningerGammaSixBalancingLogDistortion
          (primeDepthBVWoldXiCenteredRate q.1) m /
        ((m : ℝ) * Real.log 6) =
      |thetaXiRankTwoBoundaryFlux q| /
        (thetaSource.mass * thetaXiRootEnergy q) := by
  have hscalePos : 0 < thetaSource.mass * thetaXiRootEnergy q :=
    mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)
  have hscale : thetaSource.mass * thetaXiRootEnergy q ≠ 0 :=
    hscalePos.ne'
  calc
    deningerGammaSixBalancingLogDistortion
          (primeDepthBVWoldXiCenteredRate q.1) m /
        ((m : ℝ) * Real.log 6) =
        |primeDepthBVWoldXiCenteredRate q.1| :=
      deningerGammaSixBalancingLogDistortion_normalized_eq _ hm
    _ = |thetaXiRankTwoBoundaryFlux q| /
        (thetaSource.mass * thetaXiRootEnergy q) := by
      rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate,
        abs_mul, abs_neg, abs_of_pos hscalePos]
      exact (mul_div_cancel_left₀ _ hscale).symm

/-- Positive-shell gauge distortion vanishes exactly when the actual compact theta-root boundary
current vanishes. -/
theorem deningerXiGammaSixBalancingLogDistortion_eq_zero_iff_thetaFlux_eq_zero
    (q : XiZeroCopy) {m : ℕ} (hm : 0 < m) :
    deningerGammaSixBalancingLogDistortion
        (primeDepthBVWoldXiCenteredRate q.1) m = 0 ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [deningerGammaSixBalancingLogDistortion_eq]
  have hm0 : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hlog0 : Real.log 6 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 6)).ne'
  have hden : (m : ℝ) * Real.log 6 ≠ 0 := mul_ne_zero hm0 hlog0
  rw [mul_eq_zero, or_iff_right hden, abs_eq_zero]
  constructor
  · intro hrate
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate, hrate,
      mul_zero]
  · intro hflux
    have hscale : -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate] at hflux
    exact (mul_eq_zero.mp hflux).resolve_left hscale

/-- Fixed-shell vanishing of the coefficient-faithful conditioning exponent on every Xi
multiplicity copy. -/
def DeningerXiGammaSixAllBalancingLogDistortionsVanish (m : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    deningerGammaSixBalancingLogDistortion
      (primeDepthBVWoldXiCenteredRate q.1) m = 0

/-- **Frankenstein endpoint.**  At any positive shell, global vanishing of the Gamma-six
conditioning Lyapunov exponent is exactly RH.  Via the preceding coefficient identity this is the
same pointwise statement as annihilation of every genuine theta boundary current, not a new
assumption. -/
theorem deningerXiGammaSixAllBalancingLogDistortionsVanish_iff_riemannHypothesis
    {m : ℕ} (hm : 0 < m) :
    DeningerXiGammaSixAllBalancingLogDistortionsVanish m ↔ RiemannHypothesis := by
  rw [← all_thetaXiRankTwoBoundaryFlux_eq_zero_iff_riemannHypothesis]
  constructor
  · intro h q
    exact
      (deningerXiGammaSixBalancingLogDistortion_eq_zero_iff_thetaFlux_eq_zero q hm).1
        (h q)
  · intro h q
    exact
      (deningerXiGammaSixBalancingLogDistortion_eq_zero_iff_thetaFlux_eq_zero q hm).2
        (h q)

end

end RHTower
