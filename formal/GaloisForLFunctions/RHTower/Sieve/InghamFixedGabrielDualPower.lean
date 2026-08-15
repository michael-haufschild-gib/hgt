import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielScalarCore

open Complex Filter Set Topology

namespace RHTower.Sieve

noncomputable section

/-- Affine dual exponent for the fixed `4/3 -> 2` Gabriel interpolation. -/
def inghamFixedGabrielDualExponent (z : ℂ) : ℂ :=
  (1 + 180 * z) / 127

@[simp] theorem inghamFixedGabrielDualExponent_re (z : ℂ) :
    (inghamFixedGabrielDualExponent z).re = (1 + 180 * z.re) / 127 := by
  simp [inghamFixedGabrielDualExponent]

@[simp] theorem inghamFixedGabrielDualExponent_center :
    inghamFixedGabrielDualExponent (inghamFixedGabrielSigma : ℂ) = 1 := by
  norm_num [inghamFixedGabrielDualExponent, inghamFixedGabrielSigma]

theorem inghamFixedGabrielDualExponent_re_left {z : ℂ} (hz : z.re = 1 / 2) :
    (inghamFixedGabrielDualExponent z).re = 91 / 127 := by
  rw [inghamFixedGabrielDualExponent_re, hz]
  norm_num

theorem inghamFixedGabrielDualExponent_re_right {z : ℂ}
    (hz : z.re = inghamPowerSavingRightEdge) :
    (inghamFixedGabrielDualExponent z).re = 182 / 127 := by
  rw [inghamFixedGabrielDualExponent_re, hz]
  norm_num [inghamPowerSavingRightEdge]

/-- Analytic complex power carrying a fixed dual datum through the Gabriel strip. -/
def inghamFixedGabrielDualPower (w z : ℂ) : ℂ :=
  if w = 0 then 0 else
    w / (‖w‖ : ℂ) * Complex.exp
      (inghamFixedGabrielDualExponent z * (Real.log ‖w‖ : ℂ))

theorem analyticAt_inghamFixedGabrielDualPower (w z : ℂ) :
    AnalyticAt ℂ (inghamFixedGabrielDualPower w) z := by
  by_cases hw : w = 0
  · subst w
    rw [show inghamFixedGabrielDualPower 0 = fun _ => 0 by
      funext u
      simp [inghamFixedGabrielDualPower]]
    exact analyticAt_const
  · rw [show inghamFixedGabrielDualPower w = fun u =>
        w / (‖w‖ : ℂ) * Complex.exp
          (inghamFixedGabrielDualExponent u * (Real.log ‖w‖ : ℂ)) by
      funext u
      simp [inghamFixedGabrielDualPower, hw]]
    exact analyticAt_const.mul
      (((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).div_const).mul
        analyticAt_const).cexp

@[simp] theorem inghamFixedGabrielDualPower_center (w : ℂ) :
    inghamFixedGabrielDualPower w (inghamFixedGabrielSigma : ℂ) = w := by
  by_cases hw : w = 0
  · simp [inghamFixedGabrielDualPower, hw]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamFixedGabrielDualPower, if_neg hw,
      inghamFixedGabrielDualExponent_center, one_mul]
    rw [← Complex.ofReal_exp, Real.exp_log hn]
    field_simp [Complex.ofReal_ne_zero.mpr hn.ne']

theorem norm_inghamFixedGabrielDualPower {w z : ℂ} (hw : w ≠ 0) :
    ‖inghamFixedGabrielDualPower w z‖ =
      ‖w‖ ^ (inghamFixedGabrielDualExponent z).re := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [inghamFixedGabrielDualPower, if_neg hw, norm_mul, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w), Complex.norm_exp,
    Real.rpow_def_of_pos hn]
  rw [div_self hn.ne']
  simp only [one_mul, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

theorem norm_inghamFixedGabrielDualPower_left (w z : ℂ) (hz : z.re = 1 / 2) :
    ‖inghamFixedGabrielDualPower w z‖ = ‖w‖ ^ (91 / 127 : ℝ) := by
  by_cases hw : w = 0
  · subst w
    simp [inghamFixedGabrielDualPower]
  · rw [norm_inghamFixedGabrielDualPower hw,
      inghamFixedGabrielDualExponent_re_left hz]

theorem norm_inghamFixedGabrielDualPower_right (w z : ℂ)
    (hz : z.re = inghamPowerSavingRightEdge) :
    ‖inghamFixedGabrielDualPower w z‖ = ‖w‖ ^ (182 / 127 : ℝ) := by
  by_cases hw : w = 0
  · subst w
    simp [inghamFixedGabrielDualPower]
  · rw [norm_inghamFixedGabrielDualPower hw,
      inghamFixedGabrielDualExponent_re_right hz]

/-- Dual datum selected from a center-line value. Its phase makes the center scalar product
positive, while its norm has the conjugate-power exponent `127/237`. -/
def inghamFixedGabrielDualSeed (w : ℂ) : ℂ :=
  if w = 0 then 0 else
    starRingEnd ℂ w / (‖w‖ : ℂ) * (↑(‖w‖ ^ (127 / 237 : ℝ)) : ℂ)

@[simp] theorem norm_inghamFixedGabrielDualSeed (w : ℂ) :
    ‖inghamFixedGabrielDualSeed w‖ = ‖w‖ ^ (127 / 237 : ℝ) := by
  by_cases hw : w = 0
  · subst w
    simp [inghamFixedGabrielDualSeed]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamFixedGabrielDualSeed, if_neg hw, norm_mul, norm_div,
      Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w),
      Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _), div_self hn.ne', one_mul]

@[simp] theorem mul_inghamFixedGabrielDualSeed (w : ℂ) :
    w * inghamFixedGabrielDualSeed w = (↑(‖w‖ ^ (364 / 237 : ℝ)) : ℂ) := by
  by_cases hw : w = 0
  · subst w
    simp [inghamFixedGabrielDualSeed]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamFixedGabrielDualSeed, if_neg hw]
    have hphase : w * (starRingEnd ℂ w / (‖w‖ : ℂ)) = (‖w‖ : ℂ) := by
      rw [div_eq_mul_inv, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp [Complex.ofReal_ne_zero.mpr hn.ne']
      norm_num
    rw [← mul_assoc, hphase, ← Complex.ofReal_mul]
    norm_cast
    calc
      ‖w‖ * ‖w‖ ^ (127 / 237 : ℝ) =
          ‖w‖ ^ (1 : ℝ) * ‖w‖ ^ (127 / 237 : ℝ) := by rw [Real.rpow_one]
      _ = ‖w‖ ^ ((1 : ℝ) + 127 / 237) := (Real.rpow_add hn _ _).symm
      _ = ‖w‖ ^ (364 / 237 : ℝ) := by norm_num

/-- Left boundary dual fourth power is exactly the center `364/237` density. -/
theorem norm_inghamFixedGabrielDualPower_seed_left_pow_four
    (w z : ℂ) (hz : z.re = 1 / 2) :
    ‖inghamFixedGabrielDualPower (inghamFixedGabrielDualSeed w) z‖ ^ 4 =
      ‖w‖ ^ (364 / 237 : ℝ) := by
  rw [norm_inghamFixedGabrielDualPower_left _ _ hz,
    norm_inghamFixedGabrielDualSeed]
  rw [← Real.rpow_mul (norm_nonneg w)]
  rw [show (127 / 237 : ℝ) * (91 / 127) = 91 / 237 by norm_num]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg w)]
  congr 1
  norm_num

/-- Right boundary dual square is exactly the center `364/237` density. -/
theorem norm_inghamFixedGabrielDualPower_seed_right_pow_two
    (w z : ℂ) (hz : z.re = inghamPowerSavingRightEdge) :
    ‖inghamFixedGabrielDualPower (inghamFixedGabrielDualSeed w) z‖ ^ 2 =
      ‖w‖ ^ (364 / 237 : ℝ) := by
  rw [norm_inghamFixedGabrielDualPower_right _ _ hz,
    norm_inghamFixedGabrielDualSeed]
  rw [← Real.rpow_mul (norm_nonneg w)]
  rw [show (127 / 237 : ℝ) * (182 / 127) = 182 / 237 by norm_num]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg w)]
  congr 1
  norm_num

/-- The center dual seed is continuous even at its phase singularity `w=0`. -/
theorem continuous_inghamFixedGabrielDualSeed :
    Continuous inghamFixedGabrielDualSeed := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamFixedGabrielDualSeed 0 = 0 by
      simp [inghamFixedGabrielDualSeed], tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun z : ℂ => ‖inghamFixedGabrielDualSeed z‖) =
        fun z : ℂ => ‖z‖ ^ (127 / 237 : ℝ) by
      funext z
      exact norm_inghamFixedGabrielDualSeed z]
    have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) :=
      by simpa using
        (((continuous_norm : Continuous fun z : ℂ => ‖z‖).continuousAt :
          ContinuousAt (fun z : ℂ => ‖z‖) (0 : ℂ)).tendsto)
    simpa [Function.comp_def, Real.zero_rpow (by norm_num : (127 / 237 : ℝ) ≠ 0)] using
      (Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ 127 / 237)).continuousAt.tendsto.comp hnorm
  · have hev : ∀ᶠ z : ℂ in 𝓝 w, z ≠ 0 := eventually_ne_nhds hw
    have hcand : ContinuousAt (fun z : ℂ => starRingEnd ℂ z / (‖z‖ : ℂ) *
        (↑(‖z‖ ^ (127 / 237 : ℝ)) : ℂ)) w := by
      have hstar : ContinuousAt (fun z : ℂ => star z) w :=
        (continuous_star : Continuous fun z : ℂ => star z).continuousAt
      have hnormR : ContinuousAt (fun z : ℂ => ‖z‖) w :=
        (continuous_norm : Continuous fun z : ℂ => ‖z‖).continuousAt
      have hnormC : ContinuousAt (fun z : ℂ => (‖z‖ : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp hnormR
      have hdiv := hstar.div hnormC
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
      have hrpowR : ContinuousAt (fun z : ℂ => ‖z‖ ^ (127 / 237 : ℝ)) w :=
        (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 127 / 237)).continuousAt.comp hnormR
      have hrpowC : ContinuousAt
          (fun z : ℂ => (↑(‖z‖ ^ (127 / 237 : ℝ)) : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp hrpowR
      exact hdiv.mul hrpowC
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with z hz
    simp [inghamFixedGabrielDualSeed, hz]

theorem norm_inghamFixedGabrielDualPower_of_pos_re
    (z w : ℂ) (hz : 0 < (inghamFixedGabrielDualExponent z).re) :
    ‖inghamFixedGabrielDualPower w z‖ =
      ‖w‖ ^ (inghamFixedGabrielDualExponent z).re := by
  have hz' : 0 < (1 + 180 * z.re) / 127 := by simpa using hz
  by_cases hw : w = 0
  · subst w
    rw [show inghamFixedGabrielDualPower 0 z = 0 by
      simp [inghamFixedGabrielDualPower]]
    simp only [norm_zero, inghamFixedGabrielDualExponent_re]
    rw [Real.zero_rpow hz'.ne']
  · exact norm_inghamFixedGabrielDualPower hw

/-- At every positive-real-exponent strip point, the dual power is continuous in its datum,
including at datum zero. -/
theorem continuous_inghamFixedGabrielDualPower_const
    (z : ℂ) (hz : 0 < (inghamFixedGabrielDualExponent z).re) :
    Continuous fun w : ℂ => inghamFixedGabrielDualPower w z := by
  have hz' : 0 < (1 + 180 * z.re) / 127 := by simpa using hz
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamFixedGabrielDualPower 0 z = 0 by
      simp [inghamFixedGabrielDualPower], tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun u : ℂ => ‖inghamFixedGabrielDualPower u z‖) =
        fun u : ℂ => ‖u‖ ^ (inghamFixedGabrielDualExponent z).re by
      funext u
      exact norm_inghamFixedGabrielDualPower_of_pos_re z u hz]
    have hnorm : Tendsto (fun u : ℂ => ‖u‖) (𝓝 0) (𝓝 0) := by
      simpa using
        (((continuous_norm : Continuous fun u : ℂ => ‖u‖).continuousAt :
          ContinuousAt (fun u : ℂ => ‖u‖) (0 : ℂ)).tendsto)
    simpa [Function.comp_def, Real.zero_rpow hz'.ne'] using
      (Real.continuous_rpow_const hz.le).continuousAt.tendsto.comp hnorm
  · have hev : ∀ᶠ u : ℂ in 𝓝 w, u ≠ 0 := eventually_ne_nhds hw
    have hnormR : ContinuousAt (fun u : ℂ => ‖u‖) w :=
      (continuous_norm : Continuous fun u : ℂ => ‖u‖).continuousAt
    have hnormC : ContinuousAt (fun u : ℂ => (‖u‖ : ℂ)) w :=
      Complex.continuous_ofReal.continuousAt.comp hnormR
    have hphase : ContinuousAt (fun u : ℂ => u / (‖u‖ : ℂ)) w :=
      continuousAt_id.div hnormC
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
    have hlogR : ContinuousAt (fun u : ℂ => Real.log ‖u‖) w :=
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hw)).comp hnormR
    have hlogC : ContinuousAt (fun u : ℂ => (Real.log ‖u‖ : ℂ)) w :=
      Complex.continuous_ofReal.continuousAt.comp hlogR
    have hexp : ContinuousAt (fun u : ℂ => Complex.exp
        (inghamFixedGabrielDualExponent z * (Real.log ‖u‖ : ℂ))) w :=
      Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hlogC)
    have hcand : ContinuousAt (fun u : ℂ => u / (‖u‖ : ℂ) * Complex.exp
        (inghamFixedGabrielDualExponent z * (Real.log ‖u‖ : ℂ))) w :=
      hphase.mul hexp
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with u hu
    simp [inghamFixedGabrielDualPower, hu]

/-- The dual power is jointly continuous in datum and strip variable wherever the affine exponent
has positive real part. This includes the datum-zero seam, where continuity follows from variable
real-power continuity rather than a phase choice. -/
theorem continuousAt_inghamFixedGabrielDualPower_pair
    {w z : ℂ} (hz : 0 < (inghamFixedGabrielDualExponent z).re) :
    ContinuousAt
      (fun p : ℂ × ℂ => inghamFixedGabrielDualPower p.1 p.2) (w, z) := by
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamFixedGabrielDualPower 0 z = 0 by
      simp [inghamFixedGabrielDualPower], tendsto_zero_iff_norm_tendsto_zero]
    have hqcont : Continuous fun u : ℂ => (inghamFixedGabrielDualExponent u).re := by
      unfold inghamFixedGabrielDualExponent
      fun_prop
    have hpow : Tendsto
        (fun p : ℂ × ℂ => ‖p.1‖ ^ (inghamFixedGabrielDualExponent p.2).re)
        (𝓝 ((0 : ℂ), z)) (𝓝 0) := by
      simpa only [Function.comp_apply, norm_zero, Real.zero_rpow hz.ne'] using
        (continuous_fst.norm.tendsto ((0 : ℂ), z)).rpow
          ((hqcont.comp continuous_snd).tendsto ((0 : ℂ), z)) (Or.inr hz)
    have hpos : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), z),
        0 < (inghamFixedGabrielDualExponent p.2).re :=
      ((hqcont.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds hz))
    apply hpow.congr'
    filter_upwards [hpos] with p hp
    exact (norm_inghamFixedGabrielDualPower_of_pos_re p.2 p.1 hp).symm
  · have hev : ∀ᶠ p : ℂ × ℂ in 𝓝 (w, z), p.1 ≠ 0 :=
      (continuous_fst.continuousAt.eventually (eventually_ne_nhds hw))
    have hnormR : ContinuousAt (fun p : ℂ × ℂ => ‖p.1‖) (w, z) :=
      continuous_fst.norm.continuousAt
    have hnormC : ContinuousAt (fun p : ℂ × ℂ => (‖p.1‖ : ℂ)) (w, z) :=
      Complex.continuous_ofReal.continuousAt.comp hnormR
    have hphase : ContinuousAt
        (fun p : ℂ × ℂ => p.1 / (‖p.1‖ : ℂ)) (w, z) :=
      continuous_fst.continuousAt.div hnormC
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
    have hlogR : ContinuousAt (fun p : ℂ × ℂ => Real.log ‖p.1‖) (w, z) :=
      ContinuousAt.comp (f := fun p : ℂ × ℂ => ‖p.1‖)
        (Real.continuousAt_log (norm_ne_zero_iff.mpr hw)) hnormR
    have hlogC : ContinuousAt
        (fun p : ℂ × ℂ => (Real.log ‖p.1‖ : ℂ)) (w, z) :=
      Complex.continuous_ofReal.continuousAt.comp hlogR
    have hq : ContinuousAt
        (fun p : ℂ × ℂ => inghamFixedGabrielDualExponent p.2) (w, z) := by
      unfold inghamFixedGabrielDualExponent
      fun_prop
    have hcand : ContinuousAt (fun p : ℂ × ℂ =>
        p.1 / (‖p.1‖ : ℂ) * Complex.exp
          (inghamFixedGabrielDualExponent p.2 * (Real.log ‖p.1‖ : ℂ))) (w, z) :=
      hphase.mul (Complex.continuous_exp.continuousAt.comp (hq.mul hlogC))
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with p hp
    simp [inghamFixedGabrielDualPower, hp]

theorem continuousOn_inghamFixedGabrielDualPower_pair :
    ContinuousOn (fun p : ℂ × ℂ => inghamFixedGabrielDualPower p.1 p.2)
      {p | 0 < (inghamFixedGabrielDualExponent p.2).re} := by
  intro p hp
  exact (continuousAt_inghamFixedGabrielDualPower_pair hp).continuousWithinAt

end

end RHTower.Sieve
