import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielDualBudget
import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielDualPower

open Complex Filter Set Topology

namespace RHTower.Sieve

noncomputable section

/-- Analytic complex power carrying a dual datum through the moving Gabriel strip. -/
def inghamUniformGabrielDualPower (sigma : ℝ) (w z : ℂ) : ℂ :=
  if w = 0 then 0 else
    w / (‖w‖ : ℂ) * Complex.exp
      (inghamUniformGabrielDualExponent sigma z * (Real.log ‖w‖ : ℂ))

theorem analyticAt_inghamUniformGabrielDualPower
    (sigma : ℝ) (w z : ℂ) :
    AnalyticAt ℂ (inghamUniformGabrielDualPower sigma w) z := by
  by_cases hw : w = 0
  · subst w
    rw [show inghamUniformGabrielDualPower sigma 0 = fun _ => 0 by
      funext u
      simp [inghamUniformGabrielDualPower]]
    exact analyticAt_const
  · rw [show inghamUniformGabrielDualPower sigma w = fun u =>
        w / (‖w‖ : ℂ) * Complex.exp
          (inghamUniformGabrielDualExponent sigma u * (Real.log ‖w‖ : ℂ)) by
      funext u
      simp [inghamUniformGabrielDualPower, hw]]
    exact analyticAt_const.mul
      (((analyticAt_id.add analyticAt_const).div_const).mul analyticAt_const).cexp

@[simp] theorem inghamUniformGabrielDualPower_center
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (w : ℂ) :
    inghamUniformGabrielDualPower sigma w
        (inghamUniformGabrielCenter sigma : ℂ) = w := by
  by_cases hw : w = 0
  · simp [inghamUniformGabrielDualPower, hw]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamUniformGabrielDualPower, if_neg hw,
      inghamUniformGabrielDualExponent_center hsigma0, one_mul]
    rw [← Complex.ofReal_exp, Real.exp_log hn]
    field_simp [Complex.ofReal_ne_zero.mpr hn.ne']

theorem norm_inghamUniformGabrielDualPower
    {sigma : ℝ} {w z : ℂ} (hw : w ≠ 0) :
    ‖inghamUniformGabrielDualPower sigma w z‖ =
      ‖w‖ ^ (inghamUniformGabrielDualExponent sigma z).re := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [inghamUniformGabrielDualPower, if_neg hw, norm_mul, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w), Complex.norm_exp,
    Real.rpow_def_of_pos hn]
  rw [div_self hn.ne']
  simp only [one_mul, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

theorem norm_inghamUniformGabrielDualPower_left
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ) (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielDualPower sigma w z‖ =
      ‖w‖ ^ ((inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma) := by
  have hexp : 0 < (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielSeedDenominator sigma := by
    apply div_pos
    · unfold inghamUniformGabrielRightEdge
      nlinarith
    · exact uniformGabrielSeedDenominator_pos hsigma0
  by_cases hw : w = 0
  · subst w
    rw [inghamUniformGabrielDualPower, if_pos rfl, norm_zero]
    exact (Real.zero_rpow hexp.ne').symm
  · rw [norm_inghamUniformGabrielDualPower hw,
      inghamUniformGabrielDualExponent_re_left hz]

theorem norm_inghamUniformGabrielDualPower_right
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ)
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielDualPower sigma w z‖ =
      ‖w‖ ^ (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma) := by
  have hexp : 0 < 2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielSeedDenominator sigma := by
    apply div_pos
    · unfold inghamUniformGabrielRightEdge
      nlinarith
    · exact uniformGabrielSeedDenominator_pos hsigma0
  by_cases hw : w = 0
  · subst w
    rw [inghamUniformGabrielDualPower, if_pos rfl, norm_zero]
    exact (Real.zero_rpow hexp.ne').symm
  · rw [norm_inghamUniformGabrielDualPower hw,
      inghamUniformGabrielDualExponent_re_right hz]

/-- Dual datum selected from a center-line value. -/
def inghamUniformGabrielDualSeed (sigma : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else
    starRingEnd ℂ w / (‖w‖ : ℂ) *
      (↑(‖w‖ ^ inghamUniformGabrielSeedExponent sigma) : ℂ)

@[simp] theorem norm_inghamUniformGabrielDualSeed
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) (w : ℂ) :
    ‖inghamUniformGabrielDualSeed sigma w‖ =
      ‖w‖ ^ inghamUniformGabrielSeedExponent sigma := by
  have hexp := inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1
  by_cases hw : w = 0
  · subst w
    simp [inghamUniformGabrielDualSeed, Real.zero_rpow hexp.ne']
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamUniformGabrielDualSeed, if_neg hw, norm_mul, norm_div,
      Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w),
      Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _), div_self hn.ne', one_mul]

@[simp] theorem mul_inghamUniformGabrielDualSeed
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) (w : ℂ) :
    w * inghamUniformGabrielDualSeed sigma w =
      (↑(‖w‖ ^ inghamUniformGabrielInteriorPower sigma) : ℂ) := by
  by_cases hw : w = 0
  · subst w
    have hp : 0 < inghamUniformGabrielInteriorPower sigma := by
      rw [inghamUniformGabrielInteriorPower_eq_one_add_seedExponent hsigma1]
      have : 0 < inghamUniformGabrielSeedExponent sigma :=
        inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1
      linarith
    simp [inghamUniformGabrielDualSeed, Real.zero_rpow hp.ne']
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamUniformGabrielDualSeed, if_neg hw]
    have hphase : w * (starRingEnd ℂ w / (‖w‖ : ℂ)) = (‖w‖ : ℂ) := by
      rw [div_eq_mul_inv, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp [Complex.ofReal_ne_zero.mpr hn.ne']
      norm_num
    rw [← mul_assoc, hphase, ← Complex.ofReal_mul]
    norm_cast
    calc
      ‖w‖ * ‖w‖ ^ inghamUniformGabrielSeedExponent sigma =
          ‖w‖ ^ (1 : ℝ) * ‖w‖ ^ inghamUniformGabrielSeedExponent sigma := by
            rw [Real.rpow_one]
      _ = ‖w‖ ^ ((1 : ℝ) + inghamUniformGabrielSeedExponent sigma) :=
        (Real.rpow_add hn _ _).symm
      _ = ‖w‖ ^ inghamUniformGabrielInteriorPower sigma := by
        rw [inghamUniformGabrielInteriorPower_eq_one_add_seedExponent hsigma1]

theorem norm_inghamUniformGabrielDualPower_seed_left_pow_four
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ) (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma w) z‖ ^ 4 =
      ‖w‖ ^ inghamUniformGabrielInteriorPower sigma := by
  rw [norm_inghamUniformGabrielDualPower_left hsigma0 hsigma1 _ _ hz,
    norm_inghamUniformGabrielDualSeed hsigma0 hsigma1]
  rw [← Real.rpow_mul (norm_nonneg w)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg w)]
  congr 1
  convert inghamUniformGabriel_seed_left_identity hsigma0 hsigma1 using 1
  all_goals ring

theorem norm_inghamUniformGabrielDualPower_seed_right_pow_two
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ) (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma w) z‖ ^ 2 =
      ‖w‖ ^ inghamUniformGabrielInteriorPower sigma := by
  rw [norm_inghamUniformGabrielDualPower_right hsigma0 hsigma1 _ _ hz,
    norm_inghamUniformGabrielDualSeed hsigma0 hsigma1]
  rw [← Real.rpow_mul (norm_nonneg w)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg w)]
  congr 1
  convert inghamUniformGabriel_seed_right_identity hsigma0 hsigma1 using 1
  all_goals ring

theorem inghamUniformGabrielDualExponent_re_pos
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    0 < (inghamUniformGabrielDualExponent sigma z).re := by
  rw [inghamUniformGabrielDualExponent_re]
  apply div_pos
  · unfold inghamUniformGabrielRightEdge
    nlinarith
  · exact uniformGabrielSeedDenominator_pos hsigma0

theorem norm_inghamUniformGabrielDualPower_of_pos_re
    (sigma : ℝ) (z w : ℂ)
    (hz : 0 < (inghamUniformGabrielDualExponent sigma z).re) :
    ‖inghamUniformGabrielDualPower sigma w z‖ =
      ‖w‖ ^ (inghamUniformGabrielDualExponent sigma z).re := by
  by_cases hw : w = 0
  · subst w
    rw [show inghamUniformGabrielDualPower sigma 0 z = 0 by
      simp [inghamUniformGabrielDualPower]]
    simp only [norm_zero]
    exact (Real.zero_rpow hz.ne').symm
  · exact norm_inghamUniformGabrielDualPower hw

/-- Moving center dual seed remains continuous across its phase singularity. -/
theorem continuous_inghamUniformGabrielDualSeed
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    Continuous (inghamUniformGabrielDualSeed sigma) := by
  have hexp := inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamUniformGabrielDualSeed sigma 0 = 0 by
      simp [inghamUniformGabrielDualSeed], tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun z : ℂ => ‖inghamUniformGabrielDualSeed sigma z‖) =
        fun z : ℂ => ‖z‖ ^ inghamUniformGabrielSeedExponent sigma by
      funext z
      exact norm_inghamUniformGabrielDualSeed hsigma0 hsigma1 z]
    have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) :=
      by simpa using
        (((continuous_norm : Continuous fun z : ℂ => ‖z‖).continuousAt :
          ContinuousAt (fun z : ℂ => ‖z‖) (0 : ℂ)).tendsto)
    simpa [Function.comp_def, Real.zero_rpow hexp.ne'] using
      (Real.continuous_rpow_const hexp.le).continuousAt.tendsto.comp hnorm
  · have hev : ∀ᶠ z : ℂ in 𝓝 w, z ≠ 0 := eventually_ne_nhds hw
    have hcand : ContinuousAt (fun z : ℂ => starRingEnd ℂ z / (‖z‖ : ℂ) *
        (↑(‖z‖ ^ inghamUniformGabrielSeedExponent sigma) : ℂ)) w := by
      have hstar : ContinuousAt (fun z : ℂ => star z) w :=
        (continuous_star : Continuous fun z : ℂ => star z).continuousAt
      have hnormR : ContinuousAt (fun z : ℂ => ‖z‖) w :=
        (continuous_norm : Continuous fun z : ℂ => ‖z‖).continuousAt
      have hnormC : ContinuousAt (fun z : ℂ => (‖z‖ : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp hnormR
      have hdiv := hstar.div hnormC
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
      have hrpowR : ContinuousAt
          (fun z : ℂ => ‖z‖ ^ inghamUniformGabrielSeedExponent sigma) w :=
        (Real.continuous_rpow_const hexp.le).continuousAt.comp hnormR
      have hrpowC : ContinuousAt
          (fun z : ℂ => (↑(‖z‖ ^ inghamUniformGabrielSeedExponent sigma) : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp hrpowR
      exact hdiv.mul hrpowC
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with z hz
    simp [inghamUniformGabrielDualSeed, hz]

theorem continuous_inghamUniformGabrielDualPower_const
    (sigma : ℝ) (z : ℂ)
    (hz : 0 < (inghamUniformGabrielDualExponent sigma z).re) :
    Continuous fun w : ℂ => inghamUniformGabrielDualPower sigma w z := by
  have hz' : 0 < (z.re + (inghamUniformGabrielRightEdge sigma - 1)) /
      uniformGabrielSeedDenominator sigma := by simpa using hz
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamUniformGabrielDualPower sigma 0 z = 0 by
      simp [inghamUniformGabrielDualPower], tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun u : ℂ => ‖inghamUniformGabrielDualPower sigma u z‖) =
        fun u : ℂ => ‖u‖ ^ (inghamUniformGabrielDualExponent sigma z).re by
      funext u
      exact norm_inghamUniformGabrielDualPower_of_pos_re sigma z u hz]
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
        (inghamUniformGabrielDualExponent sigma z * (Real.log ‖u‖ : ℂ))) w :=
      Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hlogC)
    have hcand : ContinuousAt (fun u : ℂ => u / (‖u‖ : ℂ) * Complex.exp
        (inghamUniformGabrielDualExponent sigma z * (Real.log ‖u‖ : ℂ))) w :=
      hphase.mul hexp
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with u hu
    simp [inghamUniformGabrielDualPower, hu]

theorem continuousAt_inghamUniformGabrielDualPower_pair
    {sigma : ℝ} {w z : ℂ}
    (hz : 0 < (inghamUniformGabrielDualExponent sigma z).re) :
    ContinuousAt
      (fun p : ℂ × ℂ => inghamUniformGabrielDualPower sigma p.1 p.2) (w, z) := by
  have hz' : 0 < (z.re + (inghamUniformGabrielRightEdge sigma - 1)) /
      uniformGabrielSeedDenominator sigma := by simpa using hz
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamUniformGabrielDualPower sigma 0 z = 0 by
      simp [inghamUniformGabrielDualPower], tendsto_zero_iff_norm_tendsto_zero]
    have hqcont : Continuous fun u : ℂ =>
        (inghamUniformGabrielDualExponent sigma u).re := by
      unfold inghamUniformGabrielDualExponent
      fun_prop
    have hpow : Tendsto
        (fun p : ℂ × ℂ => ‖p.1‖ ^ (inghamUniformGabrielDualExponent sigma p.2).re)
        (𝓝 ((0 : ℂ), z)) (𝓝 0) := by
      simpa only [Function.comp_apply, norm_zero,
        inghamUniformGabrielDualExponent_re, Real.zero_rpow hz'.ne'] using
        (continuous_fst.norm.tendsto ((0 : ℂ), z)).rpow
          ((hqcont.comp continuous_snd).tendsto ((0 : ℂ), z)) (Or.inr hz)
    have hpos : ∀ᶠ p : ℂ × ℂ in 𝓝 ((0 : ℂ), z),
        0 < (inghamUniformGabrielDualExponent sigma p.2).re :=
      ((hqcont.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds hz))
    apply hpow.congr'
    filter_upwards [hpos] with p hp
    exact (norm_inghamUniformGabrielDualPower_of_pos_re sigma p.2 p.1 hp).symm
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
        (fun p : ℂ × ℂ => inghamUniformGabrielDualExponent sigma p.2) (w, z) := by
      unfold inghamUniformGabrielDualExponent
      fun_prop
    have hcand : ContinuousAt (fun p : ℂ × ℂ =>
        p.1 / (‖p.1‖ : ℂ) * Complex.exp
          (inghamUniformGabrielDualExponent sigma p.2 * (Real.log ‖p.1‖ : ℂ))) (w, z) :=
      hphase.mul (Complex.continuous_exp.continuousAt.comp (hq.mul hlogC))
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with p hp
    simp [inghamUniformGabrielDualPower, hp]

theorem continuousOn_inghamUniformGabrielDualPower_pair (sigma : ℝ) :
    ContinuousOn
      (fun p : ℂ × ℂ => inghamUniformGabrielDualPower sigma p.1 p.2)
      {p | 0 < (inghamUniformGabrielDualExponent sigma p.2).re} := by
  intro p hp
  exact (continuousAt_inghamUniformGabrielDualPower_pair hp).continuousWithinAt

end

end RHTower.Sieve
