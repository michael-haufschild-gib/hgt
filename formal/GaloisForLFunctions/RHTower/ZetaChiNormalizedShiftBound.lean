import GaloisForLFunctions.RHTower.ZetaChiConductorLogSlope
import GaloisForLFunctions.RHTower.ZetaChiSegmentLogRatio

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- The exact normalized chi logarithm has a compact-shift error tending
to zero, with both critical and transverse slope costs retained. -/
theorem norm_zetaChiSegmentLog_add_conductor_le {s : ℂ} {t : ℝ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (ht : 4 ≤ t) (him : 2 * |s.im| ≤ t) :
    ‖zetaChiSegmentLog s t +
      (s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)‖ ≤
      26 * ‖s - (1 / 2 : ℂ)‖ / t ^ 2 + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 / t := by
  let δ : ℂ := s - (1 / 2 : ℂ)
  let q : ℝ → ℂ := fun u => (1 / 2 : ℂ) + (u : ℂ) * δ
  let z : ℝ → ℂ := fun u => linePt t + (u : ℂ) * δ
  have ht0 : 0 < t := by linarith
  have hzC : Continuous z := by dsimp [z]; fun_prop
  have himz (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : 0 < (z u).im := by
    have he : (z u).im = t + u * s.im := by simp [z, δ, linePt]
    rw [he]
    nlinarith [mul_nonneg hu.1 (show 0 ≤ s.im + |s.im| by linarith [neg_abs_le s.im]),
      mul_nonneg (sub_nonneg.mpr hu.2) (abs_nonneg s.im)]
  have hlogC : ContinuousOn (fun u => logDeriv zetaChi (z u)) (Icc (0 : ℝ) 1) := by
    intro u hu
    exact ((differentiableAt_logDeriv_zetaChi (himz u hu).ne').continuousAt.comp
      hzC.continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun u => δ * logDeriv zetaChi (z u)) volume (0 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.mul hlogC)
  have hpoint (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖δ * (logDeriv zetaChi (z u) + (Real.log (t / (2 * Real.pi)) : ℂ))‖ ≤
        ‖δ‖ * ((10 / t) * ‖δ‖ + 26 / t ^ 2) := by
    have hre : (q u).re = (1 - u) / 2 + u * s.re := by
      simp [q, δ, Complex.mul_re]
      ring
    have hq0 : 0 ≤ (q u).re := by
      rw [hre]
      nlinarith [hu.2, mul_nonneg hu.1 hs0.le]
    have hq1 : (q u).re ≤ 1 := by
      rw [hre]
      nlinarith [hu.2, mul_nonneg hu.1 (sub_nonneg.mpr hs1.le)]
    have hqi : |(q u).im| ≤ |s.im| := by
      have he : (q u).im = u * s.im := by simp [q, δ]
      rw [he, abs_mul, abs_of_nonneg hu.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hu.2
    have hqnorm : ‖q u - (1 / 2 : ℂ)‖ ≤ ‖δ‖ := by
      have he : q u - (1 / 2 : ℂ) = (u : ℂ) * δ := by dsimp [q]; ring
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hu.2
    have hzz : z u = q u + (t : ℂ) * I := by dsimp [z, q, linePt]; push_cast; ring
    rw [norm_mul, hzz]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_logDeriv_zetaChi_add_log_conductor_le hq0 hq1 ht (by linarith)).trans
    exact add_le_add (mul_le_mul_of_nonneg_left hqnorm (by positivity)) le_rfl
  have heq : zetaChiSegmentLog s t + δ * (Real.log (t / (2 * Real.pi)) : ℂ) =
      ∫ u in (0 : ℝ)..1, δ * (logDeriv zetaChi (z u) +
        (Real.log (t / (2 * Real.pi)) : ℂ)) := by
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add hi intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    rfl
  change ‖zetaChiSegmentLog s t + δ * (Real.log (t / (2 * Real.pi)) : ℂ)‖ ≤ _
  rw [heq]
  have hb : ‖∫ u in (0 : ℝ)..1, δ * (logDeriv zetaChi (z u) +
      (Real.log (t / (2 * Real.pi)) : ℂ))‖ ≤
      (‖δ‖ * ((10 / t) * ‖δ‖ + 26 / t ^ 2)) * |(1 : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact hpoint u ⟨hu.1.le, hu.2⟩
  apply hb.trans_eq
  norm_num only [sub_zero, abs_one, mul_one]
  dsimp only [δ]
  ring

/-- Above an explicit compact-shift threshold, the normalized actual chi
ratio differs from one by an explicit reciprocal-height amount. -/
theorem norm_zetaChi_normalized_shift_sub_one_le {s : ℂ} {t : ℝ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (ht : 4 ≤ t) (him : 2 * |s.im| ≤ t)
    (hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ t) :
    ‖(zetaChi (s + (t : ℂ) * I) / zetaChi (linePt t)) *
        Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)) - 1‖ ≤
      (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / t := by
  let d : ℝ := ‖s - (1 / 2 : ℂ)‖
  let E : ℂ := zetaChiSegmentLog s t +
    (s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)
  have hd : 0 ≤ d := norm_nonneg _
  have ht0 : 0 < t := by linarith
  have he : ‖E‖ ≤ (26 * d + 10 * d ^ 2) / t := by
    apply (norm_zetaChiSegmentLog_add_conductor_le hs0 hs1 ht him).trans
    calc
      _ ≤ 26 * d / t + 10 * d ^ 2 / t :=
        add_le_add (div_le_div_of_nonneg_left (by positivity) ht0 (by nlinarith : t ≤ t ^ 2)) le_rfl
      _ = _ := by ring
  have he1 : ‖E‖ ≤ 1 := he.trans ((div_le_iff₀ ht0).mpr (by simpa only [one_mul] using hsize))
  rw [zetaChi_normalized_shift_eq_exp hs0 hs1]
  calc
    _ ≤ 2 * ‖E‖ := Complex.norm_exp_sub_one_le he1
    _ ≤ 2 * ((26 * d + 10 * d ^ 2) / t) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by dsimp only [d]; ring

end RHTower
