import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualContourLimit

/-!
# Uniform power decay on moving right lines

The functional-equation factor is uniformly bounded on
`1/2 ≤ Re s ≤ 1/2+d₀`.  Combining compact bounded-height control with the
explicit large-height estimate makes the power-law constant independent of
the moving displacement `d`.
-/

noncomputable section

namespace RHTower

open Complex Set MeasureTheory

theorem exists_norm_zetaChi_moving_right_line_le_rpow
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 ≤ d → d ≤ d₀ → ∀ t : ℝ,
      ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K / (max 1 |t|) ^ d := by
  let S : Set (ℝ × ℝ) := Icc 0 d₀ ×ˢ Icc (-256) 256
  let f : ℝ × ℝ → ℂ := fun p =>
    zetaChi (((1 / 2 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I)
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn f S := by
    intro p hp
    have hp1 : p.1 ≤ d₀ := hp.1.2
    have hgamma : Gammaℝ
        (1 - (((1 / 2 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp
      linarith
    have hinner : ContinuousAt (fun q : ℝ × ℝ =>
        (((1 / 2 + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I)) p := by
      fun_prop
    have hz : ContinuousAt zetaChi
        (((1 / 2 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I) :=
      (zetaChi_analyticAt hgamma).continuousAt
    have hcomp : ContinuousAt
        (zetaChi ∘ fun q : ℝ × ℝ =>
          (((1 / 2 + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I)) p :=
      ContinuousAt.comp
        (f := fun q : ℝ × ℝ =>
          (((1 / 2 + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * I))
        (g := zetaChi) hz hinner
    simpa [f, Function.comp_def] using hcomp.continuousWithinAt
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  let C₀ : ℝ := max 0 C
  let L : ℝ := Real.log Real.pi + Real.log 2 + 2
  let A₀ : ℝ := Real.exp (d₀ * L)
  let K : ℝ := max A₀ (C₀ * (256 : ℝ) ^ d₀)
  have hL : 0 < L := by
    dsimp only [L]
    have hpi : 0 < Real.log Real.pi :=
      Real.log_pos (by linarith [Real.pi_gt_three])
    have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  have hK : 0 ≤ K := hA₀.le.trans (le_max_left _ _)
  refine ⟨K, hK, fun d hd0 hdd₀ t => ?_⟩
  rw [norm_zetaChi_real_add_im_eq_abs]
  let q : ℝ := max 1 |t|
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hqpowpos : 0 < q ^ d := Real.rpow_pos_of_pos hqpos d
  change ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ ≤
    K / q ^ d
  by_cases ht : 256 ≤ |t|
  · have hbase := norm_zetaChi_le_right_line_rpow
      (σ := 1 / 2 + d) (t := |t|)
      (by linarith) (by linarith) ht
    have hmax : q = |t| := max_eq_right (by linarith)
    have hAd : Real.exp (d * L) ≤ A₀ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hdd₀ hL.le
    have hAK : Real.exp (d * L) ≤ K :=
      hAd.trans (le_max_left _ _)
    rw [hmax, div_eq_mul_inv]
    calc
      ‖zetaChi ((((1 / 2 : ℝ) + d : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖
          ≤ Real.exp (d * L) * |t| ^ (-d) := by
            simpa only [L, add_sub_cancel_left] using hbase
      _ = Real.exp (d * L) * (|t| ^ d)⁻¹ := by
            rw [Real.rpow_neg (abs_nonneg t)]
      _ ≤ K * (|t| ^ d)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hAK (by positivity)
  · have habs : |t| < 256 := lt_of_not_ge ht
    have hmem : (d, |t|) ∈ S := by
      exact ⟨⟨hd0, hdd₀⟩, ⟨by linarith [abs_nonneg t], habs.le⟩⟩
    have hcompact :
        ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ ≤ C₀ := by
      exact (hC (d, |t|) hmem).trans (le_max_right _ _)
    have hq256 : q ≤ 256 := max_le (by norm_num) habs.le
    have hqpowd₀ : q ^ d ≤ q ^ d₀ :=
      Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hdd₀
    have hqpow256 : q ^ d₀ ≤ (256 : ℝ) ^ d₀ :=
      Real.rpow_le_rpow hqpos.le hq256 hd₀0
    have hC₀0 : 0 ≤ C₀ := le_max_left _ _
    have hmul : C₀ * q ^ d ≤ C₀ * (256 : ℝ) ^ d₀ := by
      exact mul_le_mul_of_nonneg_left (hqpowd₀.trans hqpow256) hC₀0
    have hmulK : C₀ * q ^ d ≤ K :=
      hmul.trans (le_max_right _ _)
    apply (le_div_iff₀ hqpowpos).2
    exact (mul_le_mul_of_nonneg_right hcompact hqpowpos.le).trans hmulK

/-- Shifted chi-ratio estimate with one constant for every moving
displacement `0 < d ≤ d₀`. -/
theorem exists_norm_smoothAFEZetaChiShiftRatio_displaced_uniform_le
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ (τ v : ℝ),
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        K * (1 + |v|) ^ η / (max 1 |τ|) ^ (d + η) := by
  obtain ⟨Kη, hKη0, hKη⟩ :=
    exists_norm_zetaChi_fixed_right_line_le_rpow hη hηhalf
  obtain ⟨Kd, hKd0, hKd⟩ :=
    exists_norm_zetaChi_moving_right_line_le_rpow hd₀0 hd₀half
  refine ⟨Kη * Kd, mul_nonneg hKη0 hKd0, fun d hd hdd₀ τ v => ?_⟩
  have harg :
      displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I) =
        (((1 / 2 + η : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I) := by
    unfold displacedLinePt
    push_cast
    ring
  have hnum :
      ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        Kη / (max 1 |τ - v|) ^ η := by
    rw [harg]
    exact hKη (τ - v)
  have hgeom := one_div_max_one_abs_shift_rpow_le hη.le τ v
  have hnum' :
      ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        Kη * (1 + |v|) ^ η / (max 1 |τ|) ^ η := by
    calc
      ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖
          ≤ Kη / (max 1 |τ - v|) ^ η := hnum
      _ ≤ Kη * ((1 + |v|) ^ η / (max 1 |τ|) ^ η) := by
        simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hgeom hKη0
      _ = Kη * (1 + |v|) ^ η / (max 1 |τ|) ^ η := by ring
  have href :
      ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ ≤
        Kd / (max 1 |τ|) ^ d := by
    simpa only [abs_neg] using hKd d hd.le hdd₀ (-τ)
  unfold smoothAFEZetaChiShiftRatio
  rw [div_eq_mul_inv, inv_zetaChi_displacedLinePt hd
      (hdd₀.trans_lt hd₀half) τ, norm_mul]
  have hright0 : 0 ≤
      ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  calc
    ‖zetaChi (displacedLinePt d τ +
          -(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
        ‖zetaChi (((1 / 2 + d : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I)‖
      ≤ (Kη * (1 + |v|) ^ η / (max 1 |τ|) ^ η) *
          (Kd / (max 1 |τ|) ^ d) := by
        exact mul_le_mul hnum' href hright0 (by positivity)
    _ = (Kη * Kd) * (1 + |v|) ^ η /
          (max 1 |τ|) ^ (d + η) := by
      have hm : 0 < max 1 |τ| :=
        lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      rw [Real.rpow_add hm]
      have hmd : (max 1 |τ|) ^ d ≠ 0 :=
        (Real.rpow_pos_of_pos hm d).ne'
      have hmη : (max 1 |τ|) ^ η ≠ 0 :=
        (Real.rpow_pos_of_pos hm η).ne'
      field_simp [hmd, hmη]

/-- The displaced dual-weight localization constant is uniform for
`0 < d ≤ d₀`; this is the form needed when `d = R / log T`. -/
theorem exists_norm_smoothAFEZetaDisplacedDualWeight_sub_one_le_uniform_conductor
    {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ (τ : ℝ) {Y : ℝ}, 0 < Y →
        ‖smoothAFEZetaDisplacedDualWeight d τ Y - 1‖ ≤
          C * Y ^ (d + η) / (max 1 |τ|) ^ (d + η) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_uniform_le
      hd₀0 hd₀half hη hηhalf
  let G : ℝ := ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let H : ℝ := Real.exp ((d₀ + η) ^ 2) / η
  let C : ℝ := (1 / (2 * Real.pi)) * K * H * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun d hd hdd₀ τ {Y} hY => ?_⟩
  have hdhalf : d < 1 / 2 := hdd₀.trans_lt hd₀half
  have hweight := smoothAFEZetaDisplacedDualWeight_eq_one_add_at_neg
    hd hdhalf hη hηhalf hY τ
  have hdiff : smoothAFEZetaDisplacedDualWeight d τ Y - 1 =
      smoothAFEZetaDisplacedDualWeightAt (-(d + η)) d τ Y := by
    rw [hweight]
    ring
  rw [hdiff]
  let f : ℝ → ℂ := fun v =>
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
        (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)
  let D : ℝ :=
    K * (Y ^ (d + η) / (max 1 |τ|) ^ (d + η)) * H
  have hf : Integrable f :=
    smoothAFEZetaDisplacedDualWeightAt_neg_integrable
      hd hdhalf hη hηhalf hY τ
  have hmajor : Integrable (fun v : ℝ =>
      D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hfac : Real.exp ((d + η) ^ 2) / (d + η) ≤ H := by
    have hsum0 : 0 < d + η := by linarith
    have hsumle : d + η ≤ d₀ + η := by linarith
    have hsquares : (d + η) ^ 2 ≤ (d₀ + η) ^ 2 := by
      nlinarith
    have hexp : Real.exp ((d + η) ^ 2) ≤
        Real.exp ((d₀ + η) ^ 2) := Real.exp_le_exp.mpr hsquares
    dsimp only [H]
    apply (div_le_div_iff₀ hsum0 hη).2
    exact mul_le_mul hexp (by linarith) hη.le (Real.exp_pos _).le
  have hpoint : ∀ v : ℝ,
      ‖f v‖ ≤ D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    intro v
    have hr := hratio d hd hdd₀ τ v
    have hk := norm_smoothAFEGaussianKernel_vertical_le_of_ne
      (σ := -(d + η)) (by linarith) v
    have hpow :
        ‖(Y : ℂ) ^ (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ =
          Y ^ (d + η) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      simp
    have hvbase : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hvpow : (1 + |v|) ^ η ≤ 1 + |v| := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hvbase (by linarith : η ≤ 1)
    dsimp only [f, D]
    unfold smoothAFEMellinIntegrand
    rw [norm_mul, norm_mul, hpow]
    calc
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
          (-(((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (Y ^ (d + η) *
            ‖smoothAFEGaussianKernel
              (((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I)‖)
        ≤ (K * (1 + |v|) ^ η / (max 1 |τ|) ^ (d + η)) *
            (Y ^ (d + η) *
              ((Real.exp ((-(d + η)) ^ 2) / |-(d + η)|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ (d + η)) *
            (Y ^ (d + η) *
              ((Real.exp ((-(d + η)) ^ 2) / |-(d + η)|) *
                Real.exp (-(v ^ 2)))) := by
          gcongr
      _ = K * (Y ^ (d + η) / (max 1 |τ|) ^ (d + η)) *
            (Real.exp ((d + η) ^ 2) / (d + η)) *
            ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          rw [neg_sq, abs_neg, abs_of_pos (by linarith : 0 < d + η)]
          ring
      _ ≤ K * (Y ^ (d + η) / (max 1 |τ|) ^ (d + η)) * H *
            ((1 + |v|) * Real.exp (-(v ^ 2))) := by
          gcongr
  unfold smoothAFEZetaDisplacedDualWeightAt
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ v : ℝ, f v‖
      ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖f v‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          ∫ v : ℝ, D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = C * Y ^ (d + η) / (max 1 |τ|) ^ (d + η) := by
      rw [integral_const_mul]
      dsimp only [C, D, G]
      ring

end RHTower
