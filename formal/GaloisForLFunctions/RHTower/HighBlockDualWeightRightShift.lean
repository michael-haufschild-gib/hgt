import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualContourLimit
import GaloisForLFunctions.RHTower.ZetaChiLineSharp

/-!
# High-block law, brick B8 (dual side): large-argument decay of the displaced dual weight

The displaced dual weight is the Mellin integral on `Re w = 1` of
`χ(s − w)/χ(s) · Y^{−w} e^{w²}/w`, `s = ½ − d + iτ`. The integrand is analytic on `Re w > ½`,
so the contour moves to the right, to `Re w = ½ − d + K` (`K ∈ ℕ`, `K ≥ 1`), where `s − w` lies on
the fixed line `Re = −K` and Titchmarsh's sharp bound `‖χ(−K + it)‖ ≤ C |t|^{K + ½}` applies with
no dependence on `d`. Horizontal edges vanish by the Gaussian against polynomial strip growth.
Result: `‖W_{d,τ}(Y)‖ ≤ C (1 + |τ|)^{K+½} ‖χ(s)⁻¹‖ Y^{−(½ − d + K)}` — the decay for `Y ≫ τ` that
truncates the reflected series at `L ≍ √a` on a block.
-/

open Complex MeasureTheory Filter Topology Set intervalIntegral

namespace RHTower

noncomputable section

/-- The dual-weight integrand `χ(s − w)/χ(s) · Y^{−w} e^{w²}/w`. -/
def dualWeightIntegrand (d τ Y : ℝ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w) * smoothAFEMellinIntegrand Y w

theorem dualWeightIntegrand_analyticOnNhd_rightHalf (d τ : ℝ) (hd : 0 < d) {Y : ℝ}
    (hY : 0 < Y) :
    AnalyticOnNhd ℂ (dualWeightIntegrand d τ Y) {w : ℂ | 1 / 2 < w.re} := by
  intro w hw
  have hw' : (1 / 2 : ℝ) < w.re := hw
  have h1 : AnalyticAt ℂ (smoothAFEZetaDisplacedDualNumerator d τ Y) w :=
    smoothAFEZetaDisplacedDualNumerator_analyticOnNhd d τ hY w (by
      show -(d + 1 / 2) < w.re
      linarith)
  have hw0 : w - 0 ≠ 0 := by
    rw [sub_zero]
    intro h
    rw [h] at hw'
    simp at hw'
    linarith
  have h2 : AnalyticAt ℂ (fun w : ℂ => (w - 0)⁻¹) w :=
    (analyticAt_id.sub analyticAt_const).inv hw0
  have hfun : dualWeightIntegrand d τ Y
      = fun w => smoothAFEZetaDisplacedDualNumerator d τ Y w * (w - 0)⁻¹ := by
    funext w
    exact smoothAFEZetaDisplacedDualIntegrand_eq_numerator_div d τ Y w
  rw [hfun]
  exact h1.mul h2

/-- The rectangle `[1, K] × [−T, T]` has vanishing boundary integral. -/
theorem dualWeightIntegrand_rectIntegral_eq_zero {d τ Y K T : ℝ} (hd : 0 < d) (hY : 0 < Y)
    (hK : 1 ≤ K) :
    rectIntegral (dualWeightIntegrand d τ Y) (((1 : ℝ) : ℂ) - (T : ℂ) * I)
      ((K : ℂ) + (T : ℂ) * I) = 0 := by
  apply rectIntegral_eq_zero_of_analyticOnNhd (U := {w : ℂ | 1 / 2 < w.re}) ?_
    (dualWeightIntegrand_analyticOnNhd_rightHalf d τ hd hY)
  intro w hw
  have hre := (Complex.mem_reProdIm.mp hw).1
  have h1 : (((1 : ℝ) : ℂ) - (T : ℂ) * I).re = 1 := by simp
  have h2 : ((K : ℂ) + (T : ℂ) * I).re = K := by simp
  rw [h1, h2, uIcc_of_le hK] at hre
  show (1 / 2 : ℝ) < w.re
  linarith [hre.1]

/-- `χ` on the fixed line `Re = −K`: `C (1 + |t|)^{K + ½}` at every height. -/
theorem exists_norm_zetaChi_negNat_line_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖zetaChi ((((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ ((K : ℝ) + 1 / 2) := by
  obtain ⟨C₁, hC₁, hline⟩ := exists_norm_zetaChi_line_le (σ := -(K : ℝ)) (by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith)
  have hcont : ContinuousOn (fun t : ℝ => ‖zetaChi ((((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)‖)
      (Set.Icc (-2 : ℝ) 2) := by
    intro t _
    have hz : Gammaℝ (1 - ((((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    have hA := (zetaChi_analyticAt hz).continuousAt
    have hmap : ContinuousAt (fun t : ℝ => (((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I) t := by
      fun_prop
    exact ((ContinuousAt.comp (f := fun t : ℝ => (((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)
      hA hmap).norm).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hcont
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨max C₁ C₀, le_max_of_le_right hC₀0, fun t => ?_⟩
  have hp0 : (0 : ℝ) ≤ (K : ℝ) + 1 / 2 := by positivity
  have hone : (1 : ℝ) ≤ (1 + |t|) ^ ((K : ℝ) + 1 / 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((K : ℝ) + 1 / 2) := (Real.one_rpow _).symm
      _ ≤ (1 + |t|) ^ ((K : ℝ) + 1 / 2) :=
          Real.rpow_le_rpow zero_le_one (by linarith [abs_nonneg t]) hp0
  rcases le_or_gt 2 |t| with h2 | h2
  · have h := hline t h2
    have hpow : |t| ^ ((1 / 2 : ℝ) - (-(K : ℝ))) ≤ (1 + |t|) ^ ((K : ℝ) + 1 / 2) := by
      rw [show (1 / 2 : ℝ) - (-(K : ℝ)) = (K : ℝ) + 1 / 2 by ring]
      exact Real.rpow_le_rpow (abs_nonneg t) (by linarith) hp0
    calc ‖zetaChi ((((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ C₁ * |t| ^ ((1 / 2 : ℝ) - (-(K : ℝ))) := h
      _ ≤ C₁ * (1 + |t|) ^ ((K : ℝ) + 1 / 2) := mul_le_mul_of_nonneg_left hpow hC₁.le
      _ ≤ max C₁ C₀ * (1 + |t|) ^ ((K : ℝ) + 1 / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have ht : t ∈ Set.Icc (-2 : ℝ) 2 := by
      constructor <;> linarith [abs_lt.mp h2, neg_lt_of_abs_lt h2]
    have h := hC₀ t ht
    rw [norm_norm] at h
    calc ‖zetaChi ((((-(K : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C₀ := h
      _ ≤ C₀ * (1 + |t|) ^ ((K : ℝ) + 1 / 2) := le_mul_of_one_le_right hC₀0 hone
      _ ≤ max C₁ C₀ * (1 + |t|) ^ ((K : ℝ) + 1 / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- `(1 + |v|)^p e^{−v²} ≤ e^{p²} e^{−3v²/4}`. -/
theorem one_add_abs_rpow_mul_exp_neg_sq_le {p : ℝ} (hp : 0 ≤ p) (v : ℝ) :
    (1 + |v|) ^ p * Real.exp (-(v ^ 2)) ≤ Real.exp (p ^ 2) * Real.exp (-(3 / 4) * v ^ 2) := by
  have hlog : Real.log (1 + |v|) ≤ |v| := by
    have := Real.log_le_sub_one_of_pos (by linarith [abs_nonneg v] : (0 : ℝ) < 1 + |v|)
    linarith
  have hpow : (1 + |v|) ^ p = Real.exp (p * Real.log (1 + |v|)) := by
    rw [Real.rpow_def_of_pos (by linarith [abs_nonneg v])]
    ring_nf
  have hpv : p * |v| ≤ p ^ 2 + v ^ 2 / 4 := by
    nlinarith [sq_nonneg (|v| / 2 - p), sq_abs v]
  rw [hpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hlog hp
  nlinarith [this, hpv]

/-- Pointwise bound on the strip `1 ≤ Re w ≤ K`: only the `χ` factor is left implicit. -/
theorem norm_dualWeightIntegrand_le_strip {d τ Y K u : ℝ} (hY : 0 < Y) (hu1 : 1 ≤ u)
    (huK : u ≤ K) (t : ℝ) :
    ‖dualWeightIntegrand d τ Y ((u : ℂ) + (t : ℂ) * I)‖ ≤
      ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - t : ℝ) : ℂ) * I)‖ *
        ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
        (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(t ^ 2)) := by
  unfold dualWeightIntegrand smoothAFEZetaChiShiftRatio
  have harg : displacedLinePt d τ + -((u : ℂ) + (t : ℂ) * I)
      = ((1 / 2 - d - u : ℝ) : ℂ) + ((τ - t : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [harg, norm_mul, div_eq_mul_inv, norm_mul]
  have hmell := norm_smoothAFEMellinIntegrand_vertical_le hY (by linarith : (0 : ℝ) < u) t
  have hY' : Y ^ (-u) ≤ Real.exp (K * |Real.log Y|) := by
    rw [Real.rpow_def_of_pos hY]
    apply Real.exp_le_exp.mpr
    have h1 : -|Real.log Y| ≤ Real.log Y := neg_abs_le _
    nlinarith [abs_nonneg (Real.log Y)]
  have hk : Real.exp (u ^ 2) / u ≤ Real.exp (K ^ 2) := by
    calc Real.exp (u ^ 2) / u ≤ Real.exp (u ^ 2) := div_le_self (Real.exp_pos _).le hu1
      _ ≤ Real.exp (K ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hprod : Y ^ (-u) * (Real.exp (u ^ 2) / u)
      ≤ Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2) :=
    mul_le_mul hY' hk (by positivity) (Real.exp_pos _).le
  refine le_trans (mul_le_mul_of_nonneg_left hmell (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) (by positivity)) ?_
  apply le_of_eq
  ring

/-- Top horizontal edge of the right-shift rectangle vanishes. -/
theorem tendsto_dualWeightIntegrand_horizontal_top {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (1 : ℝ)..(1 / 2 - d + K''),
      dualWeightIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨T₀, N, C, hC, hgrow⟩ := hasStripPolyGrowthOffReal_zetaChi (-((K'' : ℝ) + 1)) 0
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  set B : ℝ := C * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
    (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ =>
      (K * B) * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) N).const_mul (K * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max |τ| (|τ| + T₀))] with T hT
  have hTτ : |τ| ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := (abs_nonneg τ).trans hTτ
  have hTlarge : |τ| + T₀ ≤ T := (le_max_right _ _).trans hT
  have habs : |τ - T| = T - τ := by
    rw [abs_of_nonpos (by linarith [le_abs_self τ])]
    ring
  have hbound : ∀ u ∈ Set.uIoc (1 : ℝ) K,
      ‖dualWeightIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le hK1] at hu
    have hu1 : 1 ≤ u := hu.1.le
    have huK : u ≤ K := hu.2
    have hpt := norm_dualWeightIntegrand_le_strip (d := d) (τ := τ) (K := K) hY hu1 huK T
    have him : ((((1 / 2 - d - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I)).im = τ - T := by simp
    have hchi : ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I)‖
        ≤ C * (1 + |τ| + T) ^ N := by
      have h := hgrow (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I)
        (by simp; rw [hKdef] at huK; linarith) (by simp; linarith)
        (by rw [him, habs]; linarith [neg_abs_le τ, le_abs_self τ])
      rw [him, habs] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by linarith [le_abs_self τ, neg_abs_le τ]) _ N
      linarith [neg_abs_le τ]
    calc ‖dualWeightIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)‖
        ≤ ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - T : ℝ) : ℂ) * I)‖ *
            ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
            (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(T ^ 2)) := hpt
      _ ≤ (C * (1 + |τ| + T) ^ N) * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
            (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(T ^ 2)) := by
          gcongr
      _ = B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) := by
          rw [hBdef]; ring
  calc ‖∫ u : ℝ in (1 : ℝ)..K, dualWeightIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) * |K - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) * (K - 1) := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ K - 1)]
    _ ≤ B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) * K :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (K * B) * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) := by ring

/-- Bottom horizontal edge of the right-shift rectangle vanishes. -/
theorem tendsto_dualWeightIntegrand_horizontal_bottom {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (1 : ℝ)..(1 / 2 - d + K''),
      dualWeightIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨T₀, N, C, hC, hgrow⟩ := hasStripPolyGrowthOffReal_zetaChi (-((K'' : ℝ) + 1)) 0
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  set B : ℝ := C * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
    (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmajor : Tendsto (fun T : ℝ =>
      (K * B) * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 + |τ|) N).const_mul (K * B)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (max |τ| (|τ| + T₀))] with T hT
  have hTτ : |τ| ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := (abs_nonneg τ).trans hTτ
  have hTlarge : |τ| + T₀ ≤ T := (le_max_right _ _).trans hT
  have habs : |τ - -T| = τ + T := by
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith [neg_abs_le τ, le_abs_self τ])]
  have hbound : ∀ u ∈ Set.uIoc (1 : ℝ) K,
      ‖dualWeightIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)‖ ≤
        B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le hK1] at hu
    have hu1 : 1 ≤ u := hu.1.le
    have huK : u ≤ K := hu.2
    have hF : dualWeightIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)
        = dualWeightIntegrand d τ Y ((u : ℂ) + ((-T : ℝ) : ℂ) * I) := by
      congr 1
      push_cast
      ring
    rw [hF]
    have hpt := norm_dualWeightIntegrand_le_strip (d := d) (τ := τ) (K := K) hY hu1 huK (-T)
    rw [neg_sq] at hpt
    have him : ((((1 / 2 - d - u : ℝ) : ℂ) + ((τ - -T : ℝ) : ℂ) * I)).im = τ - -T := by simp
    have hchi : ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - -T : ℝ) : ℂ) * I)‖
        ≤ C * (1 + |τ| + T) ^ N := by
      have h := hgrow (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - -T : ℝ) : ℂ) * I)
        (by simp; rw [hKdef] at huK; linarith) (by simp; linarith)
        (by rw [him, habs]; linarith [neg_abs_le τ, le_abs_self τ])
      rw [him, habs] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by linarith [le_abs_self τ, neg_abs_le τ]) _ N
      linarith [le_abs_self τ]
    calc ‖dualWeightIntegrand d τ Y ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖
        ≤ ‖zetaChi (((1 / 2 - d - u : ℝ) : ℂ) + ((τ - -T : ℝ) : ℂ) * I)‖ *
            ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
            (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(T ^ 2)) := hpt
      _ ≤ (C * (1 + |τ| + T) ^ N) * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
            (Real.exp (K * |Real.log Y|) * Real.exp (K ^ 2)) * Real.exp (-(T ^ 2)) := by
          gcongr
      _ = B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) := by
          rw [hBdef]; ring
  calc ‖∫ u : ℝ in (1 : ℝ)..K, dualWeightIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)‖
      ≤ B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) * |K - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) * (K - 1) := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ K - 1)]
    _ ≤ B * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) * K :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (K * B) * ((1 + |τ| + T) ^ N * Real.exp (-(T ^ 2))) := by ring

/-- Pointwise Gaussian majorant on the shifted line `Re w = ½ − d + K`. -/
theorem norm_dualWeightIntegrand_right_line_le {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ t : ℝ, ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ C₁ * (1 + |t|) ^ ((K'' : ℝ) + 1 / 2)) (τ v : ℝ) :
    ‖dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
          (Y ^ (-(1 / 2 - d + K'')) * Real.exp ((1 / 2 - d + K'') ^ 2)) *
          Real.exp (((K'' : ℝ) + 1 / 2) ^ 2)) *
        (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2) * Real.exp (-(3 / 4) * v ^ 2) := by
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  set p : ℝ := (K'' : ℝ) + 1 / 2 with hpdef
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hKpos : 0 < K := by linarith
  have hp0 : 0 ≤ p := by rw [hpdef]; positivity
  unfold dualWeightIntegrand smoothAFEZetaChiShiftRatio
  have harg : displacedLinePt d τ + -((K : ℂ) + (v : ℂ) * I)
      = (((-(K'' : ℝ)) : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    rw [hKdef]
    push_cast
    ring
  rw [harg, norm_mul, div_eq_mul_inv, norm_mul]
  -- the χ factor
  have hsum : 1 + |τ - v| ≤ (1 + |τ|) * (1 + |v|) := by
    have h1 : |τ - v| ≤ |τ| + |v| := abs_le.mpr ⟨by
      linarith [le_abs_self τ, neg_abs_le τ, le_abs_self v, neg_abs_le v], by
      linarith [le_abs_self τ, neg_abs_le τ, le_abs_self v, neg_abs_le v]⟩
    nlinarith [abs_nonneg τ, abs_nonneg v]
  have hrp : (1 + |τ - v|) ^ p ≤ (1 + |τ|) ^ p * (1 + |v|) ^ p := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hsum hp0
  have hA : ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I)‖
      ≤ C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p) :=
    (hC₁ (τ - v)).trans (mul_le_mul_of_nonneg_left hrp hC₁0)
  -- the Mellin factor
  have hM : ‖smoothAFEMellinIntegrand Y ((K : ℂ) + (v : ℂ) * I)‖
      ≤ (Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (-(v ^ 2)) := by
    refine (norm_smoothAFEMellinIntegrand_vertical_le hY hKpos v).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le hK1) (by positivity))
      (Real.exp_pos _).le
  have hS : 0 ≤ ‖(zetaChi (displacedLinePt d τ))⁻¹‖ := norm_nonneg _
  have h1 : ‖zetaChi ((((-(K'' : ℝ)) : ℝ) : ℂ) + ((τ - v : ℝ) : ℂ) * I)‖ *
        ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
        ‖smoothAFEMellinIntegrand Y ((K : ℂ) + (v : ℂ) * I)‖
      ≤ (C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p)) * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
        ((Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (-(v ^ 2))) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hA hS) hM (norm_nonneg _) (by positivity)
  refine h1.trans ?_
  have h2 := one_add_abs_rpow_mul_exp_neg_sq_le hp0 v
  calc (C₁ * ((1 + |τ|) ^ p * (1 + |v|) ^ p)) * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
        ((Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (-(v ^ 2)))
      = (C₁ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ * (Y ^ (-K) * Real.exp (K ^ 2)) *
          (1 + |τ|) ^ p) * ((1 + |v|) ^ p * Real.exp (-(v ^ 2))) := by ring
    _ ≤ (C₁ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ * (Y ^ (-K) * Real.exp (K ^ 2)) *
          (1 + |τ|) ^ p) * (Real.exp (p ^ 2) * Real.exp (-(3 / 4) * v ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (C₁ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ * (Y ^ (-K) * Real.exp (K ^ 2)) *
          Real.exp (p ^ 2)) * (1 + |τ|) ^ p * Real.exp (-(3 / 4) * v ^ 2) := by ring

/-- Continuity of the integrand along the shifted line. -/
theorem continuous_dualWeightIntegrand_right_line {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y)
    {K : ℝ} (hK : 1 ≤ K) (τ : ℝ) :
    Continuous (fun v : ℝ => dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  have hA : AnalyticAt ℂ (dualWeightIntegrand d τ Y) ((K : ℂ) + (v : ℂ) * I) :=
    dualWeightIntegrand_analyticOnNhd_rightHalf d τ hd hY _ (by
      show (1 / 2 : ℝ) < ((K : ℂ) + (v : ℂ) * I).re
      simp
      linarith)
  exact ContinuousAt.comp (f := fun v : ℝ => (K : ℂ) + (v : ℂ) * I) hA.continuousAt
    (by fun_prop)

/-- Integrability along the shifted line. -/
theorem integrable_dualWeightIntegrand_right_line {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    Integrable (fun v : ℝ =>
      dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zetaChi_negNat_line_le K''
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hK1 : (1 : ℝ) ≤ 1 / 2 - d + K'' := by linarith
  have hcont := continuous_dualWeightIntegrand_right_line hd hY hK1 τ
  have hint : Integrable (fun v : ℝ =>
      ((C₁ * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
          (Y ^ (-(1 / 2 - d + K'')) * Real.exp ((1 / 2 - d + K'') ^ 2)) *
          Real.exp (((K'' : ℝ) + 1 / 2) ^ 2)) *
        (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2)) * Real.exp (-(3 / 4) * v ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 3 / 4)).const_mul _
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  exact norm_dualWeightIntegrand_right_line_le hd hd4 hY hK'' hC₁0 hC₁ τ v

/-- The line `Re w = 1` and the shifted line `Re w = ½ − d + K` carry the same integral. -/
theorem integral_dualWeightIntegrand_one_eq_right {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    (∫ v : ℝ, dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) =
      ∫ v : ℝ, dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hbottom := tendsto_dualWeightIntegrand_horizontal_bottom hd hd4 hY hK'' τ
  have htop := tendsto_dualWeightIntegrand_horizontal_top hd hd4 hY hK'' τ
  have hrightK : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ,
        dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral (integrable_dualWeightIntegrand_right_line hd hd4 hY hK'' τ)
      tendsto_neg_atTop_atBot tendsto_id
  have hright1 : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T,
      dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) atTop
      (𝓝 (∫ v : ℝ, dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I))) :=
    tendsto_smoothAFEZetaDisplacedDual_right_intervalIntegral hd (by linarith) hY τ
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hlimit := ((hbottom.sub htop).add (hrightK.const_smul I)).sub (hright1.const_smul I)
  have hlimit' : Tendsto
      (fun T : ℝ =>
        ((∫ u : ℝ in (1 : ℝ)..K, dualWeightIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)) -
            (∫ u : ℝ in (1 : ℝ)..K, dualWeightIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)) +
          I • (∫ v : ℝ in (-T)..T, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I))) -
          I • (∫ v : ℝ in (-T)..T, dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)))
      atTop
      (𝓝 (I • (∫ v : ℝ, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) -
          I • (∫ v : ℝ, dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)))) := by
    simpa [sub_eq_add_neg] using hlimit
  have hevent : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (1 : ℝ)..K, dualWeightIntegrand d τ Y ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (1 : ℝ)..K, dualWeightIntegrand d τ Y ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I))
        = 0 := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hrect := dualWeightIntegrand_rectIntegral_eq_zero (d := d) (τ := τ) (Y := Y)
      (K := K) (T := T) hd hY hK1
    simpa [RHTower.rectIntegral, sub_eq_add_neg] using hrect
  have h := tendsto_nhds_unique (hlimit'.congr' hevent) (tendsto_const_nhds (x := (0 : ℂ)))
  have h' : I • ((∫ v : ℝ, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)) -
      ∫ v : ℝ, dualWeightIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) = 0 := by
    rw [smul_sub]
    exact h
  rcases smul_eq_zero.mp h' with hI | hdiff
  · exact absurd hI I_ne_zero
  · exact (sub_eq_zero.mp hdiff).symm

/-- **Large-argument decay of the displaced dual weight (right contour shift).** For every
`K ≥ 1` one constant serves all displacements `0 < d ≤ ¼`, all heights `τ` and all `Y > 0`:
`‖W_{d,τ}(Y)‖ ≤ C (1 + |τ|)^{K + ½} ‖χ(s)⁻¹‖ Y^{−(½ − d + K)}`. -/
theorem exists_norm_smoothAFEZetaDisplacedDualWeight_le_rightShift {K'' : ℕ} (hK'' : 1 ≤ K'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d τ Y : ℝ, 0 < d → d ≤ 1 / 4 → 0 < Y →
      ‖smoothAFEZetaDisplacedDualWeight d τ Y‖ ≤
        C * (1 + |τ|) ^ ((K'' : ℝ) + 1 / 2) * ‖(zetaChi (displacedLinePt d τ))⁻¹‖ *
          Y ^ (-(1 / 2 - d + K'')) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zetaChi_negNat_line_le K''
  have hG0 : 0 ≤ ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  refine ⟨(1 / (2 * Real.pi)) * (C₁ * Real.exp (((K'' : ℝ) + 1 / 2) ^ 2) *
    Real.exp (((K'' : ℝ) + 1 / 2) ^ 2) * ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2)),
    by positivity, fun d τ Y hd hd4 hY => ?_⟩
  have hK''1 : (1 : ℝ) ≤ K'' := Nat.one_le_cast.mpr hK''
  have hbound := fun v : ℝ =>
    norm_dualWeightIntegrand_right_line_le hd hd4 hY hK'' hC₁0 hC₁ τ v
  have hW : smoothAFEZetaDisplacedDualWeight d τ Y =
      (1 / (2 * Real.pi)) • ∫ v : ℝ,
        dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDisplacedDualWeight smoothAFEZetaDisplacedDualWeightAt
    congr 1
    exact integral_dualWeightIntegrand_one_eq_right hd hd4 hY hK'' τ
  have hint : Integrable (fun v : ℝ => Real.exp (-(3 / 4) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  set G : ℝ := ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) with hGdef
  set K : ℝ := 1 / 2 - d + K'' with hKdef
  set p : ℝ := (K'' : ℝ) + 1 / 2 with hpdef
  set S : ℝ := ‖(zetaChi (displacedLinePt d τ))⁻¹‖ with hSdef
  have hS0 : 0 ≤ S := norm_nonneg _
  have hKp : K ≤ p := by rw [hKdef, hpdef]; linarith
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  have hexpK : Real.exp (K ^ 2) ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  set A : ℝ := (C₁ * S * (Y ^ (-K) * Real.exp (K ^ 2)) * Real.exp (p ^ 2)) * (1 + |τ|) ^ p
    with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hnorm : ‖∫ v : ℝ, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖ ≤ A * G := by
    calc ‖∫ v : ℝ, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖
        ≤ ∫ v : ℝ, ‖dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, A * Real.exp (-(3 / 4) * v ^ 2) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
            (hint.const_mul A) (Filter.Eventually.of_forall fun v => hbound v)
      _ = A * G := by rw [MeasureTheory.integral_const_mul]
  rw [hW, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ, dualWeightIntegrand d τ Y ((K : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (A * G) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (1 / (2 * Real.pi)) * (C₁ * Real.exp (K ^ 2) * Real.exp (p ^ 2) * G) *
          (1 + |τ|) ^ p * S * Y ^ (-K) := by rw [hAdef]; ring
    _ ≤ (1 / (2 * Real.pi)) * (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2) * G) *
          (1 + |τ|) ^ p * S * Y ^ (-K) := by gcongr

end

end RHTower
