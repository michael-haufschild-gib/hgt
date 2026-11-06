import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheCentralInequalityAtTheCriticalScale

/-!
# The zeros are real at the critical scale

For every `δ > 0` there is `κ` such that for all large `T`, outside a set of `X ∈ [T, 2T]` of measure at most `δT`: every zero `z` of `H_t` with `|Re z − X| ≤ κ/(2 log T)` and `t log(Re z/2π) ≥ 7κ/log T` is real (`exists_zeros_real_at_critical_scale`).

This is the upper side of the linear depth law at typical heights. Zeros of depth `> R₀ = κ/log T` are absent near `X`, and those of smaller depth are real by the time `t ≍ R₀/log X`: the time `d/log X` of the pair model, with `d` the largest depth near the height. At the same time the local count at scale `R₀` is `≪ κ` (`exists_volume_localZeroCount_gt_le`), so a crowd does not occur, in agreement with the depth law `t(R₁ + log X) ≲ d` of `TheDepthLawSeesOnlyTheCrowd`.

**Mechanism.** `H_t(x + iy) = Q(−y) + conj Q(y)`, so it suffices that `|Q(−y)| < |Q(y)|` for `y > 0`.
* For `y ≤ 6/α`: `Re(Q′ conj Q) > 0` on `[−y, y]`, since `Q′ ≈ aQ` and `Re a = α > 0`.
* For `y > 6/α`: reflection `G(w + y) = e^{−wy/τ} G(w − y)` suppresses the window of `Q(−y)` by `e^{−(u/3) y/τ} ≤ e^{−4}`, while its strip and its top are small, and `|Q(y)|` is its full amplitude. The saddle `u = y + 2τα` runs through the dyadic scales up to `1/7`, and above that through a fixed typical box.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The two comparisons -/

/-- The amplitude carries the slope: `Re(D Q̄) > 0` from the two quadrature estimates. -/
theorem re_mul_conj_pos_of_estimates {Q M D a : ℂ} {P : ℝ} (hP : 0 < P) (ha : 0 < a.re) (hQM : ‖Q - M‖ ≤ P * (1 / 5))
    (hM : 23 / 25 * P ≤ ‖M‖) (hD : ‖D - a * Q‖ ≤ P * (a.re / 100)) : 0 < (D * starRingEnd ℂ Q).re := by
  have hQ : 18 / 25 * P ≤ ‖Q‖ := by
    have h1 := norm_sub_norm_le M Q
    rw [norm_sub_rev M Q] at h1
    linarith only [h1, hQM, hM]
  have hQ0 : 0 < ‖Q‖ := by linarith only [hQ, hP]
  have hid : D * starRingEnd ℂ Q = (D - a * Q) * starRingEnd ℂ Q + a * (Q * starRingEnd ℂ Q) := by ring
  have hconj : Q * starRingEnd ℂ Q = ((‖Q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hid, Complex.add_re, hconj, Complex.re_mul_ofReal]
  have h2 : -(‖D - a * Q‖ * ‖Q‖) ≤ ((D - a * Q) * starRingEnd ℂ Q).re := by
    have h3 := Complex.abs_re_le_norm ((D - a * Q) * starRingEnd ℂ Q)
    rw [norm_mul, RCLike.norm_conj] at h3
    exact (abs_le.mp h3).1
  have h4 : ‖D - a * Q‖ * ‖Q‖ ≤ P * (a.re / 100) * ‖Q‖ := mul_le_mul_of_nonneg_right hD hQ0.le
  have h5 : a.re * (18 / 25 * P) ≤ a.re * ‖Q‖ := mul_le_mul_of_nonneg_left hQ ha.le
  have h6 : (a.re * (18 / 25 * P) - P * (a.re / 100)) * ‖Q‖ ≤ (a.re * ‖Q‖ - P * (a.re / 100)) * ‖Q‖ :=
    mul_le_mul_of_nonneg_right (by linarith only [h5]) hQ0.le
  have h7 : 0 < (a.re * (18 / 25 * P) - P * (a.re / 100)) * ‖Q‖ := by
    have : a.re * (18 / 25 * P) - P * (a.re / 100) = 71 / 100 * (a.re * P) := by ring
    rw [this]
    positivity
  nlinarith only [h2, h4, h6, h7]

/-- **Far from the axis.** The opposite half is small against the transform. -/
theorem norm_opposite_lt_of_source {τ Y y u B : ℝ} (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hβ1 : 1 ≤ (horizontalSlope Y).re)
    (hy : 0 < y) (hrel : y + 2 * τ * (horizontalSlope Y).re = u) (hu : 0 < u) (hB0 : 0 < B)
    (hB : 100 * B ≤ (horizontalSlope Y).re) (hΛ : 200 ≤ (u - y) * (horizontalSlope Y).re)
    (hq : B * Real.sqrt τ ≤ 1 / 200) (hδ : 480000 ≤ u * (horizontalSlope Y).re) (hfar : 4 ≤ u / 3 * y / τ)
    (hslope : ∀ w ∈ Icc (u / 3) (5 * u / 4),
      ‖xiLineDeriv Y w - horizontalSlope Y * xiLine Y w‖ ≤ B * ‖xiLine Y w‖)
    (hlow : ∀ w ∈ Icc (0 : ℝ) (u / 3), ‖xiLine Y w‖ ≤ ‖xiLine Y (u / 3)‖)
    (htop : ∀ w, 5 * u / 4 ≤ w → ‖xiLine Y w‖ ≤ ‖xiLine Y (5 * u / 4)‖ *
      Real.exp (((horizontalSlope Y).re + B) * (w ^ 2 - (5 * u / 4) ^ 2) / (2 * (5 * u / 4))))
    (hne : xiLine Y u ≠ 0) :
    ‖halfGaussTransform τ (xiLine Y) (-y)‖ < ‖halfGaussTransform τ (xiLine Y) y‖ := by
  obtain ⟨-, -, hstrip, -, htopm, hwin, hmain⟩ := source_core hτ hβ1 hu hrel (by linarith only [hy, hu]) hB0 hB hΛ
    hslope hlow htop
  set β := (horizontalSlope Y).re with hβ
  set P := ‖xiLine Y u‖ * Real.exp (-(τ * β ^ 2)) with hP
  have hPpos : 0 < P := mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)
  set δ := Real.exp (-(u * β / 40)) with hδdef
  have hδ1 : δ ≤ 1 / 12000 := exp_neg_le_of_le (by norm_num) (by linarith only [hδ])
  have hδ0 : 0 < δ := Real.exp_pos _
  have hE := model_le_tenth hB0.le hτ hq
  have hE0 := gaussianSaddleModelError_nonneg (t := τ) hB0.le
  -- the transform at `y` has its full amplitude
  have hMain : 23 / 25 * P ≤ ‖xiLine Y u * Complex.exp (-(u * horizontalSlope Y)) *
      Complex.exp (y * horizontalSlope Y + τ * horizontalSlope Y ^ 2)‖ := by
    have h1 := norm_main_eq (t := τ) (X := Y) (y := y) (xiLine Y u)
    rw [hrel] at h1
    rw [h1, ← hβ, ← hP]
    have h2 := gaussPhase_ge hτ8 hτ
    nlinarith only [mul_le_mul_of_nonneg_left h2 hPpos.le]
  have hlow2 : 7 / 10 * P ≤ ‖halfGaussTransform τ (xiLine Y) y‖ := by
    have h1 := norm_sub_norm_le (xiLine Y u * Complex.exp (-(u * horizontalSlope Y)) *
      Complex.exp (y * horizontalSlope Y + τ * horizontalSlope Y ^ 2)) (halfGaussTransform τ (xiLine Y) y)
    rw [norm_sub_rev _ (halfGaussTransform τ (xiLine Y) y)] at h1
    have h2 := mul_le_mul_of_nonneg_left (show gaussianSaddleModelError B τ + 8 * δ ≤ 1 / 5 by
      linarith only [hE, hδ1]) hPpos.le
    linarith only [h1, hmain, h2, hMain, hPpos]
  -- the opposite half
  have hIabs (w : ℝ) (hw : 0 ≤ w) : gaussDensity τ (w - -y) ≤ gaussDensity τ (w - y) := by
    rw [sub_neg_eq_add]
    have h1 := gaussDensity_add_le_of_lower_bound (b := 0) hτ hy.le hw
    simpa using h1
  have hthree := norm_halfGaussTransform_le_three_masses (continuous_xiLine Y) (y := -y) (b := u / 3)
    (W := 5 * u / 4) hτ (by positivity) (by linarith only [hu]) (integrable_exp_mul_norm_xiLine hτ Y)
  have hc (z : ℝ) : Continuous fun w => gaussDensity τ (w - z) := (continuous_gaussDensity τ).comp (by fun_prop)
  have hI1 (z : ℝ) : Integrable (fun w => gaussDensity τ (w - z) * ‖xiLine Y w‖) := by
    refine (integrable_gaussDensity_sub_mul hτ (continuous_xiLine Y)
      (integrable_exp_mul_norm_xiLine hτ Y) z).norm.congr (Eventually.of_forall fun w => ?_)
    exact norm_gauss_mul τ z w hτ _
  have hA : (∫ w in Ioc 0 (u / 3), gaussDensity τ (w - -y) * ‖xiLine Y w‖) ≤ P * δ := by
    refine le_trans (setIntegral_mono_on (hI1 _).integrableOn (hI1 _).integrableOn measurableSet_Ioc fun w hw =>
      mul_le_mul_of_nonneg_right (hIabs w hw.1.le) (norm_nonneg _)) hstrip
  have hB' : (∫ w in Ioc (u / 3) (5 * u / 4), gaussDensity τ (w - -y) * ‖xiLine Y w‖) ≤
      Real.exp (-(u / 3 * y / τ)) * (P * (1 + gaussianSaddleModelError B τ)) := by
    have h1 := opposite_window_mass_le (continuous_xiLine Y) (b := u / 3) (W := 5 * u / 4) hτ hy.le
    simp only [sub_neg_eq_add]
    exact h1.trans (mul_le_mul_of_nonneg_left hwin (Real.exp_pos _).le)
  have hC : (∫ w in Ioi (5 * u / 4), gaussDensity τ (w - -y) * ‖xiLine Y w‖) ≤ 5 * (P * δ) := by
    refine le_trans (setIntegral_mono_on (hI1 _).integrableOn (hI1 _).integrableOn measurableSet_Ioi fun w hw =>
      mul_le_mul_of_nonneg_right (hIabs w ?_) (norm_nonneg _)) htopm
    have : 5 * u / 4 < w := hw
    linarith only [this, hu]
  have hexp4 : Real.exp (-(u / 3 * y / τ)) ≤ 1 / 4 := exp_neg_le_of_le (by norm_num) hfar
  have h5 : Real.exp (-(u / 3 * y / τ)) * (P * (1 + gaussianSaddleModelError B τ)) ≤ 1 / 4 * (P * (11 / 10)) :=
    mul_le_mul hexp4 (mul_le_mul_of_nonneg_left (by linarith only [hE]) hPpos.le) (by positivity) (by norm_num)
  have h6 : P * δ ≤ P * (1 / 12000) := mul_le_mul_of_nonneg_left hδ1 hPpos.le
  linarith only [hthree, hA, hB', hC, h5, h6, hlow2, hPpos]

/-! ## The typical box above the dyadic scales -/

/-- The source hypotheses at a large saddle, from a fixed typical box. -/
theorem source_hyps_of_typical {η T t X R₀ Y u : ℝ} (h : zetaTypicalHeight η (zetaPolylogLevel T) T t) (hη : 0 < η)
    (hη1 : η ≤ 1) (hT : 8 ≤ T) (hR₀ : 0 < R₀) (hK : ZeroKeeping X R₀) (hY : |Y - X| < R₀) (hY200 : 200 ≤ Y)
    (hYt : |Y - t| ≤ η) (hu0 : 0 < u) (hu1 : 6 * η ≤ u) (hR₀u : 6 * R₀ ≤ u) (hu2 : u ≤ 1) :
    (∀ w ∈ Icc (u / 3) (5 * u / 4), ‖xiLineDeriv Y w - horizontalSlope Y * xiLine Y w‖ ≤
      typicalXiSlopeError η T * ‖xiLine Y w‖) ∧
    (∀ w ∈ Icc (0 : ℝ) (u / 3), ‖xiLine Y w‖ ≤ ‖xiLine Y (u / 3)‖) ∧
    (∀ w, 5 * u / 4 ≤ w → ‖xiLine Y w‖ ≤ ‖xiLine Y (5 * u / 4)‖ *
      Real.exp (((horizontalSlope Y).re + typicalXiSlopeError η T) * (w ^ 2 - (5 * u / 4) ^ 2) / (2 * (5 * u / 4)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    exact norm_xiLineDeriv_sub_le_of_typical h hη hη1 hT hY200 hYt (by linarith only [hw.1, hu1])
      (by linarith only [hw.2, hu2, hY200])
  · intro w hw
    exact norm_xiLine_le_of_keeping hR₀ hK hY hw.1 hw.2 (by linarith only [hR₀u])
  · intro w hw
    refine norm_xiLine_le_growth hR₀ (hK.keepsAway hY.le) (by linarith only [hR₀u, hu0]) hw ?_
    have hd := norm_logDeriv_xi_horizontal_le_of_typical h hη hη1 hT hY200 hYt (σ := 5 * u / 4 + 1 / 2)
      (by linarith only [hu1, hu0]) (by linarith only [hu2, hY200])
    have h1 := Complex.re_le_norm (logDeriv xi (linePt Y (5 * u / 4)) - horizontalSlope Y)
    rw [Complex.sub_re] at h1
    have hd' : ‖logDeriv xi (linePt Y (5 * u / 4)) - horizontalSlope Y‖ ≤ typicalXiSlopeError η T := by
      simpa [linePt] using hd
    linarith only [h1, hd']

/-- The slope error of a fixed typical box is a power of `log log T`, negligible against `√(log T)`. -/
theorem eventually_typicalSlope_small :
    ∀ᶠ T : ℝ in atTop, 20000 * typicalXiSlopeError (1 / 128) T ^ 2 ≤ Real.log T := by
  set c₁ : ℝ := 24 * 128 ^ 2 with hc₁
  have hform (T : ℝ) : typicalXiSlopeError (1 / 128) T =
      4 * c₁ * Real.log (scaleLog T) + (9 * c₁ + 4) := by
    unfold typicalXiSlopeError scaleLog
    rw [hc₁]
    field_simp
    ring
  set a := 4 * c₁ with ha
  set b := 9 * c₁ + 4 with hb
  have ha0 : 0 < a := by rw [ha, hc₁]; norm_num
  have hb0 : 0 < b := by rw [hb, hc₁]; norm_num
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hsmall : 0 < 1 / (320000 * a ^ 2) := by positivity
  have h3 := (h2.comp tendsto_scaleLog).eventually (ge_mem_nhds hsmall)
  have hlog4 : ∀ᶠ T : ℝ in atTop, 2 * Real.log 4 + 2 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [h3, tendsto_scaleLog.eventually_ge_atTop (160000 * b ^ 2), hlog4, eventually_gt_atTop (1 : ℝ)]
    with T h3 h4 h5 hT1
  rw [hform]
  have hT0 : 0 < T := by linarith only [hT1]
  have hy : scaleLog T ≤ 2 * Real.log T := by
    unfold scaleLog
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith only [h5, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hy0 : 0 < scaleLog T := lt_of_lt_of_le (by positivity) h4
  simp only [Function.comp, one_mul, add_zero] at h3
  rw [div_le_iff₀ hy0] at h3
  have h6 : a ^ 2 * (Real.log (scaleLog T) ^ 2) ≤ scaleLog T / 320000 := by
    have h7 := mul_le_mul_of_nonneg_left h3 (sq_nonneg a)
    refine h7.trans (le_of_eq ?_)
    field_simp
  have h8 : (a * Real.log (scaleLog T) + b) ^ 2 ≤ 2 * (a ^ 2 * Real.log (scaleLog T) ^ 2) + 2 * b ^ 2 := by
    nlinarith only [sq_nonneg (a * Real.log (scaleLog T) - b)]
  linarith only [h4, h6, h8, hy]

/-! ## The theorem -/

/-- **No nonreal zero at a good height.** -/
theorem riemannHeat_ne_zero_of_critical {q T X τ x y : ℝ} (hq : (10 : ℝ) ^ 4 ≤ q) (hT : 1100 ≤ T)
    (hlog : (10 : ℝ) ^ 6 ≤ Real.log T) (hXT : X ∈ Icc T (2 * T)) (hgood : CriticalGood q T X)
    (htyp : ∃ t, zetaTypicalHeight (1 / 128) (zetaPolylogLevel T) T t ∧ |x - t| ≤ 1 / 128)
    (hsmall : 20000 * typicalXiSlopeError (1 / 128) T ^ 2 ≤ Real.log T)
    (hx : |x - X| ≤ q ^ 4 / Real.log T / 2) (hτ : 0 < τ)
    (h7 : 7 * (q ^ 4 / Real.log T) ≤ 2 * τ * (horizontalSlope x).re) (h8 : 2 * τ * (horizontalSlope x).re ≤ 1 / 8)
    (hy0 : y ≠ 0) (hy : |y| ≤ 1 / 2) : riemannHeat τ ((x : ℂ) + I * y) ≠ 0 := by
  obtain ⟨hK, hdata⟩ := hgood
  set L := Real.log T with hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hlog
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  set R₀ := q ^ 4 / L with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  have hq4 : ((10 : ℝ) ^ 4) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by positivity) hq 4
  have hR₀small : R₀ ≤ 1 / 56 := by linarith only [h7, h8]
  have hx1 := abs_le.mp hx
  have hxlo : T - 1 ≤ x := by linarith only [hXT.1, hx1.1, hR₀small]
  have hxhi : x ≤ 2 * T + 1 := by linarith only [hXT.2, hx1.2, hR₀small]
  have hT0 : 0 < T := by linarith only [hT]
  have hscale : L ≤ scaleLog T := by
    unfold scaleLog
    have := Real.log_le_log hT0 (show T ≤ 4 * T by linarith only [hT])
    linarith only [this]
  obtain ⟨hα1, -⟩ := slope_bounds (by linarith only [hT]) (by linarith only [hscale, hlog]) hxlo hxhi
  set α := (horizontalSlope x).re with hα
  have hαL : L / 8 ≤ α := by linarith only [hα1, hscale]
  have hα1000 : 1000 ≤ α := by linarith only [hαL, hlog]
  have hα0 : 0 < α := by linarith only [hα1000]
  have hτ8 : τ ≤ 1 / 8 := by nlinarith only [h8, hα1000, hτ]
  have hτα : τ ≤ 1 / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hαL hτ.le
    linarith only [h1, h8]
  have hY : |x - X| < R₀ := by linarith only [hx, hR₀pos]
  have hx200 : 200 ≤ x := by linarith only [hxlo, hT]
  have hR₀α : q ^ 4 / 8 ≤ R₀ * α := by
    have h3 := mul_le_mul_of_nonneg_left hαL hR₀pos.le
    refine le_trans (le_of_eq ?_) h3
    rw [hR₀]
    field_simp
  have hq16 : (10 : ℝ) ^ 16 ≤ q ^ 4 := by
    norm_num at hq4 ⊢
    exact hq4
  have hu₀α : 480000 ≤ 2 * τ * α * α := by
    have h3 := mul_le_mul_of_nonneg_right h7 hα0.le
    nlinarith only [h3, hR₀α, hq16]
  have hkeep (u : ℝ) (hu : 2 * R₀ ≤ u) : xiLine x u ≠ 0 :=
    xiLine_ne_zero_of_keepsAway hR₀pos (hK.keepsAway hY.le) hu
  -- the comparison of the two halves
  have hlt (y' : ℝ) (hy' : 0 < y') (hy2 : y' ≤ 1 / 2) :
      ‖halfGaussTransform τ (xiLine x) (-y')‖ < ‖halfGaussTransform τ (xiLine x) y'‖ := by
    by_cases hnear : y' ≤ 6 / α
    · obtain ⟨j, hR16, hR₀R, hu₁, hu₂, hB0, hB400, hq', hRα⟩ := exists_scale_of_saddle (τ := τ) (u := 2 * τ * α) hq hlog
        hαL hτ le_rfl (by linarith only [h7, hR₀pos]) (by linarith only [h8])
      set R := critR q L j with hRdef
      set B := critB q L j with hBdef
      have hR : 0 < R := by linarith only [hR₀R, hR₀pos]
      have hB1 : 0 < B + 1 := by linarith only [hB0]
      have hE := model_le_tenth hB1.le hτ hq'
      have hE0 := gaussianSaddleModelError_nonneg (t := τ) hB1.le
      have h6α : 6 / α ≤ R / 100 := by
        rw [div_le_div_iff₀ hα0 (by norm_num)]
        nlinarith only [hRα]
      refine norm_lt_norm_of_re_mul_conj_pos (b := 6 / α) (fun v _ => hasDerivAt_halfGaussTransform hτ
        (continuous_xiLine x) (integrable_exp_mul_norm_xiLine hτ x) v) ?_ hy' hnear
      intro v hv
      have hv' : |v| ≤ 6 / α := abs_le.mpr hv
      have hu1 : 9 * R / 4 ≤ v + 2 * τ * α := by linarith only [hu₁, hv.1, h6α, hR]
      have hu3 : v + 2 * τ * α ≤ 24 * R / 5 := by linarith only [hu₂, hv.2, h6α, hR]
      have huβ : 9 * R / 4 * (α / 2) ≤ (v + 2 * τ * α) * α :=
        mul_le_mul hu1 (by linarith only [hα0]) (by positivity) (by linarith only [hu1, hR])
      have hRα' : 9 * R / 4 * (α / 2) = 9 / 8 * (R * α) := by ring
      have hest := source_estimates hR₀pos hR16 hR₀R hK (hdata j hR16) hY hx200 hτ (by linarith only [hα1000]) rfl hu1 hu3
        (by linarith only [hv', h6α, hu1, hR]) hB1 (by linarith only [hB400, hB1, hα1000])
        (by linarith only [huβ, hRα', hRα])
      have hδ : Real.exp (-((v + 2 * τ * α) * α / 40)) ≤ 1 / 12000 :=
        exp_neg_le_of_le (by norm_num) (by linarith only [huβ, hRα', hRα])
      have hPpos : 0 < ‖xiLine x (v + 2 * τ * α)‖ * Real.exp (-(τ * α ^ 2)) :=
        mul_pos (norm_pos_iff.mpr (hkeep _ (by linarith only [hu1, hR₀R, hR₀pos]))) (Real.exp_pos _)
      refine re_mul_conj_pos_of_estimates (M := xiLine x (v + 2 * τ * α) *
          Complex.exp (-(((v + 2 * τ * α : ℝ) : ℂ) * horizontalSlope x)) *
          Complex.exp (v * horizontalSlope x + τ * horizontalSlope x ^ 2))
        (a := horizontalSlope x) (P := ‖xiLine x (v + 2 * τ * α)‖ * Real.exp (-(τ * α ^ 2))) hPpos hα0 ?_ ?_ ?_
      · refine hest.1.trans (mul_le_mul_of_nonneg_left ?_ hPpos.le)
        linarith only [hE, hδ]
      · have h1 := norm_main_eq (t := τ) (X := x) (y := v) (xiLine x (v + 2 * τ * α))
        rw [← hα] at h1
        rw [h1]
        exact (by
          have h2 := mul_le_mul_of_nonneg_left (gaussPhase_ge hτ8 hτ) hPpos.le
          linarith only [h2])
      · refine hest.2.trans (mul_le_mul_of_nonneg_left ?_ hPpos.le)
        rw [← hα]
        have h3 : (B + 1) * (1 + gaussianSaddleModelError (B + 1) τ) ≤ (α / 400) * (11 / 10) :=
          mul_le_mul (by linarith only [hB400]) (by linarith only [hE]) (by linarith only [hE0]) (by positivity)
        have h4 := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 60 * α by positivity)
        linarith only [h3, h4, hα0]
    · have hfarα : 6 / α < y' := not_le.mp hnear
      set u := y' + 2 * τ * α with hu
      have hu0 : 0 < u := by positivity
      have hτu : 2 * τ * α ≤ u := by linarith only [hu, hy']
      have hΛ : 200 ≤ (u - y') * α := by
        rw [hu, add_sub_cancel_left]
        linarith only [hu₀α]
      have hδ' : 480000 ≤ u * α := by
        have h3 := mul_le_mul_of_nonneg_right hτu hα0.le
        linarith only [h3, hu₀α]
      have hfar : 4 ≤ u / 3 * y' / τ := by
        rw [le_div_iff₀ hτ]
        have h3 : 6 ≤ y' * α := by
          rw [div_lt_iff₀ hα0] at hfarα
          exact hfarα.le
        have h4 : 2 * τ * α * y' ≤ u * y' := mul_le_mul_of_nonneg_right hτu hy'.le
        have h5 : 2 * τ * 6 ≤ 2 * τ * (y' * α) := mul_le_mul_of_nonneg_left h3 (by positivity)
        nlinarith only [h4, h5]
      have h2R₀ : 2 * R₀ ≤ u := by linarith only [h7, hτu, hR₀pos]
      by_cases hu7 : u ≤ 1 / 7
      · obtain ⟨j, hR16, hR₀R, hu₁, hu₂, hB0, hB400, hq', hRα⟩ := exists_scale_of_saddle (τ := τ) (u := u) hq hlog hαL hτ
          hτu (by linarith only [h7, hτu, hR₀pos]) hu7
        have hB1 : 0 < critB q L j + 1 := by linarith only [hB0]
        have hR : 0 < critR q L j := by linarith only [hR₀R, hR₀pos]
        obtain ⟨h1, h2, h3⟩ := source_hyps_of_data (u := u) hR₀pos hR16 hR₀R hK (hdata j hR16) hY hx200
          (by linarith only [hu₁, hR]) (by linarith only [hu₂, hR])
        exact norm_opposite_lt_of_source hτ hτ8 (by linarith only [hα1000]) hy' rfl hu0 hB1
          (by linarith only [hB400, hB1, hα1000]) hΛ hq' hδ' hfar h1 h2 h3 (hkeep u h2R₀)
      · obtain ⟨t', ht', hxt⟩ := htyp
        set B₁ := typicalXiSlopeError (1 / 128) T with hB₁
        have hB₁pos : 0 < B₁ := typicalXiSlopeError_pos (by linarith only [hT])
        have hu1 : 1 / 7 < u := not_le.mp hu7
        obtain ⟨h1, h2, h3⟩ := source_hyps_of_typical ht' (by norm_num) (by norm_num) (by linarith only [hT]) hR₀pos hK hY
          hx200 hxt hu0 (by linarith only [hu1]) (by linarith only [hu1, hR₀small])
          (by linarith only [hu, hy2, h8])
        have hB100 : 100 * B₁ ≤ α := by
          nlinarith only [hsmall, hαL, hlog, sq_nonneg (25 * B₁ - 2)]
        have hq' : B₁ * Real.sqrt τ ≤ 1 / 200 := by
          have h4 : (B₁ * Real.sqrt τ) ^ 2 ≤ (1 / 200) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hτ.le]
            have h5 := mul_le_mul_of_nonneg_left hτα (sq_nonneg B₁)
            refine h5.trans ?_
            rw [mul_one_div, div_le_iff₀ (by positivity)]
            nlinarith only [hsmall]
          exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp h4
        exact norm_opposite_lt_of_source hτ hτ8 (by linarith only [hα1000]) hy' rfl hu0 hB₁pos hB100 hΛ hq' hδ' hfar
          h1 h2 h3 (hkeep u h2R₀)
  rw [show riemannHeat τ ((x : ℂ) + I * y) = _ from riemannHeat_eq_halfGaussAverage hτ x y]
  apply add_conj_ne_zero_of_norm_ne
  have hy' := abs_le.mp hy
  rcases lt_or_gt_of_ne hy0 with hneg | hpos0
  · have h := hlt (-y) (by linarith only [hneg]) (by linarith only [hy'.1])
    rw [neg_neg] at h
    exact ne_of_gt h
  · exact ne_of_lt (hlt y hpos0 hy'.2)

/-- **The zeros are real at the critical scale.** For every `δ > 0` there is `κ > 0` such that for all large `T`, outside a set of `X ∈ [T, 2T]` of measure at most `δT`, every zero `z` of `H_t` with `|Re z − X| ≤ κ/(2 log T)` and `t log(Re z/2π) ≥ 7κ/log T` is real. -/
theorem exists_zeros_real_at_critical_scale :
    ∀ δ : ℝ, 0 < δ → ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ ∀ (t : ℝ) (z : ℂ), 0 < t → riemannHeat t z = 0 →
          |z.re - X| ≤ κ / (2 * Real.log T) → 7 * κ / Real.log T ≤ t * Real.log (z.re / (2 * Real.pi)) →
          z.im = 0} ≤ ENNReal.ofReal (δ * T) := by
  obtain ⟨A, hA, hbad⟩ := exists_volume_not_criticalGood_le
  intro δ hδ
  set q : ℝ := max ((10 : ℝ) ^ 4) (2 * A / δ + 1) with hq
  have hq1 : (10 : ℝ) ^ 4 ≤ q := le_max_left _ _
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hq11 : (1 : ℝ) ≤ q := le_trans (by norm_num) hq1
  have hqA : 2 * A ≤ δ * q ^ 2 := by
    have h1 : 2 * A / δ + 1 ≤ q := le_max_right _ _
    have h2 : 2 * A / δ ≤ q := by linarith only [h1]
    rw [div_le_iff₀ hδ] at h2
    have h3 : q ≤ q ^ 2 := le_self_pow₀ hq11 (by norm_num)
    nlinarith only [h2, h3, hδ]
  have hη : (0 : ℝ) < 1 / 128 := by norm_num
  have hη8 : (1 : ℝ) / 128 ≤ 1 / 8 := by norm_num
  refine ⟨q ^ 4, by positivity, ?_⟩
  filter_upwards [hbad q hq1, eventually_volume_not_zetaPolylogTypicalWindow_le hη (show 0 < δ / 2 by positivity),
    eventually_riemannHeat_zeros_real_of_zetaPolylogTypical hη hη8, eventually_typicalSlope_small,
    eventually_ge_atTop (1100 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 6 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (q ^ 4)]
    with T hv1 hv2 hfuture hsmall hT hlog hlogq
  have hT0 : 0 < T := by linarith only [hT]
  have hcover : {X | X ∈ Icc T (2 * T) ∧ ¬ ∀ (t : ℝ) (z : ℂ), 0 < t → riemannHeat t z = 0 →
      |z.re - X| ≤ q ^ 4 / (2 * Real.log T) → 7 * q ^ 4 / Real.log T ≤ t * Real.log (z.re / (2 * Real.pi)) →
      z.im = 0} ⊆ {X | X ∈ Icc T (2 * T) ∧ ¬ CriticalGood q T X} ∪
        {X | X ∈ Icc T (2 * T) ∧ ¬ zetaPolylogTypicalWindow (1 / 128) T X} := by
    rintro X ⟨hXT, hprop⟩
    by_contra hcon
    rw [mem_union, not_or] at hcon
    have hgood : CriticalGood q T X := by
      by_contra h
      exact hcon.1 ⟨hXT, h⟩
    have hwin : zetaPolylogTypicalWindow (1 / 128) T X := by
      by_contra h
      exact hcon.2 ⟨hXT, h⟩
    refine hprop fun t z ht hz hre h7 => ?_
    set L := Real.log T with hL
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hlog
    have hre' : |z.re - X| ≤ q ^ 4 / L / 2 := by
      refine hre.trans (le_of_eq ?_)
      field_simp
    have h7' : 7 * (q ^ 4 / L) ≤ t * Real.log (z.re / (2 * Real.pi)) := by
      rw [mul_div_assoc'] 
      exact h7
    have hslope : 2 * t * (horizontalSlope z.re).re = t * Real.log (z.re / (2 * Real.pi)) := by
      rw [horizontalSlope_re]
      ring
    have hqL : q ^ 4 / L ≤ 1 := by
      rw [div_le_one hL0]
      exact hlogq
    obtain ⟨t', ht', hzt⟩ := hwin z.re (by
      have := abs_le.mp hre'
      rw [abs_le]
      constructor <;> linarith only [this.1, this.2, hqL])
    rcases le_or_gt (t * Real.log (z.re / (2 * Real.pi))) (1 / 8) with h8 | h8
    · by_contra him
      refine riemannHeat_ne_zero_of_critical hq1 hT hlog hXT hgood ⟨t', ht', hzt⟩ hsmall hre' ht (by rw [hslope]; exact h7')
        (by rw [hslope]; exact h8) him (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht.le hz) ?_
      have hz' : (z.re : ℂ) + I * z.im = z := by
        apply Complex.ext <;> simp
      rw [hz']
      exact hz
    · refine hfuture t' ht' z.re hzt t ht ?_ z rfl hz
      rw [← hslope] at h8
      linarith only [h8]
  refine (measure_mono hcover).trans ((measure_union_le _ _).trans ((add_le_add hv1 hv2).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : A * T / q ^ 2 ≤ δ / 2 * T := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hqA hT0.le]
  linarith only [h1]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
