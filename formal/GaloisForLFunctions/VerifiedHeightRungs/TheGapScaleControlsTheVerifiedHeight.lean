import GaloisForLFunctions.VerifiedHeightRungs.WindowEntries
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MostHeightsAreWeilPositiveAtSmallAperture

/-!
# The gap scale in the verified window height

At the interpolation spacing the gap scale is the maximum of a linear term
and an explicit multiple of `a^(4/3)`. The exponential branch of the gap
height has leading exponent `138 exp Y`, where `Y` is that scale.
-/

open Complex MeasureTheory Real Set Filter Topology
open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.VerifiedHeightRungs

/-- The coefficient of `a^(4/3)` in the gap scale at the interpolation spacing. -/
def windowHeightInnerCoefficient : ℝ :=
  (32 * (400 * gapMass) ^ 2 * 5760 * (18 * 48 ^ 4) ^ 4 / gapEnergy) ^ ((1 : ℝ) / 3)

theorem windowHeightInnerCoefficient_pos : 0 < windowHeightInnerCoefficient := by
  have hm := gapMass_pos
  have hE := gapEnergy_pos
  unfold windowHeightInnerCoefficient
  positivity

/-- The interpolation spacing makes the gap scale grow like `a^(4/3)`. -/
theorem gapScale_nodeStep_eq {a : ℝ} (ha : 0 < a) :
    gapScale (nodeStep a / 2) =
      max (18 * 48 ^ 4 * a) (windowHeightInnerCoefficient * a ^ ((4 : ℝ) / 3)) := by
  have hE := gapEnergy_pos
  have hm := gapMass_pos
  let c : ℝ := 18 * 48 ^ 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hs : nodeStep a / 2 = 1 / (c * a) := by
    dsimp [nodeStep, c]
    field_simp
    ring
  have hscale : 32 * (400 * gapMass) ^ 2 * 5760 /
      ((nodeStep a / 2) ^ 4 * gapEnergy) =
      (32 * (400 * gapMass) ^ 2 * 5760 * c ^ 4 / gapEnergy) * a ^ 4 := by
    rw [hs]
    field_simp
  have hpow : (a ^ 4) ^ ((1 : ℝ) / 3) = a ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    norm_num
  rw [gapScale, hscale, hs, one_div_one_div]
  congr 1
  rw [Real.mul_rpow (by positivity) (by positivity), hpow]
  rfl

/-- Eventually the `a^(4/3)` branch is the exact gap scale. -/
theorem eventually_gapScale_nodeStep_eq :
    ∀ᶠ a : ℝ in atTop, gapScale (nodeStep a / 2) =
      windowHeightInnerCoefficient * a ^ ((4 : ℝ) / 3) := by
  have hC := windowHeightInnerCoefficient_pos
  have hg := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_ge_atTop
    (18 * 48 ^ 4 / windowHeightInnerCoefficient)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hg] with a ha hg
  rw [gapScale_nodeStep_eq ha, max_eq_right]
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hC).mp hg) ha.le
  rw [show (4 : ℝ) / 3 = 1 / 3 + 1 by norm_num,
    Real.rpow_add ha, Real.rpow_one]
  nlinarith only [hm]

theorem tendsto_gapScale_nodeStep_atTop :
    Tendsto (fun a : ℝ => gapScale (nodeStep a / 2)) atTop atTop := by
  have h := Tendsto.const_mul_atTop windowHeightInnerCoefficient_pos
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 3))
  exact h.congr' (eventually_gapScale_nodeStep_eq.mono fun _ ha => ha.symm)

private theorem interpolationStep_le_one {a : ℝ} (ha : 1 ≤ a) : nodeStep a ≤ 1 := by
  unfold nodeStep
  have hd : (1 : ℝ) ≤ 9 * 48 ^ 4 * a := by nlinarith only [ha]
  simpa only [one_div_one] using one_div_le_one_div_of_le zero_lt_one hd

private theorem twice_aperture_le_gapScale {a : ℝ} (ha : 0 < a) :
    2 * a ≤ gapScale (nodeStep a / 2) := by
  rw [gapScale_nodeStep_eq ha]
  exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 18 * 48 ^ 4) ha.le).trans
    (le_max_left _ _)

/-- The leading coefficient of the gap scale at the interpolation spacing. -/
theorem tendsto_gapScale_nodeStep_div_rpow :
    Tendsto (fun a : ℝ => gapScale (nodeStep a / 2) / a ^ ((4 : ℝ) / 3))
      atTop (𝓝 windowHeightInnerCoefficient) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gapScale_nodeStep_eq, eventually_gt_atTop (0 : ℝ)] with a ha ha0
  rw [ha, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos ha0 _).ne']

/-- The coefficient `138` combines the archimedean horizon and the rank-two energy. -/
theorem gapHeight_eq_explicit (σ : ℝ) :
    gapHeight σ =
      max (128 * Real.exp (138 * Real.exp (gapScale σ) -
        2 * Real.exp (-gapScale σ) - 4 * gapScale σ + 20))
        (gapTail (gapScale σ) / (gapScale σ * gapEnergy)) := by
  have hs : Real.sqrt (Real.exp (2 * gapScale σ)) = Real.exp (gapScale σ) := by
    have he : Real.exp (2 * gapScale σ) = Real.exp (gapScale σ) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  unfold gapHeight horizonExponent pairEnergy
  rw [hs]
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, div_one]
  rw [Real.sinh_eq]
  congr 3 <;> ring

/-- The auxiliary horizon in `winT₁` is singly exponential in the aperture. -/
theorem winE_eq_exp (a : ℝ) : winE a = 10 + 68 * Real.exp (a + 2) := by
  have hs : Real.sqrt (Real.exp (2 * (a + 2))) = Real.exp (a + 2) := by
    have he : Real.exp (2 * (a + 2)) = Real.exp (a + 2) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  unfold winE horizonExponent
  rw [hs] <;> ring

theorem winE_pos (a : ℝ) : 0 < winE a := by rw [winE_eq_exp]; positivity

theorem four_le_winT₁ (a : ℝ) : 4 ≤ winT₁ a := by
  have hE := winE_pos a
  have he := Real.one_le_exp (show 0 ≤ winE a + 2 * Real.pi by positivity)
  dsimp [winT₁]
  linarith only [he]

theorem winE_le_winT₁ (a : ℝ) : winE a ≤ winT₁ a := by
  have he := Real.add_one_le_exp (winE a + 2 * Real.pi)
  have hp := Real.exp_pos (winE a + 2 * Real.pi)
  have hπ := Real.pi_pos
  dsimp [winT₁]
  linarith only [he, hp, hπ]

theorem aperture_le_winT₁ {a : ℝ} (ha : 0 ≤ a) : a ≤ winT₁ a := by
  apply le_trans _ (winE_le_winT₁ a)
  rw [winE_eq_exp]
  have he := Real.add_one_le_exp (a + 2)
  linarith only [he, ha]

theorem one_le_winD₀ (a : ℝ) : 1 ≤ winD₀ a := by
  have hE := winE_pos a
  unfold winD₀
  have hh : 0 ≤ (1 + winT₁ a ^ 2) * (winE a / (2 * Real.pi)) := by positivity
  linarith only [hh]

/-- The density factor is bounded by a fixed power of the auxiliary horizon. -/
theorem winD₀_le_winT₁_pow_four (a : ℝ) : winD₀ a ≤ winT₁ a ^ 4 := by
  let T := winT₁ a
  have hT4 : 4 ≤ T := four_le_winT₁ a
  have hT : 0 ≤ T := by linarith only [hT4]
  have hE := winE_pos a
  have hET : winE a ≤ T := winE_le_winT₁ a
  have hπ : 1 ≤ 2 * Real.pi := by have hp := Real.pi_gt_three; linarith only [hp]
  have hdiv : (1 + T ^ 2) * winE a / (2 * Real.pi) ≤ (1 + T ^ 2) * T := by
    refine (div_le_self (mul_nonneg (by positivity) hE.le) hπ).trans ?_
    exact mul_le_mul_of_nonneg_left hET (by positivity)
  have h23 : T ^ 2 ≤ T ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ T by linarith only [hT4]) (sq_nonneg T)
    nlinarith only [hh]
  have h12 : 1 + T ≤ T ^ 2 := by
    have hh := mul_nonneg (show 0 ≤ T - 2 by linarith only [hT4]) (show 0 ≤ T + 1 by positivity)
    nlinarith only [hh]
  have h34 : 2 * T ^ 3 ≤ T ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left (show 2 ≤ T by linarith only [hT4]) (pow_nonneg hT 3)
    nlinarith only [hh]
  unfold winD₀
  change 1 + (1 + T ^ 2) * (winE a / (2 * Real.pi)) ≤ T ^ 4
  rw [← mul_div_assoc]
  nlinarith only [hdiv, h12, h23, h34]

/-- The logarithm of `winT₁` is `O(exp a)` with an explicit coefficient. -/
theorem log_winT₁_le_exp {a : ℝ} (ha : 0 ≤ a) :
    Real.log (winT₁ a) ≤
      (Real.log 4 + 10 + 2 * Real.pi + 68 * Real.exp 2) * Real.exp a := by
  rw [winT₁, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, winE_eq_exp, Real.exp_add]
  have hc : 0 ≤ Real.log 4 + 10 + 2 * Real.pi := by positivity
  have hm := mul_le_mul_of_nonneg_left (Real.one_le_exp ha) hc
  nlinarith only [hm]

private theorem deriv_deriv_ofReal_packet {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    deriv (deriv (fun u => (g u : ℂ))) = fun u => ((deriv (deriv g) u : ℝ) : ℂ) := by
  have hd := hg.differentiable (by norm_num)
  have hd' := (contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (1 + 1) g from hg)).2.2.differentiable (by norm_num)
  have h1 : deriv (fun u => (g u : ℂ)) = fun u => ((deriv g u : ℝ) : ℂ) :=
    funext fun u => (hd u).hasDerivAt.ofReal_comp.deriv
  rw [h1]
  exact funext fun u => (hd' u).hasDerivAt.ofReal_comp.deriv

/-- Dilation multiplies the mass by `Y` and the second-derivative mass by `Y⁻¹`. -/
theorem gapTail_dilate {Y : ℝ} (hY : 0 < Y) :
    gapTail Y = (4 * (Y * (∫ u, ‖gapTestC 1 u‖) +
      Y⁻¹ * (∫ u, ‖deriv (deriv (gapTestC 1)) u‖))) ^ 2 := by
  have h0 : (∫ u, ‖gapTestC Y u‖) = Y * (∫ u, ‖gapTestC 1 u‖) := by
    simp only [gapTestC, gapTest, div_one]
    rw [Measure.integral_comp_div (fun u => ‖(sinhTestWeight 1 u : ℂ)‖) Y,
      abs_of_pos hY, smul_eq_mul]
  have hd : deriv (deriv (gapTestC Y)) =
      fun u => ((Y⁻¹ ^ 2 * deriv (deriv (sinhTestWeight 1)) (u / Y) : ℝ) : ℂ) := by
    rw [show gapTestC Y = fun u => (gapTest Y u : ℂ) from rfl,
      deriv_deriv_ofReal_packet (gapTest_contDiff Y)]
    have h := ArithmeticCastelnuovoSeveri.deriv_deriv_dilate (sinhTestWeight_contDiff 1) Y
    exact congrArg (fun f : ℝ → ℝ => fun u => (f u : ℂ)) h
  have hb : deriv (deriv (gapTestC 1)) =
      fun u => ((deriv (deriv (sinhTestWeight 1)) u : ℝ) : ℂ) := by
    rw [show gapTestC 1 = (fun u => (sinhTestWeight 1 u : ℂ)) by
      funext u
      simp only [gapTestC, gapTest, div_one]]
    exact deriv_deriv_ofReal_packet (sinhTestWeight_contDiff 1)
  have h2 : (∫ u, ‖deriv (deriv (gapTestC Y)) u‖) =
      Y⁻¹ * (∫ u, ‖deriv (deriv (gapTestC 1)) u‖) := by
    rw [hd, hb]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg Y⁻¹)]
    rw [integral_const_mul, Measure.integral_comp_div
      (fun u => |deriv (deriv (sinhTestWeight 1)) u|) Y,
      abs_of_pos hY, smul_eq_mul]
    field_simp
  rw [gapTail, h0, h2]

/-- Above unit scale the gap-test tail is only quadratic. -/
theorem gapTail_le_quadratic {Y : ℝ} (hY : 1 ≤ Y) :
    gapTail Y ≤ Y ^ 2 * gapTail 1 := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hYi : Y⁻¹ ≤ Y := (inv_le_one_of_one_le₀ hY).trans hY
  have hsecond : 0 ≤ ∫ u, ‖deriv (deriv (gapTestC 1)) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hmass : 0 ≤ ∫ u, ‖gapTestC 1 u‖ := integral_nonneg fun _ => norm_nonneg _
  rw [gapTail_dilate hY0, gapTail]
  have hm := mul_le_mul_of_nonneg_right hYi hsecond
  have hh : 4 * (Y * (∫ u, ‖gapTestC 1 u‖) +
      Y⁻¹ * (∫ u, ‖deriv (deriv (gapTestC 1)) u‖)) ≤
      Y * (4 * ((∫ u, ‖gapTestC 1 u‖) + ∫ u, ‖deriv (deriv (gapTestC 1)) u‖)) := by
    linarith only [hm]
  have hp := pow_le_pow_left₀ (by positivity) hh 2
  simpa only [mul_pow] using hp

/-- Once the scale exceeds a fixed constant, the exponential branch determines the gap height. -/
theorem gapHeight_eq_main_of_large_scale {σ : ℝ}
    (hY : 1 ≤ gapScale σ) (hbig : 4 * (gapTail 1 / gapEnergy) ≤ gapScale σ) :
    gapHeight σ = 128 * Real.exp (138 * Real.exp (gapScale σ) -
      2 * Real.exp (-gapScale σ) - 4 * gapScale σ + 20) := by
  let Y := gapScale σ
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hE := gapEnergy_pos
  have htail : gapTail Y / (Y * gapEnergy) ≤ (gapTail 1 / gapEnergy) * Y := by
    calc
      _ ≤ (Y ^ 2 * gapTail 1) / (Y * gapEnergy) :=
        div_le_div_of_nonneg_right (gapTail_le_quadratic hY) (by positivity)
      _ = _ := by field_simp
  have hquad : Y ^ 2 ≤ 4 * Real.exp Y := by
    have hh0 := Real.add_one_le_exp (Y / 2)
    have hh : 1 + Y / 2 ≤ Real.exp (Y / 2) := by linarith only [hh0]
    have hh2 := pow_le_pow_left₀ (by positivity) hh 2
    have he : Real.exp (Y / 2) ^ 2 = Real.exp Y := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he] at hh2
    nlinarith only [hh2, hY0]
  have htailExp : gapTail Y / (Y * gapEnergy) ≤ Real.exp Y := by
    have hm := mul_le_mul_of_nonneg_right hbig hY0.le
    change 4 * (gapTail 1 / gapEnergy) * Y ≤ Y * Y at hm
    nlinarith only [htail, hm, hquad]
  have hmainExp : Real.exp Y ≤
      128 * Real.exp (138 * Real.exp Y - 2 * Real.exp (-Y) - 4 * Y + 20) := by
    have he := Real.add_one_le_exp Y
    have hn : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hY0])
    have hg : Y ≤ 138 * Real.exp Y - 2 * Real.exp (-Y) - 4 * Y + 20 := by
      linarith only [he, hn, hY0]
    exact (Real.exp_le_exp.mpr hg).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le (by norm_num))
  rw [gapHeight_eq_explicit, max_eq_left (htailExp.trans hmainExp)]

/-- At large scale the gap height dominates a double exponential with coefficient one. -/
theorem exp_exp_scale_le_gapHeight {σ : ℝ} (hY : 1 ≤ gapScale σ)
    (hbig : 4 * (gapTail 1 / gapEnergy) ≤ gapScale σ) :
    Real.exp (Real.exp (gapScale σ)) ≤ gapHeight σ := by
  rw [gapHeight_eq_main_of_large_scale hY hbig]
  have he := Real.add_one_le_exp (gapScale σ)
  have hn : Real.exp (-gapScale σ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hY])
  have hp := Real.exp_pos (gapScale σ)
  have harg : Real.exp (gapScale σ) ≤ 138 * Real.exp (gapScale σ) -
      2 * Real.exp (-gapScale σ) - 4 * gapScale σ + 20 := by
    linarith only [he, hn, hp]
  exact (Real.exp_le_exp.mpr harg).trans
    (le_mul_of_one_le_left (Real.exp_pos _).le (by norm_num))

/-- The interpolation count eventually uses only the gap-height branch. -/
theorem eventually_winN_eq_ceil_gapHeight :
    ∀ᶠ a : ℝ in atTop, winN a = ⌈gapHeight (nodeStep a / 2) / nodeStep a⌉₊ := by
  let C := Real.log 4 + 10 + 2 * Real.pi + 68 * Real.exp 2
  let K := Real.log 8000 + 6 * C
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (4 * (gapTail 1 / gapEnergy)),
    Real.tendsto_exp_atTop.eventually_ge_atTop K] with a ha habig haK
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hs : 0 < nodeStep a := nodeStep_pos ha0
  have hs1 : nodeStep a ≤ 1 := interpolationStep_le_one ha
  have hY : 2 * a ≤ gapScale (nodeStep a / 2) := twice_aperture_le_gapScale ha0
  have hY1 : 1 ≤ gapScale (nodeStep a / 2) := by linarith only [ha, hY]
  have hbig : 4 * (gapTail 1 / gapEnergy) ≤ gapScale (nodeStep a / 2) := by
    linarith only [habig, hY, ha0]
  have hG := exp_exp_scale_le_gapHeight hY1 hbig
  have hT1 : 1 ≤ winT₁ a := by have hh := four_le_winT₁ a; linarith only [hh]
  have hT0 : 0 < winT₁ a := zero_lt_one.trans_le hT1
  have hD0 : 0 ≤ winD₀ a := zero_le_one.trans (one_le_winD₀ a)
  have hlogP : Real.log (8000 * winT₁ a ^ 6) ≤ K * Real.exp a := by
    rw [Real.log_mul (by norm_num : (8000 : ℝ) ≠ 0) (pow_ne_zero _ hT0.ne'), Real.log_pow]
    have hT := log_winT₁_le_exp ha0.le
    have hlog8 : 0 ≤ Real.log 8000 := by positivity
    have h8 := mul_le_mul_of_nonneg_left (Real.one_le_exp ha0.le) hlog8
    dsimp [K, C] at *
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hT, h8]
  have hP : 8000 * winT₁ a ^ 6 ≤ gapHeight (nodeStep a / 2) := by
    have hm := mul_le_mul_of_nonneg_right haK (Real.exp_pos a).le
    have he : Real.exp a * Real.exp a ≤ Real.exp (gapScale (nodeStep a / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hY])
    calc
      _ = Real.exp (Real.log (8000 * winT₁ a ^ 6)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (Real.exp (gapScale (nodeStep a / 2))) :=
        Real.exp_le_exp.mpr (hlogP.trans (hm.trans he))
      _ ≤ _ := hG
  have hTg : winT₁ a ≤ gapHeight (nodeStep a / 2) := by
    have hp := le_self_pow₀ hT1 (by norm_num : (6 : ℕ) ≠ 0)
    have hp0 : 0 ≤ winT₁ a ^ 6 := pow_nonneg hT0.le _
    nlinarith only [hp, hp0, hP]
  have hother : 8 * a * winT₁ a * winD₀ a * 1000 ≤ gapHeight (nodeStep a / 2) := by
    calc
      _ ≤ 8 * winT₁ a * winT₁ a * (winT₁ a ^ 4) * 1000 := by
        gcongr
        · exact aperture_le_winT₁ ha0.le
        · exact winD₀_le_winT₁_pow_four a
      _ = 8000 * winT₁ a ^ 6 := by ring
      _ ≤ _ := hP
  have hG0 : 0 ≤ gapHeight (nodeStep a / 2) := (Real.exp_pos _).le.trans hG
  have hGdiv : gapHeight (nodeStep a / 2) ≤ gapHeight (nodeStep a / 2) / nodeStep a := by
    apply (le_div_iff₀ hs).mpr
    exact mul_le_of_le_one_right hG0 hs1
  rw [winN, max_eq_right hTg, max_eq_left (hother.trans hGdiv)]

/-- The logarithm of the gap height has leading term `138 exp(gapScale)`. -/
theorem tendsto_log_gapHeight_div_exp {σ : ℝ → ℝ}
    (hY : Tendsto (fun a => gapScale (σ a)) atTop atTop) :
    Tendsto (fun a => Real.log (gapHeight (σ a)) / Real.exp (gapScale (σ a)))
      atTop (𝓝 138) := by
  have hE := Real.tendsto_exp_atTop.comp hY
  have hn := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hY)
  have hneg := hn.div_atTop hE
  have hy : Tendsto (fun a => gapScale (σ a) / Real.exp (gapScale (σ a))) atTop (𝓝 0) := by
    have hh := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hE
    simpa only [Function.comp_def, id_eq, Real.log_exp] using hh
  have hc : Tendsto (fun a => (Real.log 128 + 20) / Real.exp (gapScale (σ a)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hE
  have h := (((tendsto_const_nhds (x := (138 : ℝ))).sub (hneg.const_mul 2)).sub
    (hy.const_mul 4)).add hc
  norm_num only [mul_zero, sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [hY.eventually_ge_atTop 1,
    hY.eventually_ge_atTop (4 * (gapTail 1 / gapEnergy))] with a ha hb
  dsimp only [Function.comp_def]
  rw [gapHeight_eq_main_of_large_scale ha hb,
    Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

/-- The double logarithm of the gap height differs from its scale by `log 138`. -/
theorem tendsto_log_log_gapHeight_sub_scale {σ : ℝ → ℝ}
    (hY : Tendsto (fun a => gapScale (σ a)) atTop atTop) :
    Tendsto (fun a => Real.log (Real.log (gapHeight (σ a))) - gapScale (σ a))
      atTop (𝓝 (Real.log 138)) := by
  have h := tendsto_log_gapHeight_div_exp hY
  have hl := h.log (by norm_num : (138 : ℝ) ≠ 0)
  refine hl.congr' ?_
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 138))] with a ha
  have hp : 0 < Real.log (gapHeight (σ a)) := by
    have hh := (lt_div_iff₀ (Real.exp_pos (gapScale (σ a)))).mp ha
    simpa only [zero_mul] using hh
  rw [Real.log_div hp.ne' (Real.exp_ne_zero _), Real.log_exp]

/-- At interpolation spacing, the refined gap-height constant is `log 138`. -/
theorem tendsto_log_log_gapHeight_nodeStep_sub_rpow :
    Tendsto (fun a : ℝ => Real.log (Real.log (gapHeight (nodeStep a / 2))) -
      windowHeightInnerCoefficient * a ^ ((4 : ℝ) / 3)) atTop (𝓝 (Real.log 138)) := by
  have hY := tendsto_gapScale_nodeStep_atTop
  refine (tendsto_log_log_gapHeight_sub_scale hY).congr' ?_
  filter_upwards [eventually_gapScale_nodeStep_eq] with a ha
  rw [ha]

private theorem positive_gapHeight (σ : ℝ) : 0 < gapHeight σ := by
  rw [gapHeight_eq_explicit]
  exact (mul_pos (by norm_num) (Real.exp_pos _)).trans_le (le_max_left _ _)

theorem tendsto_gapHeight_div_nodeStep_atTop :
    Tendsto (fun a : ℝ => gapHeight (nodeStep a / 2) / nodeStep a) atTop atTop := by
  have hY := tendsto_gapScale_nodeStep_atTop
  have hE := Real.tendsto_exp_atTop.comp hY
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (1 : ℝ), hE.eventually_ge_atTop b,
    hY.eventually_ge_atTop 1, hY.eventually_ge_atTop (4 * (gapTail 1 / gapEnergy))]
    with a ha hb hY1 hbig
  have hs := nodeStep_pos (zero_lt_one.trans_le ha)
  have hg := positive_gapHeight (nodeStep a / 2)
  have he : gapScale (nodeStep a / 2) ≤ Real.exp (gapScale (nodeStep a / 2)) := by
    have hh := Real.add_one_le_exp (gapScale (nodeStep a / 2))
    linarith only [hh]
  have hG := (Real.exp_le_exp.mpr he).trans (exp_exp_scale_le_gapHeight hY1 hbig)
  refine hb.trans (hG.trans ?_)
  apply (le_div_iff₀ hs).mpr
  exact mul_le_of_le_one_right hg.le (interpolationStep_le_one ha)

/-- Rounding the gap-height quotient changes it by a vanishing relative amount. -/
theorem tendsto_winN_div_gapHeight_quotient :
    Tendsto (fun a : ℝ => (winN a : ℝ) / (gapHeight (nodeStep a / 2) / nodeStep a))
      atTop (𝓝 1) := by
  have h := tendsto_nat_ceil_div_atTop.comp tendsto_gapHeight_div_nodeStep_atTop
  refine h.congr' ?_
  filter_upwards [eventually_winN_eq_ceil_gapHeight] with a ha
  simp only [Function.comp_def, ha]

private theorem tendsto_log_aperture_div_exp_scale :
    Tendsto (fun a : ℝ => Real.log a / Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 0) := by
  have hy : Tendsto (fun a : ℝ => gapScale (nodeStep a / 2) /
      Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (Real.tendsto_exp_atTop.comp tendsto_gapScale_nodeStep_atTop)
    simpa only [Function.comp_def, id_eq, Real.log_exp] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hy
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact div_nonneg (Real.log_nonneg ha) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have ha0 := zero_lt_one.trans_le ha
    have hl := Real.log_le_sub_one_of_pos ha0
    have hY := twice_aperture_le_gapScale ha0
    exact div_le_div_of_nonneg_right (by linarith only [hl, hY, ha]) (Real.exp_pos _).le

/-- The ceiling and interpolation spacing preserve the coefficient `138` in `log winN`. -/
theorem tendsto_log_winN_div_exp_scale :
    Tendsto (fun a : ℝ => Real.log (winN a) / Real.exp (gapScale (nodeStep a / 2)))
      atTop (𝓝 138) := by
  have hE := Real.tendsto_exp_atTop.comp tendsto_gapScale_nodeStep_atTop
  have hG := tendsto_log_gapHeight_div_exp tendsto_gapScale_nodeStep_atTop
  have hc : Tendsto (fun a : ℝ => Real.log (9 * 48 ^ 4) /
      Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hE
  have hX : Tendsto (fun a : ℝ => Real.log (gapHeight (nodeStep a / 2) / nodeStep a) /
      Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 138) := by
    have h := (hG.add hc).add tendsto_log_aperture_div_exp_scale
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [Real.log_div (positive_gapHeight _).ne' (nodeStep_pos ha).ne', nodeStep,
      one_div, Real.log_inv,
      Real.log_mul (by norm_num : (9 * 48 ^ 4 : ℝ) ≠ 0) ha.ne']
    ring
  have hratio := tendsto_winN_div_gapHeight_quotient
  have hlogratio := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
  rw [Real.log_one] at hlogratio
  have h := hX.add (hlogratio.div_atTop hE)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hratio.eventually (lt_mem_nhds zero_lt_one)] with a ha hr
  have hXp : 0 < gapHeight (nodeStep a / 2) / nodeStep a :=
    div_pos (positive_gapHeight _) (nodeStep_pos ha)
  have hNp : (0 : ℝ) < winN a := by
    have hh := (lt_div_iff₀ hXp).mp hr
    simpa only [zero_mul] using hh
  dsimp only [Function.comp_def]
  rw [Real.log_div hNp.ne' hXp.ne']
  ring

/-- The interpolation count has the same refined double-log limit as the gap height. -/
theorem tendsto_log_log_winN_sub_rpow :
    Tendsto (fun a : ℝ => Real.log (Real.log (winN a)) -
      windowHeightInnerCoefficient * a ^ ((4 : ℝ) / 3)) atTop (𝓝 (Real.log 138)) := by
  have h := tendsto_log_winN_div_exp_scale
  have hl := h.log (by norm_num : (138 : ℝ) ≠ 0)
  refine hl.congr' ?_
  filter_upwards [eventually_gapScale_nodeStep_eq,
    h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 138))] with a ha hp
  have hNp : 0 < Real.log (winN a) := by
    have hh := (lt_div_iff₀ (Real.exp_pos (gapScale (nodeStep a / 2)))).mp hp
    simpa only [zero_mul] using hh
  rw [Real.log_div hNp.ne' (Real.exp_ne_zero _), Real.log_exp, ha]

private def tailCoefficient : ℝ :=
  (Real.exp 1 * 400 ^ 2) * (24 * 240 * Real.log 3) * 1000

private theorem tailCoefficient_pos : 0 < tailCoefficient := by
  unfold tailCoefficient
  positivity

private theorem winC_eq_tailCoefficient (a : ℝ) :
    winC a = 2 * a * Real.exp a * tailCoefficient := by
  unfold winC tailCoefficient
  ring

private theorem max_horizon_le_winN {a : ℝ} (ha : 1 ≤ a) :
    max (winT₁ a) (gapHeight (nodeStep a / 2)) ≤ (winN a : ℝ) := by
  have ha0 := zero_lt_one.trans_le ha
  have hs := nodeStep_pos ha0
  have hm0 : 0 ≤ max (winT₁ a) (gapHeight (nodeStep a / 2)) :=
    (by have hh := four_le_winT₁ a; linarith only [hh] : 0 ≤ winT₁ a).trans (le_max_left _ _)
  calc
    _ ≤ max (winT₁ a) (gapHeight (nodeStep a / 2)) / nodeStep a := by
      apply (le_div_iff₀ hs).mpr
      exact mul_le_of_le_one_right hm0 (interpolationStep_le_one ha)
    _ ≤ max (max (winT₁ a) (gapHeight (nodeStep a / 2)) / nodeStep a)
        (8 * a * winT₁ a * winD₀ a * 1000) := le_max_left _ _
    _ ≤ _ := Nat.le_ceil _

private theorem windowHeightOfOne_exp_bounds {a : ℝ} (ha : 1 ≤ a)
    (hC : 1 ≤ winC a) (hY : Real.exp (gapScale (nodeStep a / 2)) ≤ (winN a : ℝ)) :
    (2 : ℝ) ^ winN a ≤ windowHeightOfOne a ∧
      windowHeightOfOne a ≤ Real.exp ((tailCoefficient + 1000) * (winN a : ℝ)) := by
  let n : ℝ := winN a
  let D := 8 * winT₁ a * winD₀ a * winK a + 6 * (n + 1) * nodeStep a + 1
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hTN : winT₁ a ≤ n := (le_max_left _ _).trans (max_horizon_le_winN ha)
  have hT4 := four_le_winT₁ a
  have hn1 : 1 ≤ n := by linarith only [hTN, hT4]
  have ha0 := zero_lt_one.trans_le ha
  have haN : a ≤ n := (aperture_le_winT₁ ha0.le).trans hTN
  have hT0 : 0 < winT₁ a := by linarith only [hT4]
  have hD1 := one_le_winD₀ a
  have hD0 : 0 ≤ winD₀ a := zero_le_one.trans hD1
  have hs := nodeStep_pos ha0
  have hs1 := interpolationStep_le_one ha
  have hK0 : 0 < winK a := by unfold winK; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have htail := tailCoefficient_pos
  have hNexp : n ≤ Real.exp n := by
    have hh := Real.add_one_le_exp n
    linarith only [hh]
  have hDexp : winD₀ a ≤ Real.exp (4 * n) := by
    calc
      _ ≤ winT₁ a ^ 4 := winD₀_le_winT₁_pow_four a
      _ ≤ (Real.exp n) ^ 4 := pow_le_pow_left₀ hT0.le (hTN.trans hNexp) _
      _ = _ := by rw [← Real.exp_nat_mul] <;> norm_num
  have h48 : (48 : ℝ) ≤ Real.exp 48 := by
    have hh := Real.add_one_le_exp (48 : ℝ)
    linarith only [hh]
  have hQ : (48 : ℝ) ^ winN a ≤ Real.exp (48 * n) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 48) h48 (winN a)
    rw [← Real.exp_nat_mul] at hh
    simpa only [n, mul_comm] using hh
  have hKexp : winK a ≤ Real.exp (100 * n) := by
    have h4 : 4 * n ≤ Real.exp (4 * n) := by
      have hh := Real.add_one_le_exp (4 * n)
      linarith only [hh]
    have hfront : 2 * (n + 1) ≤ Real.exp (4 * n) := by linarith only [hn1, h4]
    calc
      _ ≤ Real.exp (4 * n) * (Real.exp (48 * n)) ^ 2 := by
        unfold winK
        exact mul_le_mul hfront (pow_le_pow_left₀ (by positivity) hQ 2)
          (sq_nonneg _) (Real.exp_pos _).le
      _ = _ := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hterm : 8 * winT₁ a * winD₀ a * winK a ≤ Real.exp (113 * n) := by
    have h8 : (8 : ℝ) ≤ Real.exp (8 * n) := by
      have hh := Real.add_one_le_exp (8 * n)
      linarith only [hh, hn1]
    calc
      _ ≤ Real.exp (8 * n) * Real.exp n * Real.exp (4 * n) * Real.exp (100 * n) := by
        exact mul_le_mul
          (mul_le_mul (mul_le_mul h8 (hTN.trans hNexp) hT0.le (Real.exp_pos _).le)
            hDexp hD0 (by positivity)) hKexp hK0.le (by positivity)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hlinear : 6 * (n + 1) * nodeStep a ≤ Real.exp (113 * n) := by
    have hh := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 6 * (n + 1) by positivity)
    have he := Real.add_one_le_exp (12 * n)
    have hb : 6 * (n + 1) * nodeStep a ≤ Real.exp (12 * n) := by
      nlinarith only [hh, he, hn1]
    exact hb.trans (Real.exp_le_exp.mpr (by nlinarith only [hn0]))
  have hDupper : D ≤ Real.exp (116 * n) := by
    have h1 : 1 ≤ Real.exp (113 * n) := Real.one_le_exp (by positivity)
    have h3 : (3 : ℝ) ≤ Real.exp (3 * n) := by
      have hh := Real.add_one_le_exp (3 * n)
      linarith only [hh, hn1]
    calc
      D ≤ 3 * Real.exp (113 * n) := by dsimp [D]; linarith only [hterm, hlinear, h1]
      _ ≤ Real.exp (3 * n) * Real.exp (113 * n) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hCupper : winC a ≤ Real.exp ((tailCoefficient + 3) * n) := by
    have h2a : 2 * a ≤ Real.exp (2 * n) := by
      have hh := Real.add_one_le_exp (2 * n)
      linarith only [hh, haN]
    have htailExp : tailCoefficient ≤ Real.exp (tailCoefficient * n) := by
      have hm := mul_le_mul_of_nonneg_left hn1 htail.le
      have hh := Real.add_one_le_exp (tailCoefficient * n)
      linarith only [hm, hh]
    rw [winC_eq_tailCoefficient]
    calc
      _ ≤ Real.exp (2 * n) * Real.exp n * Real.exp (tailCoefficient * n) :=
        mul_le_mul (mul_le_mul h2a (Real.exp_le_exp.mpr haN) (Real.exp_pos _).le
          (Real.exp_pos _).le) htailExp htail.le (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have htailEq : winC a / winB a ^ 8 = winC a * D ^ 8 := by
    unfold winB
    change winC a / (1 / D) ^ 8 = _
    field_simp [hDpos.ne']
  have hQone : 1 ≤ (48 : ℝ) ^ winN a := one_le_pow₀ (by norm_num)
  have hQK : (48 : ℝ) ^ winN a ≤ winK a := by
    have hsq := le_self_pow₀ hQone two_ne_zero
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * (n + 1) by linarith only [hn0])
      (sq_nonneg ((48 : ℝ) ^ winN a))
    change _ ≤ 2 * (n + 1) * ((48 : ℝ) ^ winN a) ^ 2
    nlinarith only [hsq, hm]
  have hKD : winK a ≤ D := by
    have hprod := mul_le_mul (show (1 : ℝ) ≤ winT₁ a by linarith only [hT4]) hD1 zero_le_one hT0.le
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 8 * winT₁ a * winD₀ a by
      nlinarith only [hprod]) hK0.le
    have hl : 0 ≤ 6 * (n + 1) * nodeStep a := by positivity
    dsimp [D]
    linarith only [hm, hl]
  have hDge : 1 ≤ D := (hQone.trans hQK).trans hKD
  constructor
  · apply le_trans _ (le_max_right _ _)
    rw [htailEq]
    calc
      (2 : ℝ) ^ winN a ≤ (48 : ℝ) ^ winN a := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ ≤ D := hQK.trans hKD
      _ ≤ D ^ 8 := le_self_pow₀ hDge (by norm_num)
      _ ≤ winC a * D ^ 8 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (pow_nonneg hDpos.le 8)
  · apply max_le
    · have hm := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 3 * (n + 1) by positivity)
      have he := Real.add_one_le_exp (8 * n)
      have hb : 3 * (n + 1) * nodeStep a + Real.exp (gapScale (nodeStep a / 2)) + 1 ≤
          Real.exp (8 * n) := by nlinarith only [hm, he, hY, hn1]
      exact hb.trans (Real.exp_le_exp.mpr (by nlinarith only [htail, hn0]))
    · rw [htailEq]
      calc
        _ ≤ Real.exp ((tailCoefficient + 3) * n) * (Real.exp (116 * n)) ^ 8 :=
          mul_le_mul hCupper (pow_le_pow_left₀ hDpos.le hDupper 8)
            (pow_nonneg hDpos.le 8) (Real.exp_pos _).le
        _ = Real.exp ((tailCoefficient + 931) * n) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          norm_num <;> ring
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hn0])

/-- The final verified height is exponentially comparable to the interpolation count. -/
theorem eventually_windowHeight_exp_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ a : ℝ in atTop,
      (2 : ℝ) ^ winN a ≤ windowHeight a ∧
        windowHeight a ≤ Real.exp (K * (winN a : ℝ)) := by
  have htail := tailCoefficient_pos
  refine ⟨tailCoefficient + 1000, by positivity, ?_⟩
  have hY := tendsto_gapScale_nodeStep_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / tailCoefficient),
    hY.eventually_ge_atTop 1, hY.eventually_ge_atTop (4 * (gapTail 1 / gapEnergy))]
    with a ha hCa hY1 hYbig
  have ha0 := zero_lt_one.trans_le ha
  have hC : 1 ≤ winC a := by
    have hm := (div_le_iff₀ htail).mp hCa
    have he := mul_le_mul_of_nonneg_left (Real.one_le_exp ha0.le) (mul_nonneg ha0.le htail.le)
    rw [winC_eq_tailCoefficient]
    nlinarith only [hm, he]
  have hscale : gapScale (nodeStep a / 2) ≤ Real.exp (gapScale (nodeStep a / 2)) := by
    have he := Real.add_one_le_exp (gapScale (nodeStep a / 2))
    linarith only [he]
  have hEN : Real.exp (gapScale (nodeStep a / 2)) ≤ (winN a : ℝ) :=
    ((Real.exp_le_exp.mpr hscale).trans (exp_exp_scale_le_gapHeight hY1 hYbig)).trans
      ((le_max_right _ _).trans (max_horizon_le_winN ha))
  rw [windowHeight, max_eq_left ha]
  exact windowHeightOfOne_exp_bounds ha hC hEN

/-- The double logarithm of the final height has leading term `138 exp(gapScale)`. -/
theorem tendsto_log_log_windowHeight_div_exp_scale :
    Tendsto (fun a : ℝ => Real.log (Real.log (windowHeight a)) /
      Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 138) := by
  obtain ⟨K, hK, hb⟩ := eventually_windowHeight_exp_bounds
  have hE := Real.tendsto_exp_atTop.comp tendsto_gapScale_nodeStep_atTop
  have hN := tendsto_log_winN_div_exp_scale
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : Tendsto (fun a : ℝ => (Real.log (winN a) + Real.log (Real.log 2)) /
      Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 138) := by
    have hconst : Tendsto (fun a : ℝ => Real.log (Real.log 2) /
        Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hE
    simpa only [add_zero, add_div] using hN.add hconst
  have hup : Tendsto (fun a : ℝ => (Real.log (winN a) + Real.log K) /
      Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 138) := by
    have hconst : Tendsto (fun a : ℝ => Real.log K /
        Real.exp (gapScale (nodeStep a / 2))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hE
    simpa only [add_zero, add_div] using hN.add hconst
  have hbounds : ∀ᶠ a : ℝ in atTop,
      (Real.log (winN a) + Real.log (Real.log 2)) / Real.exp (gapScale (nodeStep a / 2)) ≤
        Real.log (Real.log (windowHeight a)) / Real.exp (gapScale (nodeStep a / 2)) ∧
      Real.log (Real.log (windowHeight a)) / Real.exp (gapScale (nodeStep a / 2)) ≤
        (Real.log (winN a) + Real.log K) / Real.exp (gapScale (nodeStep a / 2)) := by
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with a ha ha1
    have hTN := (le_max_left _ _).trans (max_horizon_le_winN ha1)
    have hT4 := four_le_winT₁ a
    have hNp : (0 : ℝ) < winN a := by linarith only [hTN, hT4]
    have hHp : 0 < windowHeight a := (pow_pos (by norm_num : (0 : ℝ) < 2) _).trans_le ha.1
    have hlogL := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) ha.1
    rw [Real.log_pow] at hlogL
    have hlogU := Real.log_le_log hHp ha.2
    rw [Real.log_exp] at hlogU
    have hlogHp : 0 < Real.log (windowHeight a) := (mul_pos hNp hc).trans_le hlogL
    have hlo' := Real.log_le_log (mul_pos hNp hc) hlogL
    rw [Real.log_mul hNp.ne' hc.ne'] at hlo'
    have hup' := Real.log_le_log hlogHp hlogU
    rw [Real.log_mul hK.ne' hNp.ne'] at hup'
    exact ⟨div_le_div_of_nonneg_right hlo' (Real.exp_pos _).le,
      div_le_div_of_nonneg_right (by linarith only [hup']) (Real.exp_pos _).le⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- The verified height has triple-exponential order with exact inner coefficient
`windowHeightInnerCoefficient` and refined additive constant `log 138`. -/
theorem tendsto_log_log_log_windowHeight_sub_rpow :
    Tendsto (fun a : ℝ => Real.log (Real.log (Real.log (windowHeight a))) -
      windowHeightInnerCoefficient * a ^ ((4 : ℝ) / 3)) atTop (𝓝 (Real.log 138)) := by
  have h := tendsto_log_log_windowHeight_div_exp_scale
  have hl := h.log (by norm_num : (138 : ℝ) ≠ 0)
  refine hl.congr' ?_
  filter_upwards [eventually_gapScale_nodeStep_eq,
    h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 138))] with a ha hp
  have hHp : 0 < Real.log (Real.log (windowHeight a)) := by
    have hh := (lt_div_iff₀ (Real.exp_pos (gapScale (nodeStep a / 2)))).mp hp
    simpa only [zero_mul] using hh
  rw [Real.log_div hHp.ne' (Real.exp_ne_zero _), Real.log_exp, ha]

end GaloisForLFunctions.VerifiedHeightRungs
