import GaloisForLFunctions.ArithmeticCriticalityTheory.ExplicitSmallApertureCCMGroundEnergyFloor
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper

/-!
# The Markov window past the plastic threshold

On a window below the first prime the full zero form is a jump form with density
`ω(t) − 2cosh(t/2)` (archimedean Lévy density minus pole density) plus one potential
(`PoleConductanceWindowWeilPositivity`):

    Ẑ(F) = ∫_0^∞ (ω(t) − 2cosh(t/2)) I_M(t) dt + ∫ F² [2 ∫ M(y) cosh((x−y)/2) dy − 𝒲M(x)] dx.

The density is nonnegative exactly up to the plastic threshold `log ρ ≈ 0.2812`: with `a = e^{−t/2}`,
`ω(t) ≥ 2cosh(t/2)` is `a⁴ + a⁶ ≥ 1`. Beyond it the jump form is no longer Markov, but its negative
part is small: on `(0.28, 0.292]` the pole density exceeds `ω` by at most `0.07`, and every gauge jump
profile is at most `4 ∫ F²`. The negative density therefore costs at most
`4 · 0.012 · 0.07 · ∫ F²`, which the potential pays.

**Theorem** (`fullZeroForm_ge_of_support_le_pastPlastic`). Every real `F ∈ C²_c` vanishing outside
`[−29/200, 29/200]` satisfies `Ẑ(F) ≥ (1/125) ∫ F²`. Consequently the restricted Weil ground energy has
`μ(A) ≥ 1/125` for every aperture `A ≤ 29/200` (`one_div_125_le_ccmRestrictedWeilGroundEnergy`), and
every contact aperture exceeds `29/200`.

The window is limited by the centre value of the potential: in exact form it is
`ψ(1/4) − log π + 2Ω(R) + 8 sinh(R/2)`, `Ω(x) = ∫_x^∞ ω = artanh(e^{−x/2}) + arctan(e^{−x/2})`, which
vanishes at `R ≈ 0.1526`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Numerical constants -/

/-- Taylor minorant of `e^{−x}`: `e^{−x} ≥ 1 − x + x²/2 − x³/6 + x⁴/24 − x⁵/100` on `[0, 1]`. -/
theorem taylor_le_exp_neg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 100 ≤ Real.exp (-x) := by
  have hx : |(-x)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_neg, abs_of_nonneg h0] at h
  norm_num at h
  have := (abs_le.mp h).1
  nlinarith [this]

/-- `log π < 1.1449`. -/
theorem log_pi_lt_sharp : Real.log Real.pi < 1.1449 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.1449) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h3 : Real.exp 1.1449 = Real.exp 1 * Real.exp 0.1449 := by rw [← Real.exp_add]; norm_num
  have h4 := Real.pi_lt_d4
  rw [h3]
  nlinarith [Real.exp_pos 0.1449, Real.exp_pos 1]

/-- `γ + log π < 1.722116`. -/
theorem two_mul_archConstantReal_lt_sharp : 2 * archConstantReal < 1.722116 := by
  have h1 := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have h2 := log_pi_lt_sharp
  unfold archConstantReal
  linarith

/-- **Below the plastic threshold.** `2cosh(t/2) ≤ ω(t)` for `0 < t ≤ 0.28`: with `a = e^{−t/2}` the
inequality reads `a⁴ + a⁶ ≥ 1`, and `a ≥ e^{−0.14} ≥ 0.8693`. -/
theorem two_mul_cosh_le_archLevyDensity_of_le_plastic {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 0.28) :
    2 * Real.cosh (t / 2) ≤ archLevyDensity t := by
  set a := Real.exp (-t / 2) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlow : 0.8693 ≤ a := by
    have hT := taylor_le_exp_neg (x := 0.14) (by norm_num) (by norm_num)
    have hmono : Real.exp (-0.14) ≤ a := Real.exp_le_exp.mpr (by linarith)
    norm_num at hT
    linarith
  have h46 : 1 ≤ a ^ 4 + a ^ 6 := by
    have e4 := pow_le_pow_left₀ (by norm_num) hlow 4
    have e6 := pow_le_pow_left₀ (by norm_num) hlow 6
    norm_num at e4 e6
    linarith
  have h4 : Real.exp (-2 * t) = a ^ 4 := by
    rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hinv : Real.exp (t / 2) = a⁻¹ := by rw [ha, ← Real.exp_neg]; ring_nf
  have hc : 2 * Real.cosh (t / 2) = a⁻¹ + a := by
    rw [Real.cosh_eq, hinv, show -(t / 2) = -t / 2 by ring]
    ring
  have hden : 0 < 1 - a ^ 4 := by
    have : a ^ 4 < 1 := pow_lt_one₀ ha0.le ha1 (by norm_num)
    linarith
  unfold archLevyDensity
  rw [h4, hc, le_div_iff₀ hden]
  have hab : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0.ne'
  have hb0 : 0 < a⁻¹ := inv_pos.mpr ha0
  nlinarith [mul_pos hb0 ha0, mul_le_mul_of_nonneg_left h46 hb0.le]

/-- **Past the plastic threshold the pole density exceeds `ω` by at most `0.07`** on `(0, 0.292]`. -/
theorem two_mul_cosh_sub_archLevyDensity_le {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 0.292) :
    2 * Real.cosh (t / 2) - archLevyDensity t ≤ 0.07 := by
  have hc : Real.cosh (t / 2) ≤ Real.cosh 0.146 :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_pos (by linarith), abs_of_pos (by norm_num)]; linarith)
  have hp := exp_le_taylor_five (x := 0.146) (by norm_num [abs_of_pos])
  have hm := exp_le_taylor_five (x := -0.146) (by norm_num [abs_of_pos])
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.146)] at hp
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 0.146)] at hm
  norm_num at hp hm
  have hcosh : 2 * Real.cosh 0.146 ≤ 2.0213552 := by
    rw [Real.cosh_eq]
    norm_num
    linarith
  have hnum : 0.8641575 ≤ Real.exp (-t / 2) := by
    have hT := taylor_le_exp_neg (x := 0.146) (by norm_num) (by norm_num)
    have : Real.exp (-(73 / 500)) ≤ Real.exp (-t / 2) := Real.exp_le_exp.mpr (by linarith)
    norm_num at hT
    linarith
  have hden0 : 0 < 1 - Real.exp (-2 * t) := by
    have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden : 1 - Real.exp (-2 * t) ≤ 0.4425008 := by
    have hT := taylor_le_exp_neg (x := 0.584) (by norm_num) (by norm_num)
    have : Real.exp (-(73 / 125)) ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by linarith)
    norm_num at hT
    linarith
  have hω : 0.8641575 / 0.4425008 ≤ archLevyDensity t := by
    unfold archLevyDensity
    exact div_le_div₀ (by linarith) hnum hden0 hden
  norm_num at hω
  linarith

/-- The window killing at radius `73/500`: `−log(1 − e^{−0.292}) ≥ 1.373`. -/
theorem neg_log_window_pastPlastic_ge :
    1.373 ≤ -Real.log (1 - Real.exp (-2 * (73 / 500))) := by
  have hpos : 0 < 1 - Real.exp (-2 * (73 / 500)) := by
    have : Real.exp (-2 * (73 / 500)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hT := taylor_le_exp_neg (x := 0.292) (by norm_num) (by norm_num)
  have hT' := taylor_le_exp_neg (x := 0.373) (by norm_num) (by norm_num)
  have he := Real.exp_neg_one_gt_d9
  have hsplit : Real.exp (-1.373) = Real.exp (-1) * Real.exp (-0.373) := by
    rw [← Real.exp_add]; norm_num
  have hy : 1 - Real.exp (-2 * (73 / 500)) ≤ Real.exp (-1.373) := by
    rw [hsplit, show -2 * ((73 : ℝ) / 500) = -0.292 by norm_num]
    norm_num at hT hT'
    nlinarith [Real.exp_pos (-1), Real.exp_pos (-0.373)]
  have := Real.log_le_log hpos hy
  rw [Real.log_exp] at this
  linarith

/-! ### The jump profile is bounded by the mass -/

/-- Every gauge jump profile of a gauge with values in `[0, 1]` is at most `4 ∫ F²`. -/
theorem gaugeJumpProfile_le_four_mul_integral_sq {F M : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hMc : Continuous M) (hMcs : HasCompactSupport M)
    (hnn : ∀ y, 0 ≤ M y) (hle : ∀ y, M y ≤ 1) (t : ℝ) :
    gaugeJumpProfile M F t ≤ 4 * ∫ x, F x ^ 2 := by
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hF2t : Integrable fun x => F (x + t) ^ 2 := hF2.comp_add_right t
  have hint : Integrable fun x => signedShiftJump M F t x := by
    unfold signedShiftJump
    exact ((hMc.mul (hMc.comp (continuous_id.add continuous_const))).mul
      ((hF.sub (hF.comp (continuous_id.add continuous_const))).pow 2)).integrable_of_hasCompactSupport
        (hMcs.mul_right.mul_right)
  have hpt : ∀ x, signedShiftJump M F t x ≤ 2 * F x ^ 2 + 2 * F (x + t) ^ 2 := fun x => by
    unfold signedShiftJump
    have hMM : M x * M (x + t) ≤ 1 := mul_le_one₀ (hle x) (hnn _) (hle _)
    have hMM0 : 0 ≤ M x * M (x + t) := mul_nonneg (hnn x) (hnn _)
    have hsq : (F x - F (x + t)) ^ 2 ≤ 2 * F x ^ 2 + 2 * F (x + t) ^ 2 := by
      nlinarith [sq_nonneg (F x + F (x + t))]
    calc M x * M (x + t) * (F x - F (x + t)) ^ 2 ≤ 1 * (F x - F (x + t)) ^ 2 :=
          mul_le_mul_of_nonneg_right hMM (sq_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hsq
  unfold gaugeJumpProfile
  calc (∫ x, signedShiftJump M F t x) ≤ ∫ x, (2 * F x ^ 2 + 2 * F (x + t) ^ 2) :=
        integral_mono hint ((hF2.const_mul 2).add (hF2t.const_mul 2)) hpt
    _ = 4 * ∫ x, F x ^ 2 := by
        rw [integral_add (hF2.const_mul 2) (hF2t.const_mul 2), integral_const_mul,
          integral_const_mul, integral_add_right_eq_self (fun x => F x ^ 2) t]
        ring

/-! ### Coercive positivity past the plastic threshold -/

/-- **Weil positivity on `[−29/200, 29/200]`.** Every real `F ∈ C²_c` vanishing outside
`[−29/200, 29/200]` satisfies `Ẑ(F) ≥ (1/125) ∫ F²`. The gauge is the plateau of radius `73/500`; the
negative part of the density `ω − 2cosh(t/2)` on `(0.28, 0.292]` is absorbed into the potential. -/
theorem fullZeroForm_ge_of_support_le_pastPlastic {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hsupp : ∀ x, 29 / 200 < |x| → F x = 0) :
    1 / 125 * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  set R : ℝ := 73 / 500 with hRdef
  set δ : ℝ := 1 / 1000 with hδdef
  have hδ : 0 < δ := by norm_num
  set M := plateauGauge R δ with hMdef
  have hMd : ContDiff ℝ 2 M := contDiff_plateauGauge R δ
  have hMcs : HasCompactSupport M := hasCompactSupport_plateauGauge hδ
  have hnn : ∀ y, 0 ≤ M y := plateauGauge_nonneg R δ
  have hle : ∀ y, M y ≤ 1 := plateauGauge_le_one R δ
  have hzero : ∀ y, R ≤ |y| → M y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hone : ∀ y, |y| ≤ 29 / 200 → M y = 1 := fun y hy =>
    plateauGauge_eq_one hδ (by rw [hRdef, hδdef]; norm_num; linarith)
  have hFM : ∀ x, F x ≠ 0 → M x = 1 := fun x hx => hone x (by
    by_contra h
    exact hx (hsupp x (not_le.mp h)))
  have hFx : ∀ x, F x ≠ 0 → |x| < R := fun x hx => by
    by_contra h
    exact hx (by
      have := hzero x (not_lt.mp h)
      rw [hFM x hx] at this
      norm_num at this)
  have hFB : ∀ x, F x ≠ 0 → |x| ≤ R := fun x hx => (hFx x hx).le
  have hMB : ∀ x, M x ≠ 0 → |x| ≤ R := fun x hx => by
    by_contra h
    exact hx (hzero x (not_le.mp h).le)
  have hlog2 : 2 * R < Real.log 2 := by
    have := Real.log_two_gt_d9
    rw [hRdef]
    linarith
  obtain ⟨KF, -, hKF⟩ := exists_lipschitz_bound_of_compactSupport (hF.of_le (by norm_num)) hFc
  have hFL : ∀ a b, |F a - F b| ≤ KF * |a - b| := fun a b => hKF b a
  obtain ⟨KM, -, hKM⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hML : ∀ a b, |M a - M b| ≤ KM * |a - b| := fun a b => hKM b a
  -- the representation
  have hQ := markovEnergy_eq_gauge_window hF hFc hMd hMcs hle hnn hzero hFM
  have hJ := signedJumpEnergy_eq_arch_of_window (F := F) hzero hlog2
  have hE := two_mul_expMoments_eq_gauge hF.continuous hMd.continuous hFB hMB hFM
  have hZ := fullZeroForm_eq_markovEnergy_add_expMoments hF.continuous hFc
  -- the jump part: Markov up to `0.28`, a small negative density on `(0.28, 2R]`
  have hωI := integrableOn_archLevy_mul_gaugeJumpProfile hle hnn hzero (by norm_num) (by norm_num)
    hF.continuous hMd.continuous hMcs hFL
  have hcI : Integrable fun t => Real.cosh (t / 2) * gaugeJumpProfile M F t :=
    (integrable_gaugeJump_kernel hF.continuous hMd.continuous hMB).integral_prod_left.congr
      (Eventually.of_forall fun t => by
        simp only [gaugeJumpProfile]
        rw [integral_const_mul])
  set m := ∫ x, F x ^ 2 with hmdef
  have hIb := gaugeJumpProfile_le_four_mul_integral_sq hF.continuous hFc hMd.continuous hMcs hnn hle
  have hind : IntegrableOn ((Ioc (0.28 : ℝ) (2 * R)).indicator fun _ => 0.07 * (4 * m)) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))).integrableOn
  have hjump : 2 * (∫ t in Ioi (0 : ℝ), Real.cosh (t / 2) * gaugeJumpProfile M F t) ≤
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile M F t) +
        0.07 * (4 * m) * (2 * R - 0.28) := by
    have hset : (∫ t in Ioi (0 : ℝ), (Ioc (0.28 : ℝ) (2 * R)).indicator
        (fun _ => 0.07 * (4 * m)) t) = 0.07 * (4 * m) * (2 * R - 0.28) := by
      rw [setIntegral_indicator measurableSet_Ioc,
        show Ioi (0 : ℝ) ∩ Ioc 0.28 (2 * R) = Ioc 0.28 (2 * R) from
          inter_eq_right.mpr fun t ht => mem_Ioi.mpr (by linarith [ht.1]),
        setIntegral_const, smul_eq_mul, Real.volume_real_Ioc, max_eq_left (by rw [hRdef]; norm_num)]
      ring
    rw [← hset, ← integral_const_mul, ← integral_add hωI hind]
    refine setIntegral_mono_on (hcI.integrableOn.const_mul 2) (hωI.add hind) measurableSet_Ioi
      fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have hI0 : 0 ≤ gaugeJumpProfile M F t := integral_nonneg fun x => by
      unfold signedShiftJump
      exact mul_nonneg (mul_nonneg (hnn _) (hnn _)) (sq_nonneg _)
    by_cases h1 : t ≤ 0.28
    · rw [Set.indicator_of_notMem (fun h => by linarith [h.1]), add_zero, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (two_mul_cosh_le_archLevyDensity_of_le_plastic ht0 h1) hI0
    · by_cases h2 : t ≤ 2 * R
      · rw [Set.indicator_of_mem (show t ∈ Ioc (0.28 : ℝ) (2 * R) from ⟨not_le.mp h1, h2⟩)]
        have hk := two_mul_cosh_sub_archLevyDensity_le ht0 (by rw [hRdef] at h2; linarith)
        have hIt := hIb t
        nlinarith [mul_le_mul_of_nonneg_right hk hI0, mul_le_mul_of_nonneg_left hIt
          (by norm_num : (0 : ℝ) ≤ 0.07)]
      · rw [gaugeJumpProfile_eq_zero_of_ge hzero (not_le.mp h2).le,
          Set.indicator_of_notMem (fun h => h2 h.2)]
        simp
  -- the potential
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * R) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hW : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hML hdec8).neg
  have hG : Continuous fun x => ∫ y, M y * Real.cosh ((x - y) / 2) := by
    have e := funext (integral_gauge_cosh_eq hMd.continuous hMcs)
    rw [e]
    fun_prop
  set V := -Real.log (1 - Real.exp (-2 * R)) - 3 / 2 * R - 2 * archConstantReal + 4 * (29 / 200)
    with hVdef
  have hV : 1 / 125 + 0.07 * 4 * (2 * R - 0.28) ≤ V := by
    have h1 := neg_log_window_pastPlastic_ge
    have h2 := two_mul_archConstantReal_lt_sharp
    rw [hVdef, hRdef]
    linarith
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hP1 : Integrable fun x => F x ^ 2 * M x * -poleFreeWeilOperator M x :=
    (((hF.continuous.pow 2).mul hMd.continuous).mul hW).integrable_of_hasCompactSupport
      ((hasCompactSupport_sq hFc).mul_right.mul_right)
  have hP2 : Integrable fun x => F x ^ 2 * ∫ y, M y * Real.cosh ((x - y) / 2) :=
    ((hF.continuous.pow 2).mul hG).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc).mul_right
  have hpot : V * m ≤ (∫ x, F x ^ 2 * M x * -poleFreeWeilOperator M x) +
      2 * ∫ x, F x ^ 2 * ∫ y, M y * Real.cosh ((x - y) / 2) := by
    rw [hmdef, ← integral_const_mul, ← integral_const_mul, ← integral_add hP1 (hP2.const_mul 2)]
    refine integral_mono (hF2.const_mul V) (hP1.add (hP2.const_mul 2)) fun x => ?_
    by_cases h : F x = 0
    · simp [h]
    · have hw := neg_poleFreeWeilOperator_ge_sharp hMd.continuous hML hle hzero hlog2 (hFx x h)
        (hFM x h)
      have hg := two_mul_le_integral_gauge_cosh (r := 29 / 200) (by norm_num) hMd.continuous hMcs
        hnn hone x
      rw [hFM x h, mul_one]
      have hF0 := sq_nonneg (F x)
      nlinarith [mul_le_mul_of_nonneg_left hw hF0, mul_le_mul_of_nonneg_left hg hF0]
  have hI0 : 0 ≤ m := integral_nonneg fun x => sq_nonneg _
  have hfin : (1 / 125 + 0.07 * 4 * (2 * R - 0.28)) * m ≤ V * m :=
    mul_le_mul_of_nonneg_right hV hI0
  rw [hZ, hQ, hJ, hE]
  linarith

/-! ### Complex tests and the restricted Weil ground energy -/

/-- **Coercive zeta positivity for complex tests on `[−29/200, 29/200]`.** -/
theorem zetaZeroConfig_re_W_ge_of_support_le_pastPlastic {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Icc (-(29 / 200)) (29 / 200)) :
    1 / 125 * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hzero : ∀ x, 29 / 200 < |x| → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hgs h
      rw [mem_Icc] at this
      exact absurd (abs_le.mpr this) (not_le.mpr hx)
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_support_le_pastPlastic hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_of_support_le_pastPlastic him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm]
  linarith

/-- **The explicit floor past the plastic threshold**: `μ(A) ≥ 1/125` for every `A ≤ 29/200`. -/
theorem one_div_125_le_ccmRestrictedWeilGroundEnergy {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 29 / 200) : 1 / 125 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(29 / 200)) (29 / 200) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le_pastPlastic
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Contact apertures exceed `29/200`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos_pastPlastic {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 29 / 200 < A.1 := by
  by_contra hA
  have := one_div_125_le_ccmRestrictedWeilGroundEnergy (not_lt.mp hA)
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
