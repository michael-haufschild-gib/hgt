import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualWeightHeightDerivative
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedVariationBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualWeightDerivativeBound

/-!
# Conductor-scale derivative bound for displaced dual weights

Central frequencies use the displaced chi slope's `1/tau` saving.  Outside
that window, `tau < 2|v|` converts the global slope into two additional
frequency powers, retained inside a quartic Gaussian majorant.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Uniform conductor-decaying quartic-Gaussian envelope for the displaced
dual-weight height derivative integrand. -/
theorem exists_norm_smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand_le
    {d0 eta : ℝ} (hd00 : 0 ≤ d0) (hd0quarter : d0 ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 < d → d ≤ d0 →
      ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y → ∀ v : ℝ,
        ‖smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
            d eta tau Y v‖ ≤
          (K * Y ^ (d + eta) / tau ^ (d + eta + 1)) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  have hd0half : d0 < 1 / 2 := hd0quarter.trans_lt (by norm_num)
  have hetaHalf : eta < 1 / 2 := hetaquarter.trans_lt (by norm_num)
  obtain ⟨R, hR, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_uniform_le
      hd00 hd0half heta hetaHalf
  obtain ⟨D, hD, hslopeGlobal⟩ :=
    exists_norm_logDeriv_zetaChi_displaced_neg_shift_sub_le_global
      hd00 hd0half heta hetaHalf
  let C : ℝ := 8 + 4 * Real.pi
  let H : ℝ := Real.exp ((d0 + eta) ^ 2) / eta
  let K : ℝ := R * H * (C + 6 * D)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun d hd hdd0 {tau Y} htau hY v => ?_⟩
  have hdquarter : d ≤ 1 / 4 := hdd0.trans hd0quarter
  have htau0 : 0 < tau := by linarith
  have habstau : |tau| = tau := abs_of_pos htau0
  have hmax : max 1 |tau| = tau := by
    rw [habstau, max_eq_right]
    linarith
  let q : ℝ := 1 + |v|
  let s : ℝ := d + eta
  have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg v]
  have hs0 : 0 < s := by dsimp only [s]; linarith
  have hratioRaw := hratio d hd hdd0 tau v
  have hratio' :
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
          (-(((-s : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        R * q ^ eta / tau ^ s := by
    simpa only [s, q, hmax] using hratioRaw
  have hqeta : q ^ eta ≤ q := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : eta ≤ 1)
  have hratioLinear :
      ‖smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
          (-(((-s : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
        R * q / tau ^ s := by
    exact hratio'.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqeta hR) (Real.rpow_nonneg htau0.le s))
  have hm := norm_smoothAFEMellinIntegrand_vertical_le_of_ne hY
    (neg_ne_zero.mpr hs0.ne') v
  have hfac : Real.exp (s ^ 2) / s ≤ H := by
    have hsle : s ≤ d0 + eta := by dsimp only [s]; linarith
    have hsquares : s ^ 2 ≤ (d0 + eta) ^ 2 := by
      have hd0eta0 : 0 ≤ d0 + eta := by linarith
      nlinarith
    have hexp : Real.exp (s ^ 2) ≤ Real.exp ((d0 + eta) ^ 2) :=
      Real.exp_le_exp.mpr hsquares
    dsimp only [H]
    apply (div_le_div_iff₀ hs0 heta).2
    exact mul_le_mul hexp (by linarith) heta.le (Real.exp_pos _).le
  have hm' :
      ‖smoothAFEMellinIntegrand Y
          (((-s : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Y ^ s * H) * Real.exp (-(v ^ 2)) := by
    have hnegSum : -eta + -d = -s := by dsimp only [s]; ring
    have hm0 :
        ‖smoothAFEMellinIntegrand Y
            (((-s : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
          Y ^ s * (Real.exp (s ^ 2) / s) * Real.exp (-(v ^ 2)) := by
      simpa only [s, hnegSum, neg_neg, neg_sq, abs_neg,
        abs_of_pos hs0] using hm
    exact hm0.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hY.le s))
      (Real.exp_pos _).le)
  have hq24 : q ^ 2 ≤ q ^ 4 := by
    have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    calc
      q ^ 2 = q ^ 2 * 1 := by ring
      _ ≤ q ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_left hq2 (sq_nonneg q)
      _ = q ^ 4 := by ring
  have hpow : tau ^ (s + 1) = tau ^ s * tau := by
    rw [Real.rpow_add htau0, Real.rpow_one]
  have htauPow0 : tau ^ s ≠ 0 := (Real.rpow_pos_of_pos htau0 s).ne'
  by_cases hv : 2 * |v| ≤ tau
  · have hslope := norm_logDeriv_zetaChi_displaced_neg_shift_sub_le_coarse
      hd hdquarter heta hetaquarter htau hv
    have hslope' :
        ‖logDeriv zetaChi
            (displacedLinePt d tau -
              (((-s : ℝ) : ℂ) + (v : ℂ) * I)) -
          logDeriv zetaChi (displacedLinePt d tau)‖ ≤
          C * q / tau := by
      simpa only [s, q, C] using hslope
    have hKcentral : R * H * C ≤ K := by
      dsimp only [K]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hR hH)
      linarith
    unfold smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
      smoothAFEZetaDisplacedChiShiftHeightDerivative
    simp only [norm_mul, norm_I, one_mul]
    calc
      (‖smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
            (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          ‖logDeriv zetaChi
              (displacedLinePt d tau -
                (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
            logDeriv zetaChi (displacedLinePt d tau)‖) *
          ‖smoothAFEMellinIntegrand Y
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ ((R * q / tau ^ s) * (C * q / tau)) *
            ((Y ^ s * H) * Real.exp (-(v ^ 2))) := by
          dsimp only [s] at hratioLinear hslope' hm'
          gcongr
      _ = (R * H * C * Y ^ s / tau ^ (s + 1)) *
            (q ^ 2 * Real.exp (-(v ^ 2))) := by
          rw [hpow]
          field_simp [htauPow0, htau0.ne']
      _ ≤ (K * Y ^ s / tau ^ (s + 1)) *
            (q ^ 4 * Real.exp (-(v ^ 2))) := by
          gcongr
      _ = (K * Y ^ (d + eta) / tau ^ (d + eta + 1)) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by rfl
  · have htail : tau < 2 * |v| := lt_of_not_ge hv
    have hslope := hslopeGlobal d hd hdd0 tau v
    have hslope' :
        ‖logDeriv zetaChi
            (displacedLinePt d tau -
              (((-s : ℝ) : ℂ) + (v : ℂ) * I)) -
          logDeriv zetaChi (displacedLinePt d tau)‖ ≤
          D * (1 + tau) * q := by
      simpa only [s, q, habstau] using hslope
    have htailFactor : tau * (1 + tau) ≤ 6 * q ^ 2 := by
      have htaule : tau ≤ 2 * |v| := by linarith
      have h1tau : 1 + tau ≤ 3 * q := by
        dsimp only [q]
        linarith [abs_nonneg v]
      calc
        tau * (1 + tau) ≤ (2 * |v|) * (3 * q) :=
          mul_le_mul htaule h1tau (by positivity) (by positivity)
        _ ≤ 6 * q ^ 2 := by
          dsimp only [q]
          nlinarith [abs_nonneg v]
    have hKtail : 6 * R * H * D ≤ K := by
      dsimp only [K]
      calc
        6 * R * H * D = R * H * (6 * D) := by ring
        _ ≤ R * H * (C + 6 * D) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hR hH)
          linarith
    unfold smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
      smoothAFEZetaDisplacedChiShiftHeightDerivative
    simp only [norm_mul, norm_I, one_mul]
    calc
      (‖smoothAFEZetaChiShiftRatio (displacedLinePt d tau)
            (-(((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          ‖logDeriv zetaChi
              (displacedLinePt d tau -
                (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
            logDeriv zetaChi (displacedLinePt d tau)‖) *
          ‖smoothAFEMellinIntegrand Y
            (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ ((R * q / tau ^ s) * (D * (1 + tau) * q)) *
            ((Y ^ s * H) * Real.exp (-(v ^ 2))) := by
          dsimp only [s] at hratioLinear hslope' hm'
          gcongr
      _ = (R * H * D * Y ^ s / tau ^ (s + 1)) *
            ((tau * (1 + tau)) * q ^ 2 * Real.exp (-(v ^ 2))) := by
          rw [hpow]
          field_simp [htauPow0, htau0.ne']
      _ ≤ (6 * R * H * D * Y ^ s / tau ^ (s + 1)) *
            (q ^ 4 * Real.exp (-(v ^ 2))) := by
          calc
            _ ≤ (R * H * D * Y ^ s / tau ^ (s + 1)) *
                ((6 * q ^ 2) * q ^ 2 * Real.exp (-(v ^ 2))) := by gcongr
            _ = _ := by ring
      _ ≤ (K * Y ^ s / tau ^ (s + 1)) *
            (q ^ 4 * Real.exp (-(v ^ 2))) := by gcongr
      _ = (K * Y ^ (d + eta) / tau ^ (d + eta + 1)) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by rfl

/-- Uniform conductor-scale derivative bound for the exact displaced dual
weight. -/
theorem exists_norm_deriv_smoothAFEZetaDisplacedDualWeight_le
    {d0 eta : ℝ} (hd00 : 0 ≤ d0) (hd0quarter : d0 ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ d : ℝ, 0 < d → d ≤ d0 →
      ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
        ‖deriv (fun u : ℝ => smoothAFEZetaDisplacedDualWeight d u Y) tau‖ ≤
          A * Y ^ (d + eta) / tau ^ (d + eta + 1) := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand_le
      hd00 hd0quarter heta hetaquarter
  let q : ℝ → ℝ := fun v => (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))
  let M : ℝ := ∫ v : ℝ, q v
  let a : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := a * K * M
  have hq : Integrable q := integrable_one_add_abs_pow_four_mul_exp_neg_sq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by dsimp only [q]; positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact integral_nonneg hq0
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  refine ⟨A, by dsimp only [A]; positivity, fun d hd hdd0 {tau Y} htau hY => ?_⟩
  have hdhalf : d < 1 / 2 :=
    (hdd0.trans hd0quarter).trans_lt (by norm_num)
  have hetaHalf : eta < 1 / 2 := hetaquarter.trans_lt (by norm_num)
  let P : ℝ := K * Y ^ (d + eta) / tau ^ (d + eta + 1)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hboundInt : Integrable (fun v : ℝ => P * q v) := hq.const_mul P
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
            d eta tau Y v‖ ≤
        ∫ v : ℝ, P * q v := by
    apply norm_integral_le_of_norm_le hboundInt
    exact Filter.Eventually.of_forall fun v => by
      simpa only [P, q] using hpoint d hd hdd0 htau hY v
  rw [(hasDerivAt_smoothAFEZetaDisplacedDualWeight_via_neg
    hd hdhalf heta hetaHalf hY tau).deriv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∫ v : ℝ,
          smoothAFEZetaDisplacedDualWeightHeightDerivativeIntegrand
            d eta tau Y v‖
        ≤ a * ∫ v : ℝ, P * q v := by gcongr
    _ = a * (P * M) := by
      rw [integral_const_mul]
    _ = A * Y ^ (d + eta) / tau ^ (d + eta + 1) := by
      dsimp only [A, P]
      ring

end RHTower
