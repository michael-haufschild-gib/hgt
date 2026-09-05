import GaloisForLFunctions.RHTower.HighBlockDualWeightRightShift
import GaloisForLFunctions.RHTower.HighBlockChiModulus
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiUniformMovingRightLine

/-!
# High-block law: the frozen dual weight has bounded variation along the sample points

`W_{d,T}(Y)` is a superposition of the powers `Y^{−w}` over a vertical line, and each power has
explicit variation `‖B^{−w} − A^{−w}‖ ≤ ‖w‖ (A^{−Re w} − B^{−Re w})/Re w`. On the left line
`Re w = −(d+η)` (the corpus's `W = 1 + ∫…` representation, ratio `≲ (1+|v|)^η T^{−(d+η)}`) the
telescoped variation over `Y ≤ T` is `≲ 1/η`; on the right line `Re w = ½ − d + 1`
(`HighBlockDualWeightRightShift`, ratio `≲ (1+T)^{3/2}(1+|v|)^{3/2}‖χ(s)⁻¹‖`) the variation over
`Y ≥ T` is `≲ 1`. The `1/w` of the kernel cancels against the `‖w‖` of the power's derivative, so
no logarithmic loss appears. Result: `Σ_{n<L} ‖W_{d,T}((n+1)x) − W_{d,T}((n+2)x)‖ ≤ C`, uniformly
in `0 < d ≤ ¼`, `T ≥ 1`, `0 < x ≤ T`, `L`.
-/

open Complex MeasureTheory Filter Topology Set Finset

namespace RHTower

noncomputable section

/-- The dual sample points `(n+1)x`. -/
def dualPt (x : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * x

theorem dualPt_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < dualPt x n := by
  unfold dualPt
  positivity

theorem dualPt_le_succ {x : ℝ} (hx : 0 < x) (n : ℕ) : dualPt x n ≤ dualPt x (n + 1) := by
  unfold dualPt
  push_cast
  exact mul_le_mul_of_nonneg_right (by linarith) hx.le

/-- **Variation of a complex power along a positive segment.** -/
theorem norm_cpow_neg_sub_cpow_neg_le {w : ℂ} (hc : w.re ≠ 0) {A B : ℝ} (hA : 0 < A)
    (hAB : A ≤ B) :
    ‖(B : ℂ) ^ (-w) - (A : ℂ) ^ (-w)‖ ≤ ‖w‖ * ((A ^ (-w.re) - B ^ (-w.re)) / w.re) := by
  have hpos : ∀ y ∈ Set.uIcc A B, 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hAB] at hy
    linarith [hy.1]
  have hderiv : ∀ y ∈ Set.uIcc A B,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-w)) (-w * (y : ℂ) ^ (-w - 1)) y :=
    fun y hy => hasDerivAt_ofReal_cpow_neg (hpos y hy)
  have hfun : (fun y : ℝ => -w * (y : ℂ) ^ (-w - 1)) = fun y : ℝ => -w * (y : ℂ) ^ (-(w + 1)) := by
    funext y
    congr 2
    ring
  have hcont : ContinuousOn (fun y : ℝ => -w * (y : ℂ) ^ (-w - 1)) (Set.uIcc A B) := by
    rw [hfun]
    intro y hy
    exact (continuousAt_const.mul
      (hasDerivAt_ofReal_cpow_neg (w := w + 1) (hpos y hy)).continuousAt).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hFTC]
  refine (intervalIntegral.norm_integral_le_integral_norm hAB).trans ?_
  have hnorm : Set.EqOn (fun y : ℝ => ‖-w * (y : ℂ) ^ (-w - 1)‖)
      (fun y : ℝ => ‖w‖ * y ^ (-w.re - 1)) (Set.uIcc A B) := by
    intro y hy
    simp only
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (hpos y hy)]
    congr 2
    all_goals simp
  rw [intervalIntegral.integral_congr hnorm, intervalIntegral.integral_const_mul]
  have h0 : (0 : ℝ) ∉ Set.uIcc A B := by
    rw [Set.uIcc_of_le hAB]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by intro h; apply hc; linarith, h0⟩)]
  apply le_of_eq
  have hexp : -w.re - 1 + 1 = -w.re := by ring
  rw [hexp]
  field_simp
  try ring

/-- The two contour representations (restated). -/
theorem smoothAFEZetaDisplacedDualWeight_eq_rightShift {d Y : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hY : 0 < Y) {K'' : ℕ} (hK'' : 1 ≤ K'') (τ : ℝ) :
    smoothAFEZetaDisplacedDualWeight d τ Y =
      (1 / (2 * Real.pi)) • ∫ v : ℝ,
        dualWeightIntegrand d τ Y (((1 / 2 - d + K'' : ℝ) : ℂ) + (v : ℂ) * I) := by
  unfold smoothAFEZetaDisplacedDualWeight smoothAFEZetaDisplacedDualWeightAt
  congr 1
  exact integral_dualWeightIntegrand_one_eq_right hd hd4 hY hK'' τ

/-- Norm of the Gaussian kernel on a vertical line, exact. -/
theorem norm_smoothAFEGaussianKernel_eq (c v : ℝ) :
    ‖smoothAFEGaussianKernel ((c : ℂ) + (v : ℂ) * I)‖ =
      Real.exp (c ^ 2 - v ^ 2) / ‖(c : ℂ) + (v : ℂ) * I‖ := by
  unfold smoothAFEGaussianKernel
  rw [norm_div, Complex.norm_exp]
  congr 2
  simp [sq]
  try ring

/-- **Left-contour variation.** -/
theorem exists_sum_norm_dualWeight_sub_le_left {d₀ η : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ (T x : ℝ), 0 < x → ∀ m : ℕ,
      ∑ n ∈ Finset.range m, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤
        C * (((dualPt x m) ^ (d + η) - (dualPt x 0) ^ (d + η)) / (d + η)) /
          (max 1 |T|) ^ (d + η) := by
  obtain ⟨K, hK0, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_displaced_uniform_le hd₀0 hd₀half hη hηhalf
  have hG0 : 0 ≤ ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  refine ⟨(1 / (2 * Real.pi)) * (K * Real.exp ((d₀ + η) ^ 2) * Real.exp (η ^ 2) *
    ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2)), by positivity, ?_⟩
  intro d hd hdd₀ T x hx m
  have hdhalf : d < 1 / 2 := lt_of_le_of_lt hdd₀ hd₀half
  set G : ℝ := ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) with hGdef
  set δ : ℝ := d + η with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ d₀ + η := by rw [hδ]; linarith
  set M : ℝ := max 1 |T| with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  -- per-term bound
  have hterm : ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤
        ((1 / (2 * Real.pi)) * (K * Real.exp ((d₀ + η) ^ 2) * Real.exp (η ^ 2) * G)) *
          (((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ) / M ^ δ := by
    intro n
    have hYn := dualPt_pos hx n
    have hYn1 := dualPt_pos hx (n + 1)
    have hle := dualPt_le_succ hx n
    rw [smoothAFEZetaDisplacedDualWeight_eq_one_add_at_neg hd hdhalf hη hηhalf hYn T,
      smoothAFEZetaDisplacedDualWeight_eq_one_add_at_neg hd hdhalf hη hηhalf hYn1 T,
      add_sub_add_left_eq_sub]
    unfold smoothAFEZetaDisplacedDualWeightAt
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)),
      ← integral_sub (smoothAFEZetaDisplacedDualWeightAt_neg_integrable hd hdhalf hη hηhalf hYn T)
        (smoothAFEZetaDisplacedDualWeightAt_neg_integrable hd hdhalf hη hηhalf hYn1 T)]
    set B : ℝ := (K * Real.exp ((d₀ + η) ^ 2) * Real.exp (η ^ 2)) *
      (((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ) / M ^ δ with hB
    have hint : Integrable (fun v : ℝ => B * Real.exp (-(3 / 4) * v ^ 2)) :=
      (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
    have hΔ0 : 0 ≤ ((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ := by
      apply div_nonneg _ hδpos.le
      linarith [Real.rpow_le_rpow hYn.le hle hδpos.le]
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    refine le_trans (mul_le_mul_of_nonneg_left
      (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun v => ?_))
      (by positivity)) ?_
    · -- pointwise bound
      set w : ℂ := ((-(d + η) : ℝ) : ℂ) + (v : ℂ) * I with hw
      have hwre : w.re = -(d + η) := by simp [hw]
      have hwre0 : w.re ≠ 0 := by rw [hwre]; linarith
      have hw0 : (0 : ℝ) < ‖w‖ := by
        rw [norm_pos_iff]
        intro h
        have := congrArg Complex.re h
        rw [hwre] at this
        simp at this
        linarith
      have hfact : smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w) *
            smoothAFEMellinIntegrand (dualPt x n) w -
          smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w) *
            smoothAFEMellinIntegrand (dualPt x (n + 1)) w =
          smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w) * smoothAFEGaussianKernel w *
            (((dualPt x n : ℝ) : ℂ) ^ (-w) - ((dualPt x (n + 1) : ℝ) : ℂ) ^ (-w)) := by
        unfold smoothAFEMellinIntegrand
        ring
      rw [hfact, norm_mul, norm_mul, norm_sub_rev]
      have hcpow := norm_cpow_neg_sub_cpow_neg_le hwre0 hYn hle
      rw [hwre] at hcpow
      have hkern : ‖smoothAFEGaussianKernel w‖ = Real.exp (δ ^ 2 - v ^ 2) / ‖w‖ := by
        rw [hw, norm_smoothAFEGaussianKernel_eq]
        congr 2
        rw [hδ]
        ring
      have hrat := hratio d hd hdd₀ T v
      rw [← hδ] at hrat
      have hpow : (1 + |v|) ^ η * Real.exp (-(v ^ 2)) ≤
          Real.exp (η ^ 2) * Real.exp (-(3 / 4) * v ^ 2) :=
        one_add_abs_rpow_mul_exp_neg_sq_le hη.le v
      have hΔ : (dualPt x n ^ (-(-(d + η))) - dualPt x (n + 1) ^ (-(-(d + η)))) / -(d + η) =
          ((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ := by
        rw [neg_neg, hδ, div_neg, neg_div', neg_sub]
      rw [hΔ] at hcpow
      calc ‖smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w)‖ * ‖smoothAFEGaussianKernel w‖ *
            ‖((dualPt x (n + 1) : ℝ) : ℂ) ^ (-w) - ((dualPt x n : ℝ) : ℂ) ^ (-w)‖
          ≤ (K * (1 + |v|) ^ η / M ^ δ) * (Real.exp (δ ^ 2 - v ^ 2) / ‖w‖) *
            (‖w‖ * (((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ)) := by
            rw [hkern]
            gcongr
        _ = (K * ((1 + |v|) ^ η * Real.exp (-(v ^ 2))) * Real.exp (δ ^ 2)) *
            (((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ) / M ^ δ := by
            rw [show δ ^ 2 - v ^ 2 = δ ^ 2 + -(v ^ 2) by ring, Real.exp_add]
            field_simp
            try ring
        _ ≤ (K * (Real.exp (η ^ 2) * Real.exp (-(3 / 4) * v ^ 2)) * Real.exp ((d₀ + η) ^ 2)) *
            (((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ) / M ^ δ := by
            gcongr
            all_goals exact Real.exp_le_exp.mpr (by nlinarith [hδle, hδpos.le])
        _ = B * Real.exp (-(3 / 4) * v ^ 2) := by
            rw [hB]
            ring
    · rw [integral_const_mul]
      apply le_of_eq
      rw [hB]
      ring
  -- telescoping
  calc ∑ n ∈ Finset.range m, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖
      ≤ ∑ n ∈ Finset.range m,
          ((1 / (2 * Real.pi)) * (K * Real.exp ((d₀ + η) ^ 2) * Real.exp (η ^ 2) * G)) *
            (((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) / δ) / M ^ δ :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = ((1 / (2 * Real.pi)) * (K * Real.exp ((d₀ + η) ^ 2) * Real.exp (η ^ 2) * G)) *
          (((dualPt x m) ^ δ - (dualPt x 0) ^ δ) / δ) / M ^ δ := by
        have htel : ∑ n ∈ Finset.range m, ((dualPt x (n + 1)) ^ δ - (dualPt x n) ^ δ) =
            (dualPt x m) ^ δ - (dualPt x 0) ^ δ :=
          Finset.sum_range_sub (fun n => (dualPt x n) ^ δ) m
        rw [← htel, Finset.sum_div, Finset.mul_sum, Finset.sum_div]

/-- **Right-contour variation** (`K'' = 1`). -/
theorem exists_sum_norm_dualWeight_sub_le_right :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ (T x : ℝ), 0 < x → ∀ m L : ℕ, m ≤ L →
      ∑ n ∈ Finset.Ico m L, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤
        C * (1 + |T|) ^ ((1 : ℝ) + 1 / 2) * ‖(zetaChi (displacedLinePt d T))⁻¹‖ *
          ((dualPt x m) ^ (-(1 / 2 - d + 1)) / (1 / 2 - d + 1)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zetaChi_negNat_line_le 1
  have hG0 : 0 ≤ ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) :=
    integral_nonneg fun v => (Real.exp_pos _).le
  set p : ℝ := (1 : ℝ) + 1 / 2 with hp
  have hp0 : 0 ≤ p := by rw [hp]; norm_num
  refine ⟨(1 / (2 * Real.pi)) * (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2) *
    ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2)), by positivity, ?_⟩
  intro d hd hd4 T x hx m L hmL
  set G : ℝ := ∫ v : ℝ, Real.exp (-(3 / 4) * v ^ 2) with hGdef
  set K : ℝ := 1 / 2 - d + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hKpos : 0 < K := by linarith
  have hKp : K ≤ p := by rw [hK, hp]; linarith
  set S : ℝ := ‖(zetaChi (displacedLinePt d T))⁻¹‖ with hS
  have hS0 : 0 ≤ S := norm_nonneg _
  have hcast : (((1 / 2 - d + (1 : ℕ) : ℝ)) : ℂ) = ((K : ℝ) : ℂ) := by
    rw [hK]; push_cast; ring
  -- per-term bound
  have hterm : ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤
        ((1 / (2 * Real.pi)) * (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2) * G)) *
          (1 + |T|) ^ p * S * (((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K) := by
    intro n
    have hYn := dualPt_pos hx n
    have hYn1 := dualPt_pos hx (n + 1)
    have hle := dualPt_le_succ hx n
    rw [smoothAFEZetaDisplacedDualWeight_eq_rightShift hd hd4 hYn (le_refl 1) T,
      smoothAFEZetaDisplacedDualWeight_eq_rightShift hd hd4 hYn1 (le_refl 1) T,
      ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    have hint1 := integrable_dualWeightIntegrand_right_line hd hd4 hYn (le_refl 1) T
    have hint2 := integrable_dualWeightIntegrand_right_line hd hd4 hYn1 (le_refl 1) T
    rw [← integral_sub hint1 hint2]
    set B : ℝ := (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2)) * (1 + |T|) ^ p * S *
      (((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K) with hB
    have hint : Integrable (fun v : ℝ => B * Real.exp (-(3 / 4) * v ^ 2)) :=
      (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
    have hΔ0 : 0 ≤ ((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K := by
      apply div_nonneg _ hKpos.le
      have := Real.rpow_le_rpow_of_nonpos hYn hle (by linarith : -K ≤ 0)
      linarith
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    refine le_trans (mul_le_mul_of_nonneg_left
      (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun v => ?_))
      (by positivity)) ?_
    · set w : ℂ := (((1 / 2 - d + (1 : ℕ) : ℝ)) : ℂ) + (v : ℂ) * I with hw
      have hwK : w = ((K : ℝ) : ℂ) + (v : ℂ) * I := by rw [hw, hcast]
      have hwre : w.re = K := by rw [hwK]; simp
      have hwre0 : w.re ≠ 0 := by rw [hwre]; exact hKpos.ne'
      have hw0 : (0 : ℝ) < ‖w‖ := by
        rw [norm_pos_iff]
        intro h
        have := congrArg Complex.re h
        rw [hwre] at this
        simp at this
        linarith
      have hfact : dualWeightIntegrand d T (dualPt x n) w - dualWeightIntegrand d T (dualPt x (n + 1)) w =
          smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w) * smoothAFEGaussianKernel w *
            (((dualPt x n : ℝ) : ℂ) ^ (-w) - ((dualPt x (n + 1) : ℝ) : ℂ) ^ (-w)) := by
        unfold dualWeightIntegrand smoothAFEMellinIntegrand
        ring
      rw [hfact, norm_mul, norm_mul, norm_sub_rev]
      have hcpow := norm_cpow_neg_sub_cpow_neg_le hwre0 hYn hle
      rw [hwre] at hcpow
      have hkern : ‖smoothAFEGaussianKernel w‖ = Real.exp (K ^ 2 - v ^ 2) / ‖w‖ := by
        rw [hwK, norm_smoothAFEGaussianKernel_eq]
      -- the ratio on the right line
      have hchi : zetaChi (displacedLinePt d T) ≠ 0 :=
        zetaChi_ne_zero_of_mem_openStrip (displacedLinePt_mem_openStrip hd (by linarith) T).1
          (displacedLinePt_mem_openStrip hd (by linarith) T).2
      have harg : displacedLinePt d T + -w = (((-(1 : ℝ)) : ℝ) : ℂ) + ((T - v : ℝ) : ℂ) * I := by
        rw [hwK, hK]
        unfold displacedLinePt
        push_cast
        ring
      have hrat : ‖smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w)‖ ≤
          C₁ * ((1 + |T|) ^ p * (1 + |v|) ^ p) * S := by
        unfold smoothAFEZetaChiShiftRatio
        rw [harg, div_eq_mul_inv, norm_mul]
        have h1 := hC₁ (T - v)
        have hcastp : ((1 : ℕ) : ℝ) + 1 / 2 = p := by rw [hp]; norm_num
        rw [hcastp] at h1
        have hsum : 1 + |T - v| ≤ (1 + |T|) * (1 + |v|) := by
          have h2 : |T - v| ≤ |T| + |v| := abs_sub _ _
          nlinarith [abs_nonneg T, abs_nonneg v]
        have hrp : (1 + |T - v|) ^ p ≤ (1 + |T|) ^ p * (1 + |v|) ^ p := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) hsum hp0
        have hcast1 : ((((-(1 : ℕ) : ℝ)) : ℝ) : ℂ) = (((-(1 : ℝ)) : ℝ) : ℂ) := by push_cast; ring
        rw [hcast1] at h1
        calc ‖zetaChi ((((-(1 : ℝ)) : ℝ) : ℂ) + ((T - v : ℝ) : ℂ) * I)‖ * S
            ≤ (C₁ * (1 + |T - v|) ^ p) * S := mul_le_mul_of_nonneg_right h1 hS0
          _ ≤ (C₁ * ((1 + |T|) ^ p * (1 + |v|) ^ p)) * S :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrp hC₁0) hS0
      have hpow : (1 + |v|) ^ p * Real.exp (-(v ^ 2)) ≤
          Real.exp (p ^ 2) * Real.exp (-(3 / 4) * v ^ 2) :=
        one_add_abs_rpow_mul_exp_neg_sq_le hp0 v
      calc ‖smoothAFEZetaChiShiftRatio (displacedLinePt d T) (-w)‖ * ‖smoothAFEGaussianKernel w‖ *
            ‖((dualPt x (n + 1) : ℝ) : ℂ) ^ (-w) - ((dualPt x n : ℝ) : ℂ) ^ (-w)‖
          ≤ (C₁ * ((1 + |T|) ^ p * (1 + |v|) ^ p) * S) * (Real.exp (K ^ 2 - v ^ 2) / ‖w‖) *
            (‖w‖ * (((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K)) := by
            rw [hkern]
            gcongr
        _ = (C₁ * ((1 + |v|) ^ p * Real.exp (-(v ^ 2))) * Real.exp (K ^ 2)) * (1 + |T|) ^ p * S *
            (((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K) := by
            rw [show K ^ 2 - v ^ 2 = K ^ 2 + -(v ^ 2) by ring, Real.exp_add]
            field_simp
            try ring
        _ ≤ (C₁ * (Real.exp (p ^ 2) * Real.exp (-(3 / 4) * v ^ 2)) * Real.exp (p ^ 2)) *
            (1 + |T|) ^ p * S * (((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K) := by
            gcongr
            all_goals exact Real.exp_le_exp.mpr (by nlinarith [hKp, hKpos.le])
        _ = B * Real.exp (-(3 / 4) * v ^ 2) := by
            rw [hB]
            ring
    · rw [integral_const_mul]
      apply le_of_eq
      rw [hB]
      ring
  -- telescoping over `Ico m L`
  calc ∑ n ∈ Finset.Ico m L, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖
      ≤ ∑ n ∈ Finset.Ico m L,
          ((1 / (2 * Real.pi)) * (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2) * G)) *
            (1 + |T|) ^ p * S * (((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) / K) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = ((1 / (2 * Real.pi)) * (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2) * G)) *
          (1 + |T|) ^ p * S * (((dualPt x m) ^ (-K) - (dualPt x L) ^ (-K)) / K) := by
        have htel : ∑ n ∈ Finset.Ico m L, ((dualPt x n) ^ (-K) - (dualPt x (n + 1)) ^ (-K)) =
            (dualPt x m) ^ (-K) - (dualPt x L) ^ (-K) := by
          rw [Finset.sum_Ico_eq_sum_range]
          have := Finset.sum_range_sub' (fun k => (dualPt x (m + k)) ^ (-K)) (L - m)
          simp only [add_zero] at this
          rw [show m + (L - m) = L from Nat.add_sub_cancel' hmL] at this
          rw [← this]
          rfl
        rw [← htel, Finset.sum_div, Finset.mul_sum]
    _ ≤ ((1 / (2 * Real.pi)) * (C₁ * Real.exp (p ^ 2) * Real.exp (p ^ 2) * G)) *
          (1 + |T|) ^ p * S * ((dualPt x m) ^ (-K) / K) := by
        gcongr
        have := (dualPt_pos hx L)
        have : 0 ≤ (dualPt x L) ^ (-K) := by positivity
        linarith

/-- `‖χ(½−d+iT)⁻¹‖ ≤ (2π)^d T^{−d} e^5` for `T ≥ 1`, `0 ≤ d ≤ ¼`. -/
theorem norm_inv_zetaChi_displacedLinePt_le {d T : ℝ} (hd0 : 0 ≤ d) (hd4 : d ≤ 1 / 4)
    (hT : 1 ≤ T) :
    ‖(zetaChi (displacedLinePt d T))⁻¹‖ ≤ (2 * Real.pi) ^ d * T ^ (-d) * Real.exp 5 := by
  obtain ⟨e, he, heq⟩ := exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp hd0 hd4
    (by linarith)
  rw [norm_inv, heq, mul_inv, ← Real.exp_neg]
  have hTpos : 0 < T := by linarith
  have hw : (chiModulusWeight d T)⁻¹ = (2 * Real.pi) ^ d * T ^ (-d) := by
    unfold chiModulusWeight
    rw [Real.div_rpow hTpos.le (by positivity), inv_div, div_eq_mul_inv, ← Real.rpow_neg hTpos.le]
  have he5 : |e| ≤ 5 := by
    refine he.trans ?_
    have h1 : Real.pi / T ≤ Real.pi := div_le_self Real.pi_pos.le hT
    have h2 : 5 / T ^ 2 ≤ 5 := div_le_self (by norm_num) (one_le_pow₀ hT)
    have h3 : Real.pi / T + 5 / T ^ 2 ≤ 9 := by linarith [Real.pi_le_four]
    have h4 : 0 ≤ Real.pi / T + 5 / T ^ 2 := by positivity
    calc d * (Real.pi / T + 5 / T ^ 2) ≤ (1 / 4) * 9 :=
          mul_le_mul hd4 h3 h4 (by norm_num)
      _ ≤ 5 := by norm_num
  have hee : Real.exp (-e) ≤ Real.exp 5 :=
    Real.exp_le_exp.mpr (by linarith [neg_abs_le e])
  rw [hw]
  exact mul_le_mul_of_nonneg_left hee (by positivity)

/-- **Uniform bound on the dual weight.** -/
theorem exists_norm_smoothAFEZetaDisplacedDualWeight_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ T Y : ℝ, 1 ≤ T → 0 < Y →
      ‖smoothAFEZetaDisplacedDualWeight d T Y‖ ≤ C := by
  obtain ⟨C₀, hC₀0, hsmall⟩ := exists_norm_smoothAFEZetaDisplacedDualWeight_sub_one_le_uniform_conductor
    (d₀ := 1 / 4) (η := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₁, hC₁0, hlarge⟩ := exists_norm_smoothAFEZetaDisplacedDualWeight_le_rightShift (K'' := 1)
    (le_refl 1)
  refine ⟨max (1 + C₀) (C₁ * (4 * (2 * Real.pi) * Real.exp 5)), le_max_of_le_left (by linarith), ?_⟩
  intro d hd hd4 T Y hT hY
  have hTpos : 0 < T := by linarith
  have hmaxT : max 1 |T| = T := by rw [abs_of_pos hTpos]; exact max_eq_right hT
  rcases le_or_gt Y T with hYT | hYT
  · -- small scale
    have h := hsmall d hd hd4 T hY
    rw [hmaxT] at h
    have hδ : (0 : ℝ) ≤ d + 1 / 4 := by linarith
    have hratio : Y ^ (d + 1 / 4) / T ^ (d + 1 / 4) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact Real.rpow_le_rpow hY.le hYT hδ
    have h' : ‖smoothAFEZetaDisplacedDualWeight d T Y - 1‖ ≤ C₀ := by
      calc ‖smoothAFEZetaDisplacedDualWeight d T Y - 1‖ ≤ C₀ * Y ^ (d + 1 / 4) / T ^ (d + 1 / 4) := h
        _ = C₀ * (Y ^ (d + 1 / 4) / T ^ (d + 1 / 4)) := by ring
        _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hratio hC₀0
        _ = C₀ := mul_one _
    calc ‖smoothAFEZetaDisplacedDualWeight d T Y‖
        = ‖(smoothAFEZetaDisplacedDualWeight d T Y - 1) + 1‖ := by ring_nf
      _ ≤ ‖smoothAFEZetaDisplacedDualWeight d T Y - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C₀ + 1 := by rw [norm_one]; linarith
      _ ≤ max (1 + C₀) (C₁ * (4 * (2 * Real.pi) * Real.exp 5)) := by
          rw [add_comm]; exact le_max_left _ _
  · -- large scale
    have h := hlarge d T Y hd hd4 hY
    have hS := norm_inv_zetaChi_displacedLinePt_le hd.le hd4 hT
    set S := ‖(zetaChi (displacedLinePt d T))⁻¹‖ with hSdef
    have hS0 : 0 ≤ S := norm_nonneg _
    have hp : ((1 : ℕ) : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [hp] at h
    have hK : -(1 / 2 - d + ((1 : ℕ) : ℝ)) = -(3 / 2 - d) := by push_cast; ring
    rw [hK] at h
    -- (1+|T|)^{3/2} ≤ 4 T^{3/2}
    have h1T : (1 + |T|) ^ (3 / 2 : ℝ) ≤ 4 * T ^ (3 / 2 : ℝ) := by
      rw [abs_of_pos hTpos]
      calc (1 + T) ^ (3 / 2 : ℝ) ≤ (2 * T) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = 2 ^ (3 / 2 : ℝ) * T ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hTpos.le
        _ ≤ 4 * T ^ (3 / 2 : ℝ) := by
            gcongr
            calc (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := by rw [Real.rpow_two]; norm_num
    -- Y^{-(3/2-d)} ≤ T^{-(3/2-d)}
    have hYpow : Y ^ (-(3 / 2 - d)) ≤ T ^ (-(3 / 2 - d)) :=
      Real.rpow_le_rpow_of_nonpos hTpos hYT.le (by linarith)
    have h2π : (2 * Real.pi) ^ d ≤ 2 * Real.pi := by
      calc (2 * Real.pi) ^ d ≤ (2 * Real.pi) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = 2 * Real.pi := Real.rpow_one _
    -- assemble: C₁ (1+T)^{3/2} S Y^{-(3/2-d)} ≤ C₁ · 4 T^{3/2} · (2π)^d T^{-d} e^5 · T^{-(3/2-d)}
    have hTT : T ^ (3 / 2 : ℝ) * T ^ (-d) * T ^ (-(3 / 2 - d)) = 1 := by
      rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
      rw [show (3 / 2 : ℝ) + -d + -(3 / 2 - d) = 0 by ring, Real.rpow_zero]
    calc ‖smoothAFEZetaDisplacedDualWeight d T Y‖
        ≤ C₁ * (1 + |T|) ^ (3 / 2 : ℝ) * S * Y ^ (-(3 / 2 - d)) := h
      _ ≤ C₁ * (4 * T ^ (3 / 2 : ℝ)) * ((2 * Real.pi) ^ d * T ^ (-d) * Real.exp 5) *
            T ^ (-(3 / 2 - d)) := by gcongr
      _ = C₁ * (4 * (2 * Real.pi) ^ d * Real.exp 5) *
            (T ^ (3 / 2 : ℝ) * T ^ (-d) * T ^ (-(3 / 2 - d))) := by ring
      _ = C₁ * (4 * (2 * Real.pi) ^ d * Real.exp 5) := by rw [hTT, mul_one]
      _ ≤ C₁ * (4 * (2 * Real.pi) * Real.exp 5) := by gcongr
      _ ≤ max (1 + C₀) (C₁ * (4 * (2 * Real.pi) * Real.exp 5)) := le_max_right _ _

/-- **Uniform total variation of the frozen dual weight along the sample points.** -/
theorem exists_sum_norm_dualWeight_diff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ T x : ℝ, 1 ≤ T → 0 < x → x ≤ T →
      ∀ L : ℕ, ∑ n ∈ Finset.range L, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
          smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤ C := by
  obtain ⟨CL, hCL0, hL⟩ := exists_sum_norm_dualWeight_sub_le_left (d₀ := 1 / 4) (η := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CR, hCR0, hR⟩ := exists_sum_norm_dualWeight_sub_le_right
  refine ⟨CL * 8 + CR * (4 * (2 * Real.pi) * Real.exp 5), by positivity, ?_⟩
  intro d hd hd4 T x hT hx hxT L
  have hTpos : 0 < T := by linarith
  have hmaxT : max 1 |T| = T := by rw [abs_of_pos hTpos]; exact max_eq_right hT
  set m := min L ⌊T / x⌋₊ with hm
  have hmL : m ≤ L := min_le_left _ _
  rw [← Finset.sum_range_add_sum_Ico _ hmL]
  -- left part
  have hleft := hL d hd hd4 T x hx m
  rw [hmaxT] at hleft
  set δ : ℝ := d + 1 / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hm_le : (m : ℝ) ≤ T / x := by
    have h1 : m ≤ ⌊T / x⌋₊ := min_le_right _ _
    calc (m : ℝ) ≤ (⌊T / x⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ T / x := Nat.floor_le (by positivity)
  have hYm : dualPt x m ≤ 2 * T := by
    unfold dualPt
    have h1 : ((m : ℝ) + 1) * x ≤ (T / x + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx.le
    have h2 : (T / x + 1) * x = T + x := by field_simp
    linarith
  have hleft' : ∑ n ∈ Finset.range m, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
      smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤ CL * 8 := by
    refine hleft.trans ?_
    have hY0 : 0 ≤ (dualPt x 0) ^ δ := Real.rpow_nonneg (dualPt_pos hx 0).le _
    have hYmδ : (dualPt x m) ^ δ ≤ 2 ^ δ * T ^ δ := by
      rw [← Real.mul_rpow (by norm_num) hTpos.le]
      exact Real.rpow_le_rpow (dualPt_pos hx m).le hYm hδpos.le
    have h2δ : (2 : ℝ) ^ δ ≤ 2 := by
      calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
        _ = 2 := Real.rpow_one _
    have hTδ : 0 < T ^ δ := by positivity
    have hquarter : 1 / δ ≤ 4 := by
      rw [div_le_iff₀ hδpos]
      rw [hδ]
      linarith
    calc CL * (((dualPt x m) ^ δ - (dualPt x 0) ^ δ) / δ) / T ^ δ
        ≤ CL * ((2 ^ δ * T ^ δ) / δ) / T ^ δ := by gcongr; linarith
      _ = CL * 2 ^ δ * (1 / δ) := by field_simp
      _ ≤ CL * 2 * 4 := by gcongr
      _ = CL * 8 := by ring
  -- right part
  have hright' : ∑ n ∈ Finset.Ico m L, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
      smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖ ≤
        CR * (4 * (2 * Real.pi) * Real.exp 5) := by
    rcases eq_or_lt_of_le hmL with hmeq | hmlt
    · rw [hmeq, Finset.Ico_self, Finset.sum_empty]
      positivity
    · have hright := hR d hd hd4 T x hx m L hmL
      -- m = ⌊T/x⌋ and dualPt x m > T
      have hmfloor : m = ⌊T / x⌋₊ := by
        rw [hm]
        exact min_eq_right (by
          by_contra hcon
          have hlt := not_le.mp hcon
          have : m = L := by rw [hm]; exact min_eq_left hlt.le
          omega)
      have hYmT : T < dualPt x m := by
        unfold dualPt
        rw [hmfloor]
        have h1 := Nat.lt_floor_add_one (T / x)
        have h2 : T / x * x < ((⌊T / x⌋₊ : ℝ) + 1) * x := mul_lt_mul_of_pos_right h1 hx
        rwa [div_mul_cancel₀ _ hx.ne'] at h2
      have hS := norm_inv_zetaChi_displacedLinePt_le hd.le hd4 hT
      set S := ‖(zetaChi (displacedLinePt d T))⁻¹‖ with hSdef
      have hS0 : 0 ≤ S := norm_nonneg _
      have hK : 1 ≤ 1 / 2 - d + 1 := by linarith
      have hKpos : 0 < 1 / 2 - d + 1 := by linarith
      have h1T : (1 + |T|) ^ ((1 : ℝ) + 1 / 2) ≤ 4 * T ^ ((1 : ℝ) + 1 / 2) := by
        rw [abs_of_pos hTpos]
        calc (1 + T) ^ ((1 : ℝ) + 1 / 2) ≤ (2 * T) ^ ((1 : ℝ) + 1 / 2) :=
              Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
          _ = 2 ^ ((1 : ℝ) + 1 / 2) * T ^ ((1 : ℝ) + 1 / 2) := Real.mul_rpow (by norm_num) hTpos.le
          _ ≤ 4 * T ^ ((1 : ℝ) + 1 / 2) := by
              gcongr
              calc (2 : ℝ) ^ ((1 : ℝ) + 1 / 2) ≤ 2 ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 4 := by rw [Real.rpow_two]; norm_num
      have hYpow : (dualPt x m) ^ (-(1 / 2 - d + 1)) ≤ T ^ (-(1 / 2 - d + 1)) :=
        Real.rpow_le_rpow_of_nonpos hTpos hYmT.le (by linarith)
      have h2π : (2 * Real.pi) ^ d ≤ 2 * Real.pi := by
        calc (2 * Real.pi) ^ d ≤ (2 * Real.pi) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
          _ = 2 * Real.pi := Real.rpow_one _
      have hTT : T ^ ((1 : ℝ) + 1 / 2) * T ^ (-d) * T ^ (-(1 / 2 - d + 1)) = 1 := by
        rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
        rw [show (1 : ℝ) + 1 / 2 + -d + -(1 / 2 - d + 1) = 0 by ring, Real.rpow_zero]
      have hinvK : 1 / (1 / 2 - d + 1) ≤ 1 := by
        rw [div_le_one hKpos]; exact hK
      have hYm0 : 0 ≤ (dualPt x m) ^ (-(1 / 2 - d + 1)) := Real.rpow_nonneg (dualPt_pos hx m).le _
      have h1T0 : 0 ≤ (1 + |T|) ^ ((1 : ℝ) + 1 / 2) := by positivity
      have hTd0 : 0 ≤ T ^ (-d) := by positivity
      have hTK0 : 0 ≤ T ^ (-(1 / 2 - d + 1)) := by positivity
      have hD : (dualPt x m) ^ (-(1 / 2 - d + 1)) / (1 / 2 - d + 1) ≤
          T ^ (-(1 / 2 - d + 1)) / (1 / 2 - d + 1) :=
        div_le_div_of_nonneg_right hYpow hKpos.le
      have hD0 : 0 ≤ (dualPt x m) ^ (-(1 / 2 - d + 1)) / (1 / 2 - d + 1) :=
        div_nonneg hYm0 hKpos.le
      have hX0 : 0 ≤ CR * (4 * (2 * Real.pi) * Real.exp 5) := by positivity
      calc ∑ n ∈ Finset.Ico m L, ‖smoothAFEZetaDisplacedDualWeight d T (dualPt x n) -
            smoothAFEZetaDisplacedDualWeight d T (dualPt x (n + 1))‖
          ≤ CR * (1 + |T|) ^ ((1 : ℝ) + 1 / 2) * S *
              ((dualPt x m) ^ (-(1 / 2 - d + 1)) / (1 / 2 - d + 1)) := hright
        _ ≤ CR * (4 * T ^ ((1 : ℝ) + 1 / 2)) * ((2 * Real.pi) ^ d * T ^ (-d) * Real.exp 5) *
              (T ^ (-(1 / 2 - d + 1)) / (1 / 2 - d + 1)) :=
            mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1T hCR0) hS hS0 (by positivity))
              hD hD0 (by positivity)
        _ = CR * (4 * (2 * Real.pi) ^ d * Real.exp 5) *
              (T ^ ((1 : ℝ) + 1 / 2) * T ^ (-d) * T ^ (-(1 / 2 - d + 1))) /
              (1 / 2 - d + 1) := by ring
        _ = CR * (4 * (2 * Real.pi) ^ d * Real.exp 5) / (1 / 2 - d + 1) := by
            rw [hTT, mul_one]
        _ ≤ CR * (4 * (2 * Real.pi) * Real.exp 5) / (1 / 2 - d + 1) := by
            apply div_le_div_of_nonneg_right _ hKpos.le
            gcongr
        _ ≤ CR * (4 * (2 * Real.pi) * Real.exp 5) / 1 :=
            div_le_div_of_nonneg_left hX0 one_pos hK
        _ = CR * (4 * (2 * Real.pi) * Real.exp 5) := div_one _
  linarith

end

end RHTower
