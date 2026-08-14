import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative
import GaloisForLFunctions.RHTower.TrigammaVertical
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContourLimit
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative slow variation of the zeta-AFE chi shift

The exact chi-shift derivative is controlled by a difference of logarithmic derivatives, not by
either logarithmic derivative separately.  This module bounds that difference on the conductor
window `2 |v| ≤ tau`.  The leading `log tau` modes have already cancelled algebraically; a
trigamma mean-value estimate leaves the scale `(1 + |v|) / tau`.
-/

noncomputable section

open Complex Set

namespace RHTower

/-- Digamma varies by `O((1+|v|)/tau)` across the positive-height conductor segment from
`1/4 + i tau/2` to `3/4 + i(tau-v)/2`. -/
theorem norm_digamma_conductor_increment_le
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖Complex.digamma
          (((3 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) -
        Complex.digamma
          (((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  let z0 : ℂ := ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I
  let z1 : ℂ := ((3 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I
  have htau0 : 0 < tau := by linarith
  have hline : ∀ r : ℝ, AffineMap.lineMap z0 z1 r =
      (((1 / 4 : ℝ) + r / 2 : ℝ) : ℂ) +
        (((tau - r * v) / 2 : ℝ) : ℂ) * I := by
    intro r
    apply Complex.ext
    · simp [z0, z1, AffineMap.lineMap_apply]
      ring
    · simp [z0, z1, AffineMap.lineMap_apply]
      ring
  have hdiff : ∀ z ∈ segment ℝ z0 z1, DifferentiableAt ℂ Complex.digamma z := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨r, hr, rfl⟩
    apply (digamma_analyticOnNhd_re_pos _ ?_).differentiableAt
    rw [hline]
    change 0 <
      ((((1 / 4 : ℝ) + r / 2 : ℝ) : ℂ) +
        (((tau - r * v) / 2 : ℝ) : ℂ) * I).re
    norm_num
    nlinarith [hr.1]
  have hbound : ∀ z ∈ segment ℝ z0 z1,
      ‖deriv Complex.digamma z‖ ≤ 16 / tau ^ 2 + 2 * Real.pi / tau := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨r, hr, rfl⟩
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have hv0 : 0 ≤ |v| := abs_nonneg v
    have hrv : r * v ≤ |v| := by
      calc
        r * v ≤ r * |v| := mul_le_mul_of_nonneg_left (le_abs_self v) hr0
        _ ≤ 1 * |v| := mul_le_mul_of_nonneg_right hr1 hv0
        _ = |v| := one_mul _
    have ht : tau / 4 ≤ (tau - r * v) / 2 := by linarith
    have htpos : 0 < (tau - r * v) / 2 := lt_of_lt_of_le (by positivity) ht
    have hsigma : 0 < (1 / 4 : ℝ) + r / 2 := by positivity
    rw [hline]
    refine (norm_deriv_digamma_vertical_le hsigma htpos).trans ?_
    have htau4 : 0 < tau / 4 := by positivity
    have hsquare : 1 / ((tau - r * v) / 2) ^ 2 ≤ 16 / tau ^ 2 := by
      have hsq : (tau / 4) ^ 2 ≤ ((tau - r * v) / 2) ^ 2 :=
        (sq_le_sq₀ htau4.le htpos.le).2 ht
      have hi := one_div_le_one_div_of_le (sq_pos_of_pos htau4) hsq
      have heq : 1 / (tau / 4) ^ 2 = 16 / tau ^ 2 := by
        field_simp
        norm_num
      exact hi.trans_eq heq
    have hpi : Real.pi / (2 * ((tau - r * v) / 2)) ≤ 2 * Real.pi / tau := by
      have hden : 2 * (tau / 4) ≤ 2 * ((tau - r * v) / 2) := by nlinarith
      have hi := one_div_le_one_div_of_le (by positivity : 0 < 2 * (tau / 4)) hden
      have hmul := mul_le_mul_of_nonneg_left hi Real.pi_pos.le
      calc
        Real.pi / (2 * ((tau - r * v) / 2))
            = Real.pi * (1 / (2 * ((tau - r * v) / 2))) := by ring
        _ ≤ Real.pi * (1 / (2 * (tau / 4))) := hmul
        _ = 2 * Real.pi / tau := by
          field_simp
          norm_num
    linarith
  have hmvt := (convex_segment z0 z1).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (left_mem_segment ℝ z0 z1) (right_mem_segment ℝ z0 z1)
  have hnorm : ‖z1 - z0‖ ≤ 1 + |v| := by
    have hrepr : z1 - z0 =
        (((1 / 2 : ℝ) : ℂ) + (((-v / 2 : ℝ) : ℂ) * I)) := by
      dsimp only [z0, z1]
      push_cast
      ring
    rw [hrepr]
    calc
      ‖((1 / 2 : ℝ) : ℂ) + (((-v / 2 : ℝ) : ℂ) * I)‖
          ≤ ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(((-v / 2 : ℝ) : ℂ) * I)‖ := norm_add_le _ _
      _ = 1 / 2 + |v| / 2 := by simp
      _ ≤ 1 + |v| := by linarith [abs_nonneg v]
  dsimp only [z0, z1] at hmvt
  refine hmvt.trans ?_
  exact mul_le_mul_of_nonneg_left hnorm (by positivity)

/-- Conjugate lower-height form of `norm_digamma_conductor_increment_le`. -/
theorem norm_digamma_conductor_increment_neg_le
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖Complex.digamma
          (((3 / 4 : ℝ) : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I) -
        Complex.digamma
          (((1 / 4 : ℝ) : ℂ) - ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  let a : ℂ := ((3 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I
  let b : ℂ := ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I
  have ha : (starRingEnd ℂ) a =
      ((3 / 4 : ℝ) : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [a, map_div₀, map_ofNat]
  have hb : (starRingEnd ℂ) b =
      ((1 / 4 : ℝ) : ℂ) - ((tau / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [b, map_div₀, map_ofNat]
  rw [← ha, ← hb, ReflectedDigammaAnomaly.digamma_conj,
    ReflectedDigammaAnomaly.digamma_conj, ← map_sub, norm_conj]
  exact norm_digamma_conductor_increment_le htau hv

/-- Moving from the left chi argument into the positive half-plane costs one digamma recurrence
term.  Its norm is at most `4/tau` on the conductor window. -/
theorem norm_digamma_shifted_increment_le
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖Complex.digamma
          (((-1 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) -
        Complex.digamma
          (((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) + 4 / tau := by
  let a : ℂ := ((-1 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I
  let b : ℂ := ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I
  have htau0 : 0 < tau := by linarith
  have hvle : |v| ≤ tau / 2 := by linarith
  have him : tau / 4 ≤ (tau - v) / 2 := by linarith [le_abs_self v]
  have him0 : 0 < (tau - v) / 2 := lt_of_lt_of_le (by positivity) him
  have haim : |a.im| = (tau - v) / 2 := by
    dsimp only [a]
    simp [abs_of_pos him0]
  have hanorm : tau / 4 ≤ ‖a‖ := by
    calc
      tau / 4 ≤ (tau - v) / 2 := him
      _ = |a.im| := haim.symm
      _ ≤ ‖a‖ := Complex.abs_im_le_norm a
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, norm_zero] at hanorm
    linarith
  have hainv : ‖a⁻¹‖ ≤ 4 / tau := by
    rw [norm_inv]
    have hi := one_div_le_one_div_of_le (by positivity : 0 < tau / 4) hanorm
    have heq : 1 / (tau / 4) = 4 / tau := by field_simp
    simpa only [one_div] using hi.trans_eq heq
  have haPole : ∀ m : ℕ, a ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    have hal : a.re = -1 / 4 := by simp [a]
    have har : (-(m : ℂ)).re = -(m : ℝ) := by simp
    rw [hal, har] at hre
    cases m with
    | zero => norm_num at hre
    | succ m =>
        have hm1 : (1 : ℝ) ≤ (Nat.succ m : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        linarith
  have hrec := Complex.digamma_apply_add_one a haPole
  have haone : a + 1 =
      ((3 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
    dsimp only [a]
    push_cast
    ring
  have hsplit : Complex.digamma a - Complex.digamma b =
      (Complex.digamma (a + 1) - Complex.digamma b) - a⁻¹ := by
    rw [hrec]
    ring
  change ‖Complex.digamma a - Complex.digamma b‖ ≤ _
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [haone]
  exact add_le_add (norm_digamma_conductor_increment_le htau hv) hainv

/-- Exact quantitative form of the cancellation in the chi logarithmic slope. -/
theorem norm_logDeriv_zetaChi_shift_sub_line_le
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖logDeriv zetaChi
          (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)‖ ≤
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) + 2 / tau := by
  rw [logDeriv_zetaChi_shift_sub_line_eq_digamma_increments]
  have hfirst :
      ‖Complex.digamma
          ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
        Complex.digamma (linePt tau / 2)‖ ≤
        (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) + 4 / tau := by
    have hz : (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
        ((-1 / 4 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [linePt]
        ring
      · simp [linePt]
    have hs : linePt tau / 2 =
        ((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [linePt]
        ring
      · simp [linePt]
    rw [hz, hs]
    exact norm_digamma_shifted_increment_le htau hv
  have hsecond :
      ‖Complex.digamma
          ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
        Complex.digamma ((1 - linePt tau) / 2)‖ ≤
        (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
    have hz : (1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
        ((3 / 4 : ℝ) : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [linePt]
        ring
      · simp [linePt]
        ring
    have hs : (1 - linePt tau) / 2 =
        ((1 / 4 : ℝ) : ℂ) - ((tau / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [linePt]
        ring
      · simp [linePt]
        ring
    rw [hz, hs]
    exact norm_digamma_conductor_increment_neg_le htau hv
  calc
    ‖-(Complex.digamma
          ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (linePt tau / 2)) / 2 -
        (Complex.digamma
          ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - linePt tau) / 2)) / 2‖
      ≤ ‖-(Complex.digamma
          ((linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (linePt tau / 2)) / 2‖ +
        ‖(Complex.digamma
          ((1 - (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - linePt tau) / 2)) / 2‖ := norm_sub_le _ _
    _ ≤ ((16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) + 4 / tau) / 2 +
        ((16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)) / 2 := by
      rw [norm_div, norm_neg, norm_div]
      norm_num
      exact add_le_add (div_le_div_of_nonneg_right hfirst (by norm_num))
        (div_le_div_of_nonneg_right hsecond (by norm_num))
    _ = (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) + 2 / tau := by ring

/-- Coarse but integration-friendly slow-variation bound. -/
theorem norm_logDeriv_zetaChi_shift_sub_line_le_coarse
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖logDeriv zetaChi
          (linePt tau - (((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)‖ ≤
      (6 + 2 * Real.pi) * (1 + |v|) / tau := by
  have h := norm_logDeriv_zetaChi_shift_sub_line_le htau hv
  have htau0 : 0 < tau := by linarith
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hpow : 16 / tau ^ 2 ≤ 4 / tau := by
    rw [div_le_div_iff₀ (sq_pos_of_pos htau0) htau0]
    nlinarith
  refine h.trans ?_
  calc
    (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) + 2 / tau
        ≤ (4 / tau + 2 * Real.pi / tau) * (1 + |v|) + 2 / tau := by
          gcongr
    _ ≤ (4 / tau + 2 * Real.pi / tau) * (1 + |v|) +
          (2 / tau) * (1 + |v|) := by
          gcongr
          nlinarith [mul_nonneg (by positivity : 0 ≤ 2 / tau) hv0]
    _ = (6 + 2 * Real.pi) * (1 + |v|) / tau := by
      field_simp
      ring

/-- The exact chi ratio moves at relative speed `O((1+|v|)/tau)` throughout the conductor
window.  This is the coefficient-variation input needed by a moving-polynomial mean-square
argument. -/
theorem norm_deriv_smoothAFEZetaChiShiftRatio_neg_right_one_line_le
    {tau v : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖deriv
        (fun u : ℝ => smoothAFEZetaChiShiftRatio (linePt u)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))) tau‖ ≤
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
        ((6 + 2 * Real.pi) * (1 + |v|) / tau) := by
  rw [(hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line tau v).deriv]
  rw [norm_mul, norm_mul, norm_I, one_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_logDeriv_zetaChi_shift_sub_line_le_coarse htau hv) (norm_nonneg _)

/-- On a dyadic height block, the central-conductor chi ratio can be frozen with an explicit
Lipschitz error.  This is the blockwise coefficient-control form of the relative derivative
estimate. -/
theorem norm_smoothAFEZetaChiShiftRatio_sub_le_dyadic
    {T tau u v : ℝ} (hT : 4 ≤ T)
    (htau : tau ∈ Set.Icc T (2 * T)) (hu : u ∈ Set.Icc T (2 * T))
    (hv : 2 * |v| ≤ T) :
    ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) -
        smoothAFEZetaChiShiftRatio (linePt u)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
      ((1 + 2 * T) * (6 + 2 * Real.pi) * (1 + |v|) ^ 2 / T) * |tau - u| := by
  let f : ℝ → ℂ := fun y => smoothAFEZetaChiShiftRatio (linePt y)
    (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))
  let C : ℝ := (1 + 2 * T) * (6 + 2 * Real.pi) * (1 + |v|) ^ 2 / T
  have hdiff : ∀ y ∈ Set.Icc T (2 * T), DifferentiableAt ℝ f y := by
    intro y hy
    exact (hasDerivAt_smoothAFEZetaChiShiftRatio_neg_right_one_line y v).differentiableAt
  have hbound : ∀ y ∈ Set.Icc T (2 * T), ‖deriv f y‖ ≤ C := by
    intro y hy
    have hy4 : 4 ≤ y := hT.trans hy.1
    have hvy : 2 * |v| ≤ y := hv.trans hy.1
    have hy0 : 0 < y := by linarith
    have hyratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le y v
    have hyabs : |y| = y := abs_of_pos hy0
    have hyfac : 1 + |y| ≤ 1 + 2 * T := by rw [hyabs]; linarith [hy.2]
    have hratio :
        ‖smoothAFEZetaChiShiftRatio (linePt y)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤
            (1 + 2 * T) * (1 + |v|) := by
      exact hyratio.trans (mul_le_mul_of_nonneg_right hyfac (by positivity))
    have hderiv :=
      norm_deriv_smoothAFEZetaChiShiftRatio_neg_right_one_line_le hy4 hvy
    dsimp only [f, C]
    refine hderiv.trans ?_
    calc
      ‖smoothAFEZetaChiShiftRatio (linePt y)
          (-(((1 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ((6 + 2 * Real.pi) * (1 + |v|) / y)
        ≤ ((1 + 2 * T) * (1 + |v|)) *
            ((6 + 2 * Real.pi) * (1 + |v|) / y) := by gcongr
      _ ≤ ((1 + 2 * T) * (1 + |v|)) *
            ((6 + 2 * Real.pi) * (1 + |v|) / T) := by
              gcongr
              exact hy.1
      _ = (1 + 2 * T) * (6 + 2 * Real.pi) * (1 + |v|) ^ 2 / T := by ring
  have hmvt := (convex_Icc T (2 * T)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound hu htau
  dsimp only [f, C] at hmvt ⊢
  simpa [Real.norm_eq_abs] using hmvt

end RHTower
