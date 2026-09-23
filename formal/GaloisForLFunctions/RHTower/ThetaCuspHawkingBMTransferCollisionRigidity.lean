import GaloisForLFunctions.RHTower.TrigammaVertical
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import GaloisForLFunctions.HTGeometry.PolygammaMultiplication
import GaloisForLFunctions.HTGeometry.HorizontalModulusDerivative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonlinearRadiationKernel
import GaloisForLFunctions.RHTower.HedenmalmStokesFourthTraceCurvatureBudgetBand
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Birmingham--Mokhtari second-harmonic transfer collision rigidity

At Xi-divisor height, reflected and Schwarz-conjugate BM boundary transfers collide exactly on
critical line. Proof uses Gauss multiplication to expose a strictly positive horizontal logarithmic
slope of squared transfer modulus.
-/

open Complex Real Set

namespace RHTower

noncomputable section

def d4BMSecondHarmonicTransferOfRho (rho : ℂ) : ℂ :=
  Complex.Gamma (-rho - 1) * Complex.Gamma (-1 / 2 : ℂ) *
    (Complex.Gamma (-(rho + 4) / 4))⁻¹ *
      (Complex.Gamma (-(3 * rho + 2) / 4))⁻¹

def d4BMPositiveStripTransferProfile (u : ℂ) : ℂ :=
  d4BMSecondHarmonicTransferOfRho (1 - 4 * u)

def d4BMPositiveStripTransferLogSlope (u : ℂ) : ℂ :=
  (Real.log (256 / 27 : ℝ) : ℂ) +
    (u - 5 / 4)⁻¹ + (u - 5 / 12)⁻¹ + (u - 1 / 12)⁻¹ -
      (u - 1 / 2)⁻¹ +
    Complex.digamma u + Complex.digamma (u + 1 / 2) -
      Complex.digamma (u + 7 / 12) - Complex.digamma (u + 11 / 12)

lemma two_lt_log_twoHundredFiftySix_div_twentySeven :
    (2 : ℝ) < Real.log (256 / 27 : ℝ) := by
  have hlt : Real.exp 2 < (256 / 27 : ℝ) := by
    have h := Real.exp_one_lt_d9
    have he : Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hp : 0 < Real.exp 1 := Real.exp_pos 1
    rw [he]
    nlinarith
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr hlt

lemma norm_digamma_horizontal_shift_le
    {sigma tau c : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) (hc : 0 ≤ c) :
    ‖Complex.digamma
          (((sigma + c : ℝ) : ℂ) + (tau : ℂ) * I) -
        Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I)‖ ≤
      c * (1 / |tau| ^ (2 : ℕ) + Real.pi / (2 * |tau|)) := by
  let z0 : ℂ := (sigma : ℂ) + (tau : ℂ) * I
  let z1 : ℂ := ((sigma + c : ℝ) : ℂ) + (tau : ℂ) * I
  have hline : ∀ r : ℝ, AffineMap.lineMap z0 z1 r =
      (((sigma + r * c : ℝ) : ℂ) + (tau : ℂ) * I) := by
    intro r
    apply Complex.ext
    · simp [z0, z1, AffineMap.lineMap_apply]
      ring
    · simp [z0, z1, AffineMap.lineMap_apply]
  have hdiff : ∀ z ∈ segment ℝ z0 z1, DifferentiableAt ℂ Complex.digamma z := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨r, hr, rfl⟩
    apply (digamma_analyticOnNhd_re_pos _ ?_).differentiableAt
    rw [hline]
    change 0 < ((((sigma + r * c : ℝ) : ℂ) + (tau : ℂ) * I).re)
    norm_num
    nlinarith [hr.1]
  have hbound : ∀ z ∈ segment ℝ z0 z1,
      ‖deriv Complex.digamma z‖ ≤
        1 / |tau| ^ (2 : ℕ) + Real.pi / (2 * |tau|) := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨r, hr, rfl⟩
    rw [hline]
    have hre : 0 < sigma + r * c := by nlinarith [hr.1]
    simpa only [abs_of_pos htau] using
      (norm_deriv_digamma_vertical_le hre htau)
  have hmvt := (convex_segment z0 z1).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (left_mem_segment ℝ z0 z1) (right_mem_segment ℝ z0 z1)
  have hnorm : ‖z1 - z0‖ = c := by
    have heq : z1 - z0 = (c : ℂ) := by
      dsimp only [z0, z1]
      push_cast
      ring
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  dsimp only [z0, z1] at hmvt
  rw [hnorm] at hmvt
  simpa only [mul_comm] using hmvt

lemma norm_digamma_horizontal_shift_abs_le
    {sigma tau c : ℝ} (hsigma : 0 < sigma) (htau : tau ≠ 0) (hc : 0 ≤ c) :
    ‖Complex.digamma
          (((sigma + c : ℝ) : ℂ) + (tau : ℂ) * I) -
        Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I)‖ ≤
      c * (1 / |tau| ^ (2 : ℕ) + Real.pi / (2 * |tau|)) := by
  rcases lt_or_gt_of_ne htau with htneg | htpos
  · have hpos : 0 < -tau := by linarith
    have h := norm_digamma_horizontal_shift_le hsigma hpos hc
    have hconj1' : (starRingEnd ℂ)
        (((sigma + c : ℝ) : ℂ) + (tau : ℂ) * I) =
          (((sigma + c : ℝ) : ℂ) + ((-tau : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    have hconj0' : (starRingEnd ℂ)
        ((sigma : ℂ) + (tau : ℂ) * I) =
          ((sigma : ℂ) + ((-tau : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    have hnorm :
        ‖Complex.digamma
            (((sigma + c : ℝ) : ℂ) + (tau : ℂ) * I) -
          Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I)‖ =
        ‖Complex.digamma
            (((sigma + c : ℝ) : ℂ) + ((-tau : ℝ) : ℂ) * I) -
          Complex.digamma ((sigma : ℂ) + ((-tau : ℝ) : ℂ) * I)‖ := by
      rw [← norm_conj]
      simp only [map_sub, ← ReflectedDigammaAnomaly.digamma_conj,
        hconj1', hconj0']
    rw [hnorm]
    simpa [abs_of_neg htneg] using h
  · exact norm_digamma_horizontal_shift_le hsigma htpos hc

lemma vertical_inv_sub_re (sigma tau a : ℝ) :
    ((((sigma : ℂ) + (tau : ℂ) * I) - (a : ℂ))⁻¹).re =
      (sigma - a) / ((sigma - a) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
  rw [Complex.inv_re]
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, Complex.normSq_apply, sub_im, add_im,
    mul_im, zero_add]
  ring

lemma trigamma_height_budget_lt_three_halves
    {tau : ℝ} (htau : 13 / 8 < |tau|) :
    1 / |tau| ^ (2 : ℕ) + Real.pi / (2 * |tau|) < 3 / 2 := by
  have htpos : 0 < |tau| := lt_trans (by norm_num) htau
  have hsquare : (169 / 64 : ℝ) < |tau| ^ (2 : ℕ) := by nlinarith
  have hinv : 1 / |tau| ^ (2 : ℕ) < (64 / 169 : ℝ) := by
    rw [div_lt_iff₀ (sq_pos_of_pos htpos)]
    nlinarith
  have hpi : Real.pi / (2 * |tau|) < (88 / 91 : ℝ) := by
    rw [div_lt_iff₀ (mul_pos (by norm_num) htpos)]
    nlinarith [Real.pi_lt_d4]
  calc
    1 / |tau| ^ (2 : ℕ) + Real.pi / (2 * |tau|) < 64 / 169 + 88 / 91 :=
      add_lt_add hinv hpi
    _ < 3 / 2 := by norm_num

lemma positiveStrip_rationalSlope_re_gt_neg_half
    {sigma tau : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1 / 4)
    (htau : 13 / 8 < |tau|) :
    (((((sigma : ℂ) + (tau : ℂ) * I) - 5 / 4)⁻¹ +
        (((sigma : ℂ) + (tau : ℂ) * I) - 5 / 12)⁻¹ +
        (((sigma : ℂ) + (tau : ℂ) * I) - 1 / 12)⁻¹ -
        (((sigma : ℂ) + (tau : ℂ) * I) - 1 / 2)⁻¹).re) > -(1 / 2 : ℝ) := by
  have ht2 : (169 / 64 : ℝ) < tau ^ (2 : ℕ) := by
    nlinarith [sq_abs tau]
  have h1den : 0 < (sigma - 5 / 4) ^ (2 : ℕ) + tau ^ (2 : ℕ) := by positivity
  have h2den : 0 < (sigma - 5 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ) := by positivity
  have h3den : 0 < (sigma - 1 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ) := by positivity
  have h4den : 0 < (sigma - 1 / 2) ^ (2 : ℕ) + tau ^ (2 : ℕ) := by positivity
  have h1 : -(3 / 10 : ℝ) <
      (sigma - 5 / 4) / ((sigma - 5 / 4) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    rw [lt_div_iff₀ h1den]
    nlinarith [sq_nonneg (sigma - 5 / 4)]
  have h2 : -(3 / 20 : ℝ) <
      (sigma - 5 / 12) / ((sigma - 5 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    rw [lt_div_iff₀ h2den]
    nlinarith [sq_nonneg (sigma - 5 / 12)]
  have h3 : -(1 / 30 : ℝ) <
      (sigma - 1 / 12) / ((sigma - 1 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    by_cases h : sigma < 1 / 12
    · rw [lt_div_iff₀ h3den]
      nlinarith [sq_nonneg (sigma - 1 / 12)]
    · have hnonneg : 0 ≤
          (sigma - 1 / 12) / ((sigma - 1 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ)) :=
        div_nonneg (by linarith) h3den.le
      linarith
  have h4 : 0 <
      -((sigma - 1 / 2) / ((sigma - 1 / 2) ^ (2 : ℕ) + tau ^ (2 : ℕ))) := by
    have hneg : sigma - 1 / 2 < 0 := by linarith
    exact neg_pos.mpr (div_neg_of_neg_of_pos hneg h4den)
  have h1re :
      ((((sigma : ℂ) + (tau : ℂ) * I) - 5 / 4)⁻¹).re =
        (sigma - 5 / 4) / ((sigma - 5 / 4) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    convert vertical_inv_sub_re sigma tau (5 / 4) using 1
    all_goals norm_num
  have h2re :
      ((((sigma : ℂ) + (tau : ℂ) * I) - 5 / 12)⁻¹).re =
        (sigma - 5 / 12) / ((sigma - 5 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    convert vertical_inv_sub_re sigma tau (5 / 12) using 1
    all_goals norm_num
  have h3re :
      ((((sigma : ℂ) + (tau : ℂ) * I) - 1 / 12)⁻¹).re =
        (sigma - 1 / 12) / ((sigma - 1 / 12) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    convert vertical_inv_sub_re sigma tau (1 / 12) using 1
    all_goals norm_num
  have h4re :
      ((((sigma : ℂ) + (tau : ℂ) * I) - 1 / 2)⁻¹).re =
        (sigma - 1 / 2) / ((sigma - 1 / 2) ^ (2 : ℕ) + tau ^ (2 : ℕ)) := by
    convert vertical_inv_sub_re sigma tau (1 / 2) using 1
    all_goals norm_num
  simp only [add_re, sub_re]
  rw [h1re, h2re, h3re, h4re]
  linarith

lemma positiveStrip_digammaSlope_re_gt_neg_three_halves
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 13 / 8 < |tau|) :
    (Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I) +
      Complex.digamma (((sigma + 1 / 2 : ℝ) : ℂ) + (tau : ℂ) * I) -
      Complex.digamma (((sigma + 7 / 12 : ℝ) : ℂ) + (tau : ℂ) * I) -
      Complex.digamma (((sigma + 11 / 12 : ℝ) : ℂ) + (tau : ℂ) * I)).re >
        -(3 / 2 : ℝ) := by
  let B : ℝ := 1 / |tau| ^ (2 : ℕ) + Real.pi / (2 * |tau|)
  have htau0 : tau ≠ 0 := by
    intro h
    rw [h, abs_zero] at htau
    norm_num at htau
  have hB : B < 3 / 2 :=
    trigamma_height_budget_lt_three_halves htau
  have h1 := norm_digamma_horizontal_shift_abs_le
    hsigma htau0 (by norm_num : (0 : ℝ) ≤ 7 / 12)
  have h2 := norm_digamma_horizontal_shift_abs_le
    (by linarith : 0 < sigma + 1 / 2) htau0
    (by norm_num : (0 : ℝ) ≤ 5 / 12)
  have h1' :
      ‖Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I) -
        Complex.digamma (((sigma + 7 / 12 : ℝ) : ℂ) + (tau : ℂ) * I)‖ ≤
          (7 / 12 : ℝ) * B := by
    rw [norm_sub_rev]
    simpa only [B] using h1
  have h2' :
      ‖Complex.digamma (((sigma + 1 / 2 : ℝ) : ℂ) + (tau : ℂ) * I) -
        Complex.digamma (((sigma + 11 / 12 : ℝ) : ℂ) + (tau : ℂ) * I)‖ ≤
          (5 / 12 : ℝ) * B := by
    have hadd : sigma + 1 / 2 + 5 / 12 = sigma + 11 / 12 := by ring
    rw [norm_sub_rev]
    simpa only [hadd, B] using h2
  let w : ℂ :=
    (Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I) -
      Complex.digamma (((sigma + 7 / 12 : ℝ) : ℂ) + (tau : ℂ) * I)) +
    (Complex.digamma (((sigma + 1 / 2 : ℝ) : ℂ) + (tau : ℂ) * I) -
      Complex.digamma (((sigma + 11 / 12 : ℝ) : ℂ) + (tau : ℂ) * I))
  have hnorm : ‖w‖ ≤ B := by
    calc
      ‖w‖ ≤
          ‖Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I) -
            Complex.digamma (((sigma + 7 / 12 : ℝ) : ℂ) + (tau : ℂ) * I)‖ +
          ‖Complex.digamma (((sigma + 1 / 2 : ℝ) : ℂ) + (tau : ℂ) * I) -
            Complex.digamma (((sigma + 11 / 12 : ℝ) : ℂ) + (tau : ℂ) * I)‖ :=
        norm_add_le _ _
      _ ≤ (7 / 12 : ℝ) * B + (5 / 12 : ℝ) * B := add_le_add h1' h2'
      _ = B := by ring
  have hre : -‖w‖ ≤ w.re :=
    (abs_le.mp (Complex.abs_re_le_norm w)).1
  have hw : w =
      Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I) +
        Complex.digamma (((sigma + 1 / 2 : ℝ) : ℂ) + (tau : ℂ) * I) -
        Complex.digamma (((sigma + 7 / 12 : ℝ) : ℂ) + (tau : ℂ) * I) -
        Complex.digamma (((sigma + 11 / 12 : ℝ) : ℂ) + (tau : ℂ) * I) := by
    dsimp only [w]
    ring
  rw [hw] at hre
  rw [hw] at hnorm
  linarith

theorem d4BMPositiveStripTransferLogSlope_re_pos
    {sigma tau : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1 / 4)
    (htau : 13 / 8 < |tau|) :
    0 < (d4BMPositiveStripTransferLogSlope
      ((sigma : ℂ) + (tau : ℂ) * I)).re := by
  have hlog := two_lt_log_twoHundredFiftySix_div_twentySeven
  have hrat := positiveStrip_rationalSlope_re_gt_neg_half hsigma0 hsigma1 htau
  have hgam := positiveStrip_digammaSlope_re_gt_neg_three_halves hsigma0 htau
  have hgam' :
      (Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I) +
        Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I + 1 / 2) -
        Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I + 7 / 12) -
        Complex.digamma ((sigma : ℂ) + (tau : ℂ) * I + 11 / 12)).re >
          -(3 / 2 : ℝ) := by
    convert hgam using 1
    all_goals push_cast; ring_nf
  unfold d4BMPositiveStripTransferLogSlope
  simp only [add_re, sub_re, ofReal_re]
  simp only [add_re, sub_re] at hrat hgam'
  nlinarith [hlog, hrat, hgam']

lemma ne_neg_nat_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    z ≠ -(m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  exact hz (by simpa using him)

lemma d4BM_log_constant_identity :
    (4 : ℂ) * Complex.log 4 - 3 * Complex.log 3 =
      (Real.log (256 / 27 : ℝ) : ℂ) := by
  have hreal :
      4 * Real.log 4 - 3 * Real.log 3 = Real.log (256 / 27 : ℝ) := by
    rw [show (256 / 27 : ℝ) = 4 ^ (4 : ℕ) / 3 ^ (3 : ℕ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have h4 : Complex.log (4 : ℂ) = (Real.log 4 : ℂ) :=
    (Complex.ofReal_log (by norm_num)).symm
  have h3 : Complex.log (3 : ℂ) = (Real.log 3 : ℂ) :=
    (Complex.ofReal_log (by norm_num)).symm
  rw [h4, h3]
  exact_mod_cast hreal

theorem d4BMPositiveStripTransfer_rawLogSlope_eq
    {u : ℂ} (hu : u.im ≠ 0) :
    4 * Complex.digamma (4 * u - 2) - Complex.digamma (u - 5 / 4) -
        3 * Complex.digamma (3 * u - 5 / 4) =
      d4BMPositiveStripTransferLogSlope u := by
  have hoff (a : ℂ) (ha : a.im = 0) (m : ℕ) : u - a ≠ -(m : ℂ) := by
    apply ne_neg_nat_of_im_ne_zero
    simp only [sub_im, ha, sub_zero]
    exact hu
  have h4off (m : ℕ) :
      (4 : ℂ) * (u - 1 / 2) ≠ -(m : ℂ) := by
    apply ne_neg_nat_of_im_ne_zero
    have him : ((4 : ℂ) * (u - 1 / 2)).im = 4 * u.im := by
      norm_num [Complex.mul_im, Complex.sub_im]
    rw [him]
    exact mul_ne_zero (by norm_num) hu
  have h3off (m : ℕ) :
      (3 : ℂ) * (u - 5 / 12) ≠ -(m : ℂ) := by
    apply ne_neg_nat_of_im_ne_zero
    have him : ((3 : ℂ) * (u - 5 / 12)).im = 3 * u.im := by
      norm_num [Complex.mul_im, Complex.sub_im]
    rw [him]
    exact mul_ne_zero (by norm_num) hu
  have h4 := GaloisForLFunctions.digamma_multiplication_rescaled
    (n := 4) (by norm_num) h4off
  have h3 := GaloisForLFunctions.digamma_multiplication_rescaled
    (n := 3) (by norm_num) h3off
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h4 h3
  norm_num at h4 h3
  have hr1 := Complex.digamma_apply_add_one (u - 1 / 2)
    (hoff (1 / 2) (by norm_num))
  have hr2 := Complex.digamma_apply_add_one (u - 5 / 4)
    (hoff (5 / 4) (by norm_num))
  have hr3 := Complex.digamma_apply_add_one (u - 5 / 12)
    (hoff (5 / 12) (by norm_num))
  have hr4 := Complex.digamma_apply_add_one (u - 1 / 12)
    (hoff (1 / 12) (by norm_num))
  unfold d4BMPositiveStripTransferLogSlope
  rw [← d4BM_log_constant_identity]
  ring_nf at h4 h3 hr1 hr2 hr3 hr4 ⊢
  linear_combination -h4 + h3 - hr1 + hr2 + hr3 + hr4

lemma hasDerivAt_Gamma_regular {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    HasDerivAt Complex.Gamma (Complex.digamma s * Complex.Gamma s) s := by
  have hd := (Complex.differentiableAt_Gamma s hs).hasDerivAt
  have hne := Complex.Gamma_ne_zero hs
  have hlog : Complex.digamma s = deriv Complex.Gamma s / Complex.Gamma s := by
    rw [Complex.digamma_def, logDeriv_apply]
  have heq : Complex.digamma s * Complex.Gamma s = deriv Complex.Gamma s := by
    rw [hlog]
    exact div_mul_cancel₀ _ hne
  rwa [heq]

lemma d4BM_four_mul_sub_two_off_poles {u : ℂ} (hu : u.im ≠ 0) (m : ℕ) :
    4 * u - 2 ≠ -(m : ℂ) := by
  apply ne_neg_nat_of_im_ne_zero
  have him : (4 * u - 2).im = 4 * u.im := by
    norm_num [Complex.mul_im, Complex.sub_im]
  rw [him]
  exact mul_ne_zero (by norm_num) hu

lemma d4BM_sub_five_fourths_off_poles {u : ℂ} (hu : u.im ≠ 0) (m : ℕ) :
    u - 5 / 4 ≠ -(m : ℂ) := by
  apply ne_neg_nat_of_im_ne_zero
  norm_num [Complex.sub_im]
  exact hu

lemma d4BM_three_mul_sub_five_fourths_off_poles
    {u : ℂ} (hu : u.im ≠ 0) (m : ℕ) :
    3 * u - 5 / 4 ≠ -(m : ℂ) := by
  apply ne_neg_nat_of_im_ne_zero
  have him : (3 * u - 5 / 4).im = 3 * u.im := by
    norm_num [Complex.mul_im, Complex.sub_im]
  rw [him]
  exact mul_ne_zero (by norm_num) hu

lemma d4BM_neg_half_off_poles (m : ℕ) : (-1 / 2 : ℂ) ≠ -(m : ℂ) := by
  cases m with
  | zero => norm_num
  | succ m =>
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith

def d4BMPositiveStripTransferNormalized (u : ℂ) : ℂ :=
  Complex.Gamma (4 * u - 2) * Complex.Gamma (-1 / 2 : ℂ) *
    (Complex.Gamma (u - 5 / 4))⁻¹ *
      (Complex.Gamma (3 * u - 5 / 4))⁻¹

lemma d4BMPositiveStripTransferProfile_eq_normalized (u : ℂ) :
    d4BMPositiveStripTransferProfile u =
      d4BMPositiveStripTransferNormalized u := by
  unfold d4BMPositiveStripTransferProfile d4BMSecondHarmonicTransferOfRho
    d4BMPositiveStripTransferNormalized
  ring_nf

theorem hasDerivAt_d4BMPositiveStripTransferNormalized
    {u : ℂ} (hu : u.im ≠ 0) :
    HasDerivAt d4BMPositiveStripTransferNormalized
      (d4BMPositiveStripTransferNormalized u *
        d4BMPositiveStripTransferLogSlope u) u := by
  have hlin4 : HasDerivAt (fun w : ℂ => 4 * w - 2) 4 u := by
    simpa using ((hasDerivAt_id u).const_mul 4).sub_const 2
  have hlin1 : HasDerivAt (fun w : ℂ => w - 5 / 4) 1 u := by
    simpa using (hasDerivAt_id u).sub_const (5 / 4)
  have hlin3 : HasDerivAt (fun w : ℂ => 3 * w - 5 / 4) 3 u := by
    simpa using ((hasDerivAt_id u).const_mul 3).sub_const (5 / 4)
  have hA := (hasDerivAt_Gamma_regular
    (d4BM_four_mul_sub_two_off_poles hu)).comp u hlin4
  have hB := (hasDerivAt_Gamma_regular
    (d4BM_sub_five_fourths_off_poles hu)).comp u hlin1
  have hD := (hasDerivAt_Gamma_regular
    (d4BM_three_mul_sub_five_fourths_off_poles hu)).comp u hlin3
  have hBne : Complex.Gamma (u - 5 / 4) ≠ 0 :=
    Complex.Gamma_ne_zero (d4BM_sub_five_fourths_off_poles hu)
  have hDne : Complex.Gamma (3 * u - 5 / 4) ≠ 0 :=
    Complex.Gamma_ne_zero (d4BM_three_mul_sub_five_fourths_off_poles hu)
  have hprod := ((hA.mul_const (Complex.Gamma (-1 / 2 : ℂ))).mul
    (hB.inv hBne)).mul (hD.inv hDne)
  refine hprod.congr_deriv ?_
  rw [← d4BMPositiveStripTransfer_rawLogSlope_eq hu]
  unfold d4BMPositiveStripTransferNormalized
  simp only [Function.comp_apply, Pi.inv_apply, Pi.mul_apply]
  field_simp [hBne, hDne]
  ring

theorem hasDerivAt_d4BMPositiveStripTransferProfile
    {u : ℂ} (hu : u.im ≠ 0) :
    HasDerivAt d4BMPositiveStripTransferProfile
      (d4BMPositiveStripTransferProfile u *
        d4BMPositiveStripTransferLogSlope u) u := by
  have hfun : d4BMPositiveStripTransferProfile =
      d4BMPositiveStripTransferNormalized := by
    funext w
    exact d4BMPositiveStripTransferProfile_eq_normalized w
  rw [hfun]
  exact hasDerivAt_d4BMPositiveStripTransferNormalized hu

lemma d4BMPositiveStripTransferProfile_ne_zero
    {u : ℂ} (hu : u.im ≠ 0) :
    d4BMPositiveStripTransferProfile u ≠ 0 := by
  rw [d4BMPositiveStripTransferProfile_eq_normalized]
  unfold d4BMPositiveStripTransferNormalized
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (Complex.Gamma_ne_zero (d4BM_four_mul_sub_two_off_poles hu))
        (Complex.Gamma_ne_zero d4BM_neg_half_off_poles))
      (inv_ne_zero (Complex.Gamma_ne_zero
        (d4BM_sub_five_fourths_off_poles hu))))
    (inv_ne_zero (Complex.Gamma_ne_zero
      (d4BM_three_mul_sub_five_fourths_off_poles hu)))

lemma d4BM_logSlope_mul_conj_re
    (F L : ℂ) : ((F * L) * (starRingEnd ℂ) F).re =
      Complex.normSq F * L.re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im, Complex.normSq_apply]
  ring

theorem strictMonoOn_normSq_d4BMPositiveStripTransferProfile
    {tau : ℝ} (htau : 13 / 8 < |tau|) :
    StrictMonoOn
      (fun sigma : ℝ => Complex.normSq
        (d4BMPositiveStripTransferProfile
          ((sigma : ℂ) + (tau : ℂ) * I)))
      (Set.Ioo 0 (1 / 4)) := by
  have htau0 : tau ≠ 0 := by
    intro h
    rw [h, abs_zero] at htau
    norm_num at htau
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 (1 / 4))
  · exact continuousOn_of_forall_continuousAt fun sigma hsigma => by
      have hu : (((sigma : ℂ) + (tau : ℂ) * I).im) ≠ 0 := by
        simpa using htau0
      exact (HTGeometry.hasDerivAt_normSq_horizontal_general
        d4BMPositiveStripTransferProfile tau sigma
        (hasDerivAt_d4BMPositiveStripTransferProfile hu).differentiableAt).continuousAt
  · intro sigma hsigma
    rw [interior_Ioo] at hsigma
    have hu : (((sigma : ℂ) + (tau : ℂ) * I).im) ≠ 0 := by
      simpa using htau0
    have hF := hasDerivAt_d4BMPositiveStripTransferProfile hu
    have hsq := HTGeometry.hasDerivAt_normSq_horizontal_general
      d4BMPositiveStripTransferProfile tau sigma hF.differentiableAt
    rw [hsq.deriv, hF.deriv, d4BM_logSlope_mul_conj_re]
    have hprofile : 0 < Complex.normSq
        (d4BMPositiveStripTransferProfile
          ((sigma : ℂ) + (tau : ℂ) * I)) :=
      Complex.normSq_pos.mpr (d4BMPositiveStripTransferProfile_ne_zero hu)
    have hslope := d4BMPositiveStripTransferLogSlope_re_pos
      hsigma.1 hsigma.2 htau
    positivity

lemma d4BMPositiveStripTransferProfile_rho_div_four (rho : ℂ) :
    d4BMPositiveStripTransferProfile (rho / 4) =
      d4BMSecondHarmonicTransferOfRho (1 - rho) := by
  unfold d4BMPositiveStripTransferProfile
  congr 1
  ring

lemma d4BMPositiveStripTransferProfile_one_sub_conj_div_four (rho : ℂ) :
    d4BMPositiveStripTransferProfile ((1 - (starRingEnd ℂ) rho) / 4) =
      d4BMSecondHarmonicTransferOfRho ((starRingEnd ℂ) rho) := by
  unfold d4BMPositiveStripTransferProfile
  congr 1
  ring

theorem d4BMSecondHarmonicTransfer_reflect_conj_collision_iff
    {rho : ℂ} (hre0 : 0 < rho.re) (hre1 : rho.re < 1)
    (him : 13 / 2 < |rho.im|) :
    d4BMSecondHarmonicTransferOfRho (1 - rho) =
        d4BMSecondHarmonicTransferOfRho ((starRingEnd ℂ) rho) ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hcollision
    have htau : 13 / 8 < |rho.im / 4| := by
      rw [abs_div]
      norm_num
      nlinarith
    have hmono := strictMonoOn_normSq_d4BMPositiveStripTransferProfile htau
    have hsigma1 : rho.re / 4 ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
      constructor <;> nlinarith
    have hsigma2 : (1 - rho.re) / 4 ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
      constructor <;> nlinarith
    have hprofile :
        d4BMPositiveStripTransferProfile (rho / 4) =
          d4BMPositiveStripTransferProfile
            ((1 - (starRingEnd ℂ) rho) / 4) := by
      rw [d4BMPositiveStripTransferProfile_rho_div_four,
        d4BMPositiveStripTransferProfile_one_sub_conj_div_four]
      exact hcollision
    have hu1 : rho / 4 =
        (((rho.re / 4 : ℝ) : ℂ) + ((rho.im / 4 : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
    have hu2 : (1 - (starRingEnd ℂ) rho) / 4 =
        ((((1 - rho.re) / 4 : ℝ) : ℂ) +
          ((rho.im / 4 : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
    rw [hu1, hu2] at hprofile
    have hnorm := congrArg Complex.normSq hprofile
    have hsigma := hmono.injOn hsigma1 hsigma2 hnorm
    nlinarith
  · intro hre
    have hpoint : 1 - rho = (starRingEnd ℂ) rho := by
      apply Complex.ext
      · simp only [sub_re, one_re, Complex.conj_re]
        linarith
      · simp
    rw [hpoint]

lemma d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar (q : XiZeroCopy) :
    d4BMXiSecondHarmonicBoundaryTransfer q =
      d4BMSecondHarmonicTransferOfRho (q.1 : ℂ) := by
  unfold d4BMXiSecondHarmonicBoundaryTransfer
    d4BMGravitationalNormalizableBoundaryTransfer
    d4BMSecondHarmonicTransferOfRho
  rw [d4BMGravitationalRadialC_secondHarmonic,
    d4BMGravitationalHypergeometricA_secondHarmonic,
    d4BMGravitationalHypergeometricB_secondHarmonic,
    d4ThetaTeukolskyRho_xiSpectralPoint]

theorem d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff
    (q : XiZeroCopy) :
    d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar,
    d4BMXiSecondHarmonicBoundaryTransfer_eq_scalar]
  change d4BMSecondHarmonicTransferOfRho (1 - (q.1 : ℂ)) =
      d4BMSecondHarmonicTransferOfRho ((starRingEnd ℂ) (q.1 : ℂ)) ↔
    (q.1 : ℂ).re = 1 / 2
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  by_cases hlow : |(q.1 : ℂ).im| ≤ 243 / 20
  · have hline := xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le
      (243 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths q hlow
    constructor
    · intro _
      exact hline
    · intro _
      have hpoint : 1 - (q.1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := by
        apply Complex.ext
        · simp only [sub_re, one_re, Complex.conj_re]
          linarith
        · simp
      rw [hpoint]
  · have him : 13 / 2 < |(q.1 : ℂ).im| := by
      have hhigh : 243 / 20 < |(q.1 : ℂ).im| := lt_of_not_ge hlow
      nlinarith
    exact d4BMSecondHarmonicTransfer_reflect_conj_collision_iff
      hstrip.1 hstrip.2 him

theorem d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_re_eq_half
    (q : XiZeroCopy) :
    d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_transfer_eq,
    d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff]

theorem d4BMXiFESchwarzHasDirectHelicityDarkKernel_iff_re_eq_half
    (q : XiZeroCopy) :
    d4BMXiFESchwarzHasDirectHelicityDarkKernel q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiFESchwarzHasDirectHelicityDarkKernel_iff_transfer_eq,
    d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff]

end

end RHTower
