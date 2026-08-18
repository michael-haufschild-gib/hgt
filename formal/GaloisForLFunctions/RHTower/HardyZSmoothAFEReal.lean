import GaloisForLFunctions.RHTower.HardyZSmoothAFE
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualSeriesFreezing
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# The real form of the smooth approximate functional equation for Hardy's `Z`

Taking real parts of `hardyZ_eq_two_tsum_smoothAFE` turns each edge into a twisted Hardy
cosine/sine series.  This is the exact shape consumed by `abs_integral_mul_cos_hardyTwistPhase_le`:
every term is a real weight against `cos(θ(τ) − τ log n + φ)`.
-/

open Complex

noncomputable section

namespace RHTower

/-! ## Summability of the direct edge -/

theorem norm_natSucc_cpow_neg_linePt (n : ℕ) (τ : ℝ) :
    ‖((n : ℂ) + 1) ^ (-linePt τ)‖ = ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1
  unfold linePt
  simp

theorem smoothAFEDirectWeightedSeries_summable {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    Summable (fun n : ℕ =>
      ((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x)) := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := (1 : ℝ)) (by norm_num)
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hq : Summable (fun n : ℕ => (K * x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ))) :=
    hbase.mul_left (K * x)
  apply Summable.of_norm
  refine hq.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro n
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hratio : (0 : ℝ) < ((n : ℝ) + 1) / x := by positivity
  have hb := hcut hratio
  have hrpow : (((n : ℝ) + 1) / x) ^ (-(1 : ℝ)) = x / ((n : ℝ) + 1) := by
    rw [Real.rpow_neg_one, inv_div]
  rw [hrpow] at hb
  have hsplit : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) * (K * (x / ((n : ℝ) + 1)))
      = (K * x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
    have hpow : ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
        = ((n : ℝ) + 1) ^ ((1 / 2 : ℝ)) * ((n : ℝ) + 1) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hpos]
      congr 1
      norm_num
    have hhalf : ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) = (((n : ℝ) + 1) ^ ((1 / 2 : ℝ)))⁻¹ :=
      Real.rpow_neg hpos.le _
    have hone : ((n : ℝ) + 1) ^ (1 : ℝ) = (n : ℝ) + 1 := Real.rpow_one _
    have hhalfpos : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 / 2 : ℝ)) := Real.rpow_pos_of_pos hpos _
    rw [hpow, hhalf, hone]
    field_simp
  calc ‖((n : ℂ) + 1) ^ (-linePt τ) * smoothAFECutoff (((n : ℝ) + 1) / x)‖
      = ‖((n : ℂ) + 1) ^ (-linePt τ)‖ * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ := norm_mul _ _
    _ = ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) * ‖smoothAFECutoff (((n : ℝ) + 1) / x)‖ := by
        rw [norm_natSucc_cpow_neg_linePt]
    _ ≤ ((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) * (K * (x / ((n : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hpos.le _)
    _ = (K * x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := hsplit

/-! ## Real and imaginary parts of a twisted phase term -/

theorem re_ofReal_mul_exp_I_mul (c t : ℝ) (w : ℂ) :
    ((((c : ℝ) : ℂ) * Complex.exp (I * ((t : ℝ) : ℂ))) * w).re
      = c * (Real.cos t * w.re - Real.sin t * w.im) := by
  rw [show I * ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) * I by ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring

theorem re_ofReal_mul_exp_neg_I_mul (c t : ℝ) (w : ℂ) :
    ((((c : ℝ) : ℂ) * Complex.exp (-I * ((t : ℝ) : ℂ))) * w).re
      = c * (Real.cos t * w.re + Real.sin t * w.im) := by
  rw [show -I * ((t : ℝ) : ℂ) = I * (((-t : ℝ)) : ℂ) by push_cast; ring]
  rw [re_ofReal_mul_exp_I_mul c (-t) w, Real.cos_neg, Real.sin_neg]
  ring

/-! ## The real expansion -/

/-- **The real Gaussian smooth approximate functional equation for Hardy's `Z`.**  Each edge is a
twisted Hardy cosine/sine series with real weights. -/
theorem hardyZ_eq_two_tsum_smoothAFE_real {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    hardyZ τ =
      (∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFECutoff (((n : ℝ) + 1) / x)).re -
          Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFECutoff (((n : ℝ) + 1) / x)).im)) +
      (∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).re +
          Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).im)) -
      (Complex.exp (I * (gammaHardyTheta τ : ℂ)) *
        smoothAFEZetaShiftedPoleResidue (linePt τ) x).re := by
  have hcast : ∀ n : ℕ, ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((n : ℂ) + 1) := fun n => by push_cast; ring
  have hdirect := smoothAFEDirectWeightedSeries_summable hx τ
  have hdual := smoothAFEZetaDualWeightedSeries_summable hx τ τ
  have hS1 : Summable (fun n : ℕ =>
      ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        Complex.exp (I * ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) *
          smoothAFECutoff (((n : ℝ) + 1) / x)) := by
    have hm := hdirect.mul_left (Complex.exp (I * (gammaHardyTheta τ : ℂ)))
    refine hm.congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := exp_theta_mul_cpow_neg_linePt τ hpos
    rw [hcast n] at h
    rw [← mul_assoc, h]
  have hS2 : Summable (fun n : ℕ =>
      ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-I * ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) *
          smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)) := by
    have hm := hdual.mul_left (Complex.exp (-I * (gammaHardyTheta τ : ℂ)))
    refine hm.congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := exp_neg_theta_mul_cpow_linePt_sub_one τ hpos
    rw [hcast n] at h
    rw [← mul_assoc, h]
  have h1 : (∑' n : ℕ,
      ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        Complex.exp (I * ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) *
          smoothAFECutoff (((n : ℝ) + 1) / x)).re
      = ∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFECutoff (((n : ℝ) + 1) / x)).re -
          Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFECutoff (((n : ℝ) + 1) / x)).im) := by
    have hmap := Complex.reCLM.map_tsum hS1
    simp only [Complex.reCLM_apply] at hmap
    rw [hmap]
    exact tsum_congr fun n => re_ofReal_mul_exp_I_mul _ _ _
  have h2 : (∑' n : ℕ,
      ((((Real.sqrt ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        Complex.exp (-I * ((hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ : ℝ) : ℂ))) *
          smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).re
      = ∑' n : ℕ, (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).re +
          Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
            (smoothAFEZetaDualWeight τ (((n : ℝ) + 1) * x)).im) := by
    have hmap := Complex.reCLM.map_tsum hS2
    simp only [Complex.reCLM_apply] at hmap
    rw [hmap]
    exact tsum_congr fun n => re_ofReal_mul_exp_neg_I_mul _ _ _
  have hre := congrArg Complex.re (hardyZ_eq_two_tsum_smoothAFE hx τ)
  rw [Complex.ofReal_re, Complex.sub_re, Complex.add_re, h1, h2] at hre
  exact hre

end RHTower

end
