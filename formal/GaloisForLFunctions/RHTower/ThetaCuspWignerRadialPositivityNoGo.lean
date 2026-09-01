import GaloisForLFunctions.RHTower.ThetaCuspWignerProductFiberNormalForm
import GaloisForLFunctions.HTGeometry.BesselK1DerivRecurrence

/-!
# Theta Wigner radial-positivity no-go

The exact product-fibre normal form leaves a universal radial Fourier transform.  At radial scale
`c = 3`, its zero-frequency spatial profile is a strictly negative integrable function away from
the origin, so the transform is strictly negative.  The scale is attained by the actual ordered
theta pair `(n,m) = (1,1)` at an explicit centre.

This kills the pairwise-radial positivity lane toward the Hedenmalm endpoint: individual actual
theta-pair Wigner contributions cannot all be nonnegative, even at zero frequency.  Since full
center-mixed Fourier nonnegativity is equivalent to RH, any surviving proof must use cancellation
after divisor/product-fibre summation rather than positivity of each radial pair.

Positive survivor: the already exact fully coupled product-fibre sum remains viable; only the
pairwise-positive decomposition is ruled out.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

private theorem integrable_exp_neg_three_mul_cosh_two :
    Integrable (fun v : ℝ => Real.exp (-3 * Real.cosh (2 * v))) := by
  have hC := (HTGeometry.integrable_exp_neg_cosh
    (z := (3 : ℂ)) (by norm_num)).re
  have hR : Integrable (fun t : ℝ => Real.exp (-3 * Real.cosh t)) := by
    convert hC using 1
    funext t
    have harg : -(3 : ℂ) * Complex.cosh (t : ℂ) =
        ((-3 * Real.cosh t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cosh]
      norm_cast
    rw [harg]
    exact (Complex.exp_ofReal_re _).symm
  exact (MeasureTheory.integrable_comp_mul_left_iff
    (g := fun t : ℝ => Real.exp (-3 * Real.cosh t)) (by norm_num)).2 hR

private theorem integrable_cosh_two_mul_exp_neg_three_mul_cosh_two :
    Integrable (fun v : ℝ =>
      Real.cosh (2 * v) * Real.exp (-3 * Real.cosh (2 * v))) := by
  have hC := (HTGeometry.integrable_coshPow_mul_exp_neg_cosh
    (z := (3 : ℂ)) (k := 1) (by norm_num) (by norm_num)).re
  have hR : Integrable (fun t : ℝ =>
      Real.cosh t * Real.exp (-3 * Real.cosh t)) := by
    convert hC using 1
    funext t
    have hcosh : Complex.cosh (t : ℂ) = (Real.cosh t : ℂ) :=
      (Complex.ofReal_cosh t).symm
    have harg : -(3 : ℂ) * Complex.cosh (t : ℂ) =
        ((-3 * Real.cosh t : ℝ) : ℂ) := by
      rw [hcosh]
      norm_cast
    rw [harg, hcosh]
    simp only [pow_one]
    change Real.cosh t * Real.exp (-3 * Real.cosh t) =
      (((Real.cosh t : ℝ) : ℂ) *
        Complex.exp (((-3 * Real.cosh t : ℝ) : ℂ))).re
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_re,
      Complex.exp_ofReal_im, zero_mul, sub_zero]
  exact (MeasureTheory.integrable_comp_mul_left_iff
    (g := fun t : ℝ => Real.cosh t * Real.exp (-3 * Real.cosh t))
      (by norm_num)).2 hR

private theorem integrable_neg_thetaCuspWignerRadialProfile_three :
    Integrable (fun v : ℝ => -thetaCuspWignerRadialProfile 3 v) := by
  have h := integrable_cosh_two_mul_exp_neg_three_mul_cosh_two.sub
    integrable_exp_neg_three_mul_cosh_two
  convert h.const_mul 162 using 1
  funext v
  unfold thetaCuspWignerRadialProfile
  simp only [Pi.sub_apply]
  ring

private theorem neg_thetaCuspWignerRadialProfile_three_nonneg (v : ℝ) :
    0 ≤ -thetaCuspWignerRadialProfile 3 v := by
  unfold thetaCuspWignerRadialProfile
  have hc := Real.one_le_cosh (2 * v)
  have he := Real.exp_pos (-3 * Real.cosh (2 * v))
  nlinarith

private theorem Ioc_zero_one_subset_support_neg_thetaCuspWignerRadialProfile_three :
    Ioc (0 : ℝ) 1 ⊆ Function.support
      (fun v : ℝ => -thetaCuspWignerRadialProfile 3 v) := by
  intro v hv
  change -thetaCuspWignerRadialProfile 3 v ≠ 0
  unfold thetaCuspWignerRadialProfile
  have hv0 : v ≠ 0 := ne_of_gt hv.1
  have hc : 1 < Real.cosh (2 * v) :=
    Real.one_lt_cosh.mpr (mul_ne_zero (by norm_num) hv0)
  have he := Real.exp_pos (-3 * Real.cosh (2 * v))
  nlinarith

/-- Universal radial positivity already fails at zero Fourier frequency. -/
theorem thetaCuspWignerRadialTransform_three_zero_re_neg :
    (thetaCuspWignerRadialTransform 3 0).re < 0 := by
  let f : ℝ → ℝ := fun v => -thetaCuspWignerRadialProfile 3 v
  have hf0 : 0 ≤ f := by
    intro v
    exact neg_thetaCuspWignerRadialProfile_three_nonneg v
  have hfi : Integrable f :=
    integrable_neg_thetaCuspWignerRadialProfile_three
  have hsupp : 0 < volume (Function.support f) := by
    have hmono : volume (Ioc (0 : ℝ) 1) ≤ volume (Function.support f) :=
      measure_mono Ioc_zero_one_subset_support_neg_thetaCuspWignerRadialProfile_three
    rw [Real.volume_Ioc] at hmono
    exact lt_of_lt_of_le (by norm_num) hmono
  have hint : 0 < ∫ v : ℝ, f v :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg hf0 hfi).2 hsupp
  change (∫ v : ℝ,
    ((thetaCuspWignerRadialProfile 3 v : ℂ) *
      thetaWignerDifferencePhase 0 v)).re < 0
  simp only [thetaWignerDifferencePhase, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  have hprof : Integrable (fun v : ℝ => thetaCuspWignerRadialProfile 3 v) := by
    refine hfi.neg.congr ?_
    filter_upwards with v
    dsimp only [f, Pi.neg_apply]
    simp
  have hre :
      (∫ v : ℝ, (thetaCuspWignerRadialProfile 3 v : ℂ)).re =
        ∫ v : ℝ, thetaCuspWignerRadialProfile 3 v := by
    have h :=
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hprof.ofReal).symm
    convert h using 1 <;> simp
  rw [hre]
  dsimp only [f] at hint
  rw [MeasureTheory.integral_neg] at hint
  linarith

/-- Actual first-atom pair whose recentered zero-frequency Wigner contribution is negative. -/
theorem thetaCuspSourcePairWigner_one_one_logScale_three_zero_re_neg :
    (thetaCuspSourcePairWigner 1 1
      (Real.log (3 / (2 * Real.pi)) / 2) 0).re < 0 := by
  let u : ℝ := Real.log (3 / (2 * Real.pi)) / 2
  have harg : 0 < (3 / (2 * Real.pi) : ℝ) := by positivity
  have hscale : thetaCuspWignerAtomScale 1 1 u = 3 := by
    unfold thetaCuspWignerAtomScale
    dsimp only [u]
    rw [show 2 * (Real.log (3 / (2 * Real.pi)) / 2) =
      Real.log (3 / (2 * Real.pi)) by ring, Real.exp_log harg]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hfactor :
      thetaCuspSourcePairWigner 1 1 u 0 =
        (Real.exp u : ℂ) * thetaCuspWignerRadialTransform 3 0 := by
    rw [thetaCuspSourcePairWigner_eq_phase_mul_radial
      (n := 1) (m := 1) (by norm_num) (by norm_num), hscale]
    simp [thetaCuspWignerDivisorRatioPhase]
  change (thetaCuspSourcePairWigner 1 1 u 0).re < 0
  rw [hfactor, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg (Real.exp_pos u)
    thetaCuspWignerRadialTransform_three_zero_re_neg

/-- **Pairwise-radial Wigner route kill.**  Real Wigner contributions of actual positive theta
atom pairs are not pointwise nonnegative.  Therefore the RH-equivalent full Hedenmalm current
cannot be proved by assigning a nonnegative radial Fourier contribution to every ordered pair. -/
theorem not_forall_thetaCuspSourcePairWigner_re_nonneg :
    ¬ ∀ n m : ℕ, 0 < n → 0 < m → ∀ u b : ℝ,
      0 ≤ (thetaCuspSourcePairWigner n m u b).re := by
  intro h
  have hnonneg := h 1 1 (by norm_num) (by norm_num)
    (Real.log (3 / (2 * Real.pi)) / 2) 0
  linarith [thetaCuspSourcePairWigner_one_one_logScale_three_zero_re_neg]

end

end RHTower
