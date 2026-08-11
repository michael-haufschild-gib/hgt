import GaloisForLFunctions.RHTower.HedenmalmThetaCompactFluxEnergy

/-!
# Reusable Cayley tools for theta boundary clocks

Small operator and scalar lemmas shared by direct and squared Cayley receivers.  The only
theta-specific statement is faithfulness of the pinned boundary observation on every canonical
Xi divisor eigenline.
-/

open Complex MeasureTheory

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Every eigenvalue of a strict contraction has modulus below one. -/
theorem norm_eigenvalue_lt_one_of_strict_contraction
    {T : ThetaH →L[ℂ] ThetaH} {x : ℂ} {v : ThetaH}
    (hT : ‖T‖ < 1) (hv0 : v ≠ 0) (hv : T v = x • v) :
    ‖x‖ < 1 := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hle : ‖x‖ * ‖v‖ ≤ ‖T‖ * ‖v‖ := by
    rw [← norm_smul, ← hv]
    exact T.le_opNorm v
  have hxle : ‖x‖ ≤ ‖T‖ := by nlinarith
  exact hxle.trans_lt hT

/-- Inversion of a unit Cayley denominator on an eigenline. -/
theorem ringInverse_one_sub_apply_of_eigen
    {T : ThetaH →L[ℂ] ThetaH} {x : ℂ} {v : ThetaH}
    (hunit : IsUnit (1 - T)) (hv0 : v ≠ 0) (hv : T v = x • v) :
    Ring.inverse (1 - T) v = (1 - x)⁻¹ • v := by
  have hx1 : 1 - x ≠ 0 := by
    intro hx
    have hker : (1 - T) v = 0 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hv]
      have : x = 1 := (sub_eq_zero.mp hx).symm
      rw [this, one_smul, sub_self]
    exact hv0 ((ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1 (by simpa using hker))
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  rw [← ContinuousLinearMap.mul_apply,
    Ring.mul_inverse_cancel _ hunit, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    map_smul, hv, smul_smul]
  rw [← sub_smul]
  congr 1
  field_simp
  simp

/-- Powers of a bounded operator preserve an eigenline with corresponding scalar power. -/
theorem pow_apply_of_complex_eigen
    {T : ThetaH →L[ℂ] ThetaH} {x : ℂ} {v : ThetaH}
    (hv : T v = x • v) (n : ℕ) :
    (T ^ n) v = x ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, hv, map_smul, ih,
        smul_smul, pow_succ]
      congr 1
      ring

/-- Every canonical theta divisor mode has nonzero rank-two boundary output. -/
theorem pinnedBoundaryCLM_thetaXiDivisorEigenvector_ne_zero (q : XiZeroCopy) :
    pinnedBoundaryCLM (thetaXiDivisorEigenvector q) ≠ 0 := by
  intro hzero
  have hm := (pinnedBoundaryCLM_eq_zero_iff (thetaXiDivisorEigenvector q)).1 hzero
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  apply hsqrt
  rw [← pinnedMean_thetaDivisorEigenvector
    (xiSpectralPoint q) (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q)]
  exact hm.1

/-- Cayley transform of an imaginary-axis scalar lies on unit circle. -/
theorem norm_one_add_eq_norm_one_sub_of_re_eq_zero
    {x : ℂ} (hx : x.re = 0) :
    ‖1 + x‖ = ‖1 - x‖ := by
  have hsq : ‖1 + x‖ ^ 2 = ‖1 - x‖ ^ 2 := by
    calc
      ‖1 + x‖ ^ 2 = Complex.normSq (1 + x) := Complex.sq_norm (1 + x)
      _ = Complex.normSq (1 - x) := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hx]
        ring
      _ = ‖1 - x‖ ^ 2 := (Complex.sq_norm (1 - x)).symm
  nlinarith [norm_nonneg (1 + x), norm_nonneg (1 - x)]

theorem norm_cayley_eq_one_of_re_eq_zero
    {x : ℂ} (hx : x.re = 0) (hden : 1 - x ≠ 0) :
    ‖(1 + x) / (1 - x)‖ = 1 := by
  rw [norm_div, norm_one_add_eq_norm_one_sub_of_re_eq_zero hx,
    div_self (norm_ne_zero_iff.mpr hden)]

/-- Cayley transform strictly expands a right-half-plane scalar. -/
theorem one_lt_norm_cayley_of_re_pos
    {x : ℂ} (hx : 0 < x.re) (hden : 1 - x ≠ 0) :
    1 < ‖(1 + x) / (1 - x)‖ := by
  have hsq : ‖1 - x‖ ^ 2 < ‖1 + x‖ ^ 2 := by
    calc
      ‖1 - x‖ ^ 2 = Complex.normSq (1 - x) := Complex.sq_norm (1 - x)
      _ < Complex.normSq (1 + x) := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
        nlinarith
      _ = ‖1 + x‖ ^ 2 := (Complex.sq_norm (1 + x)).symm
  have hnorm : ‖1 - x‖ < ‖1 + x‖ := by
    nlinarith [norm_nonneg (1 - x), norm_nonneg (1 + x)]
  rw [norm_div, one_lt_div (norm_pos_iff.mpr hden)]
  exact hnorm

end

end RHTower.HedenmalmThetaSource
