import GaloisForLFunctions.ThetaCuspSections.ParabolicCurrentCore

/-!
# Curvature paid by the real endpoint pole budget

Comparing real reciprocal squares with endpoint poles retains their cancellation.
The exact zero sum then bounds the complete source's second moment and extends
its parabolic cosine minorant to radius `13/2`.
-/

open Complex MeasureTheory Set
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar
open GaloisForLFunctions.VerifiedHeightRungs

private theorem reciprocal_real_comparison {z : ℂ} (hz : 81 / 4 ≤ z.re) :
    (z⁻¹).re ≤ 82 / 81 * ((z + 1 / 4)⁻¹).re := by
  have hA : 0 < z.re := by linarith only [hz]
  have hD : 0 < z.re ^ 2 + z.im ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hA) (sq_nonneg _)
  have hD' : 0 < (z.re + 1 / 4) ^ 2 + z.im ^ 2 := by positivity
  have hpaid := add_nonneg
    (mul_nonneg (mul_nonneg hA.le (by positivity : 0 ≤ z.re + 1 / 4))
      (sub_nonneg.mpr hz))
    (mul_nonneg (by positivity : 0 ≤ z.re + 41 / 2) (sq_nonneg z.im))
  have hre : (z + 1 / 4).re = z.re + 1 / 4 := by norm_num
  have him : (z + 1 / 4).im = z.im := by norm_num
  rw [Complex.inv_re, Complex.inv_re, Complex.normSq_apply, Complex.normSq_apply, hre, him]
  simp only [← sq]
  rw [← mul_div_assoc, div_le_div_iff₀ hD hD']
  nlinarith only [hpaid]

/-- The real reciprocal square is paid directly by its endpoint pole. -/
theorem reciprocalSquare_re_le_endpoint (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).re ≤
      82 / 81 * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have hρ := xiZeroCopy_eq_half_add q
  have hx : (xiSpectralPoint q).re = (q.1 : ℂ).im := by rw [hρ]; simp
  have hy : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by rw [hρ]; simp
  have hx2 : (41 / 2 : ℝ) < (xiSpectralPoint q).re ^ 2 := by
    rw [hx]
    exact xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hy2 : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
    rw [hy]
    nlinarith only [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  have hprod : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = xiSpectralPoint q ^ 2 + 1 / 4 := by
    rw [hρ]
    linear_combination (-(xiSpectralPoint q ^ 2)) * Complex.I_mul_I
  have hreal : 81 / 4 ≤ (xiSpectralPoint q ^ 2).re := by
    rw [sq, Complex.mul_re]
    nlinarith only [hx2, hy2]
  rw [xiZeroCopyReciprocalSquare, inv_pow, hprod, one_div]
  exact reciprocal_real_comparison hreal

/-- The complete theta source has a sharper quadratic curvature budget. -/
theorem second_moment_le_four_over_169 :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * thetaCuspFullSource x ≤ 4 / 169 * Xi 0 := by
  have hsum := summable_xiZeroCopyReciprocalSquare
  have hpoles := summable_inv_mul_one_sub
  have hre : (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q).re ≤
      82 / 81 * poleSharpConstant := by
    rw [Complex.re_tsum hsum]
    calc
      _ ≤ ∑' q : XiZeroCopy,
          82 / 81 * ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
        (hsum.mapL Complex.reCLM).tsum_le_tsum reciprocalSquare_re_le_endpoint
          ((hpoles.mapL Complex.reCLM).mul_left _)
      _ = _ := by
        rw [tsum_mul_left, ← Complex.re_tsum hpoles, tsum_inv_zero_mul_one_sub_zero_re]
  have h2 := Xi_secondDeriv_zero_eq_neg_two_mul_thetaCuspSecondMoment
  have h3 := Xi_secondDeriv_eq_center_mul_canonicalProduct_re 0
  rw [Complex.ofReal_zero, secondDeriv_xiCanonicalProduct_zero, Complex.neg_re] at h3
  have h4 := mul_le_mul_of_nonneg_left hre Xi_zero_pos.le
  have h5 := mul_le_mul_of_nonneg_left poleSharpConstant_le Xi_zero_pos.le
  nlinarith only [h2, h3, h4, h5, Xi_zero_pos.le]

/-- The complete cosine transform retains its parabolic minorant at radius `13/2`. -/
theorem Xi_ge_wide_center_parabola (b : ℝ) :
    Xi 0 * (1 - 4 * b ^ 2 / 169) ≤ Xi b := by
  have hsrc : IntegrableOn thetaCuspFullSource (Ioi 0) :=
    integrable_thetaCuspFullSource'.integrableOn
  have hsec : IntegrableOn (fun x : ℝ => x ^ 2 * thetaCuspFullSource x) (Ioi 0) :=
    integrable_thetaCuspSecondMoment.integrableOn
  have hcos : IntegrableOn (fun x : ℝ => thetaCuspFullSource x * Real.cos (b * x)) (Ioi 0) := by
    refine Integrable.mul_bdd (c := 1) hsrc (by fun_prop) (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (b * x)
  have hmono : ∫ x in Ioi (0 : ℝ), (thetaCuspFullSource x - b ^ 2 / 2 *
      (x ^ 2 * thetaCuspFullSource x)) ≤
      ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.cos (b * x) := by
    refine setIntegral_mono_on (hsrc.sub (hsec.const_mul _)) hcos measurableSet_Ioi fun x _ => ?_
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := b * x))
      (thetaCuspFullSource_pos x).le
    nlinarith only [h]
  rw [integral_sub hsrc (hsec.const_mul _), integral_const_mul] at hmono
  have hpaid := mul_le_mul_of_nonneg_left second_moment_le_four_over_169 (sq_nonneg b)
  have hmass := Xi_zero_eq_two_mul_integral_thetaCuspFullSource
  rw [Xi_eq_thetaCuspCosineRepresentation b, thetaCuspCosineRepresentation]
  nlinarith only [hmono, hpaid, hmass]

/-- The wider cosine minorant is nonnegative throughout its parabolic window. -/
theorem Xi_ge_wide_parabola {b : ℝ} (hb : |b| ≤ 13 / 2) :
    (49 / 100 : ℝ) * (1 - 4 * b ^ 2 / 169) ≤ Xi b := by
  have hb2 : b ^ 2 ≤ 169 / 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg b) hb 2
    norm_num only [sq_abs] at hh
    norm_num at hh ⊢
    exact hh
  have hw : 0 ≤ 1 - 4 * b ^ 2 / 169 := by linarith only [hb2]
  have hz : (49 / 100 : ℝ) ≤ Xi 0 := by
    have hh := Xi_zero_ge
    norm_num at hh ⊢
    exact hh
  exact (mul_le_mul_of_nonneg_right hz hw).trans (Xi_ge_wide_center_parabola b)

/-- The complete current retains a larger weighted core with an explicit source floor. -/
theorem current_ge_wide_parabolic {a b : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hb : |b| ≤ 13 / 2) :
    a / 275 * (1 - 4 * b ^ 2 / 169) ^ 2 ≤ current a b := by
  obtain ⟨hlog, hxi⟩ := re_logDeriv_xi_ge_thirteen_halves ha ha2 hb
  have him : 0.0076 * a ≤ (logDeriv XiC ((b : ℂ) - (a : ℂ) * I)).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using hlog
  have hnn : ∀ a' ∈ Ioo 0 a, 0 ≤ current a' b := fun a' ha' =>
    current_nonneg_of_rhVerifiedThrough (T := 66) ha'.1 (by
      norm_num
      exact HadamardBudget.rhVerifiedThrough_sixtySeven) (hb.trans (by norm_num))
  have hN := sq_Xi_le_normSq ha.le hnn
  have hb2 : b ^ 2 ≤ 169 / 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg b) hb 2
    norm_num only [sq_abs] at hh
    norm_num at hh ⊢
    exact hh
  have hw : 0 ≤ (49 / 100 : ℝ) * (1 - 4 * b ^ 2 / 169) := by
    have : 0 ≤ 1 - 4 * b ^ 2 / 169 := by linarith only [hb2]
    positivity
  have hsq := pow_le_pow_left₀ hw (Xi_ge_wide_parabola hb) 2
  have hne : XiC ((b : ℂ) - (a : ℂ) * I) ≠ 0 := hxi
  change _ ≤ 2 * ((starRingEnd ℂ) (XiC ((b : ℂ) - (a : ℂ) * I)) *
    (-I * deriv XiC ((b : ℂ) - (a : ℂ) * I))).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hne, ← logDeriv_apply]
  have h1 := mul_le_mul (hsq.trans hN) him (by positivity : 0 ≤ 0.0076 * a)
    (Complex.normSq_nonneg (XiC ((b : ℂ) - (a : ℂ) * I)))
  have hp := mul_nonneg ha.le (sq_nonneg (1 - 4 * b ^ 2 / 169))
  nlinarith only [h1, hp]

#print axioms reciprocalSquare_re_le_endpoint
#print axioms second_moment_le_four_over_169
#print axioms Xi_ge_wide_center_parabola
#print axioms current_ge_wide_parabolic

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
