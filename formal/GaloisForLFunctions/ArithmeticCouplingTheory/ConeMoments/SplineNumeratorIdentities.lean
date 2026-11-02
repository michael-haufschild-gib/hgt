import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineBlaschkeBounds

/-!
# Fourier and reflection identities for the spline numerator

The finite shifted Fourier polynomial equals `exp(itx) sinh(δ + ix)^8`.
The quotient of this spline numerator by its complex conjugate is the
explicit eighth-power Blaschke factor. These identities identify the two
pairings of the real moment Jacobian with the bounded primitive estimates.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma splineCoefficient_phase (δ x : ℝ) (j : Fin 9) :
    (splineCoefficient δ j : ℂ)*phase (splineShift j) x =
      (1/256 : ℂ)*((-Complex.exp (-((δ : ℂ)+(x : ℂ)*Complex.I)))^j.val*
        (Complex.exp ((δ : ℂ)+(x : ℂ)*Complex.I))^(8-j.val)*(Nat.choose 8 j.val : ℂ)) := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hj : j.val ≤ 8 := by omega
  have he : Complex.exp (-z)^j.val*Complex.exp z^(8-j.val)=
      Complex.exp ((splineShift j : ℂ)*z) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [splineShift, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast, Nat.cast_sub hj, Nat.cast_ofNat]
    ring
  have hexp := exp_real_phase (splineShift j) δ x
  simp only [splineCoefficient, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  rw [show (-Complex.exp (-z))^j.val=(-1 : ℂ)^j.val*Complex.exp (-z)^j.val by
    rw [← mul_pow]; congr 1; ring]
  calc
    _ = ((-1 : ℂ)^j.val*(Nat.choose 8 j.val : ℂ)/256)*
        ((Real.exp (splineShift j*δ) : ℂ)*phase (splineShift j) x) := by ring
    _ = ((-1 : ℂ)^j.val*(Nat.choose 8 j.val : ℂ)/256)*
        (Complex.exp (-z)^j.val*Complex.exp z^(8-j.val)) := by rw [he, hexp]
    _ = _ := by ring

/-- The finite Fourier expansion is exactly the cubic-spline numerator. -/
theorem shiftedSplineNumerator_eq (δ t x : ℝ) :
    shiftedSplineNumerator δ t x=phase t x*Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8 := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hsum : (∑ j : Fin 9, (splineCoefficient δ j : ℂ)*phase (splineShift j) x)=
      Complex.sinh z^8 := by
    simp_rw [splineCoefficient_phase]
    rw [← mul_sum]
    have hb := add_pow (-Complex.exp (-z)) (Complex.exp z) 8
    rw [← Fin.sum_univ_eq_sum_range] at hb
    rw [← hb, Complex.sinh, div_pow]
    ring
  unfold shiftedSplineNumerator
  simp only [phase_freq_add]
  calc
    _ = phase t x*∑ j : Fin 9, (splineCoefficient δ j : ℂ)*phase (splineShift j) x := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hsum]

lemma phase_mul_opposite (u x : ℝ) : phase u x*phase (-u) x=1 := by
  rw [← phase_freq_add, add_neg_cancel, phase_zero]

lemma phase_ne_zero (u x : ℝ) : phase u x ≠ 0 := by
  intro h
  have hn := phase_norm u x
  rw [h, norm_zero] at hn
  norm_num at hn

lemma spline_sinh_ne_zero {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I) ≠ 0 := by
  rw [sinh_exp_factor]
  have he := exp_real_phase (-2) δ x
  simp only [Complex.ofReal_neg, Complex.ofReal_ofNat] at he
  rw [he]
  apply mul_ne_zero (div_ne_zero (Complex.exp_ne_zero _) (by norm_num))
  simpa only [splineRatio, phase_neg_arg, neg_neg] using
    splineBlaschke_denominator_ne_zero hδ (-x)

/-- Reflection of the spline numerator is exactly the eighth-power Blaschke factor. -/
theorem splineBlaschke_eq_sinh_ratio {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    splineBlaschke δ x=Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8 /
      (starRingEnd ℂ) (Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8) := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hpp : phase 1 x*phase 1 x=phase 2 x := by
    rw [← phase_freq_add]; norm_num
  have hpm : phase (-1) x*phase 1 x=1 := by
    rw [← phase_freq_add]; norm_num [phase_zero]
  have h2m : phase (-2) x*phase 2 x=1 := by
    rw [← phase_freq_add]; norm_num [phase_zero]
  have he : Complex.exp z=(Real.exp δ : ℂ)*phase 1 x := by
    simpa only [Complex.ofReal_one, one_mul] using exp_real_phase 1 δ x
  have he2 : Complex.exp (-2*z)=(splineRatio δ : ℂ)*phase (-2) x := by
    simpa only [splineRatio, Complex.ofReal_neg, Complex.ofReal_ofNat] using exp_real_phase (-2) δ x
  have hzbar : (starRingEnd ℂ) z=(δ : ℂ)+((-x : ℝ) : ℂ)*Complex.I := by
    dsimp only [z]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  have hebar : Complex.exp ((starRingEnd ℂ) z)=(Real.exp δ : ℂ)*phase (-1) x := by
    rw [hzbar]
    simpa only [Complex.ofReal_one, one_mul, phase_neg_arg] using exp_real_phase 1 δ (-x)
  have he2bar : Complex.exp (-2*((starRingEnd ℂ) z))=
      (splineRatio δ : ℂ)*phase 2 x := by
    rw [hzbar]
    simpa only [splineRatio, Complex.ofReal_neg, Complex.ofReal_ofNat, phase_neg_arg, neg_neg]
      using exp_real_phase (-2) δ (-x)
  have hn : Complex.sinh z*phase 1 x=
      (Real.exp δ : ℂ)/2*(phase 2 x-(splineRatio δ : ℂ)) := by
    rw [sinh_exp_factor, he, he2]
    calc
      _ = (Real.exp δ : ℂ)/2*(phase 1 x*phase 1 x-
          (splineRatio δ : ℂ)*(phase (-2) x*(phase 1 x*phase 1 x))) := by ring
      _ = _ := by rw [hpp, h2m]; ring
  have hd : (starRingEnd ℂ) (Complex.sinh z)*phase 1 x=
      (Real.exp δ : ℂ)/2*(1-(splineRatio δ : ℂ)*phase 2 x) := by
    rw [← Complex.sinh_conj, sinh_exp_factor, hebar, he2bar]
    calc
      _ = (Real.exp δ : ℂ)/2*(phase (-1) x*phase 1 x)*
          (1-(splineRatio δ : ℂ)*phase 2 x) := by ring
      _ = _ := by rw [hpm]; ring
  have hs : (starRingEnd ℂ) (Complex.sinh z) ≠ 0 := by
    intro h
    apply spline_sinh_ne_zero hδ x
    simpa only [Complex.conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have hfrac : Complex.sinh z/(starRingEnd ℂ) (Complex.sinh z)=
      (phase 2 x-(splineRatio δ : ℂ))/(1-(splineRatio δ : ℂ)*phase 2 x) := by
    apply (div_eq_div_iff hs (splineBlaschke_denominator_ne_zero hδ x)).mpr
    apply mul_right_cancel₀ (phase_ne_zero 1 x)
    calc
      _ = (Complex.sinh z*phase 1 x)*(1-(splineRatio δ : ℂ)*phase 2 x) := by ring
      _ = ((phase 2 x-(splineRatio δ : ℂ))*(starRingEnd ℂ) (Complex.sinh z))*phase 1 x := by
        rw [hn]
        calc
          _ = (phase 2 x-(splineRatio δ : ℂ))*
              ((Real.exp δ : ℂ)/2*(1-(splineRatio δ : ℂ)*phase 2 x)) := by ring
          _ = _ := by rw [← hd]; ring
  rw [splineBlaschke, ← hfrac, div_pow, map_pow]

#print axioms shiftedSplineNumerator_eq
#print axioms splineBlaschke_eq_sinh_ratio
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
