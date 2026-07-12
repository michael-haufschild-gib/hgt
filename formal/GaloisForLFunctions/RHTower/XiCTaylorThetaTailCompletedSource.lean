import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCancellation

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

theorem thetaCuspRawEvenCoefficient_eq_fullSource_complex_integral (k : ℕ) :
    ((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) =
      2 * ∫ x : ℝ in Ioi 0,
        ((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
          (2 * k).factorial := by
  rw [thetaCuspRawEvenMoment]
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [MeasureTheory.integral_mul_const]
  have hcast :
      (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (2 * k) * (thetaCuspFullSource x : ℂ)) =
        ((∫ x : ℝ in Ioi 0,
          x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) := by
    rw [show (fun x : ℝ => (x : ℂ) ^ (2 * k) *
        (thetaCuspFullSource x : ℂ)) =
        fun x : ℝ => ((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) by
      funext x
      push_cast
      rfl]
    exact integral_ofReal
  rw [hcast]
  ring

theorem integrableOn_pow_mul_thetaCuspFullSource_complex (k : ℕ) :
    IntegrableOn (fun x : ℝ =>
      ((x ^ k * thetaCuspFullSource x : ℝ) : ℂ)) (Ioi 0) := by
  have htwo := integrableOn_pow_mul_thetaCuspTailDerivative k 2
  have hzero := integrableOn_pow_mul_thetaCuspTailDerivative k 0
  have hreal : IntegrableOn (fun x : ℝ =>
      x ^ k * thetaCuspFullSource x) (Ioi 0) := by
    rw [show (fun x : ℝ => x ^ k * thetaCuspFullSource x) =
        fun x : ℝ => x ^ k * thetaCuspTailDerivative 2 x -
          (1 / 4 : ℝ) * (x ^ k * thetaCuspTailDerivative 0 x) by
      funext x
      rw [thetaCuspFullSource_eq_tail_second_sub]
      ring]
    exact htwo.sub (hzero.const_mul (1 / 4 : ℝ))
  exact hreal.ofReal

/-- Every odd-cutoff Xi Taylor section is exactly the finite cosine transform of the completed
theta source.  This is a finite identity, with no limiting or divisor input. -/
theorem xiCTaylorApprox_oddCutoff_eq_fullSource_truncatedCosine
    (d : ℕ) (z : ℂ) :
    xiCTaylorApprox (2 * d + 1) z =
      2 * ∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x : ℂ) * truncatedCosineSection d z x := by
  rw [xiCTaylorApprox_oddCutoff_eq_evenMagnitude_eval]
  rw [xiCTaylorEvenMagnitudePolynomial]
  unfold truncatedCosineSection
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) / (2 * k).factorial) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((-1 : ℂ) ^ k * z ^ (2 * k)) *
          ((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k).factorial) by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring]
  rw [MeasureTheory.integral_finset_sum]
  · rw [show eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
        (∑ k ∈ Finset.range (d + 1),
          C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k) =
        ∑ k ∈ Finset.range (d + 1),
          eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
            (C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k) by
      change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) (-z ^ 2))
          (∑ k ∈ Finset.range (d + 1),
            C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k) = _
      rw [map_sum]
      simp only [Polynomial.coe_eval₂RingHom]]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change ((thetaCuspRawEvenMoment k / (2 * k).factorial : ℝ) : ℂ) *
      (-z ^ 2) ^ k = _
    rw [thetaCuspRawEvenCoefficient_eq_fullSource_complex_integral]
    calc
      (2 * ∫ x : ℝ in Ioi 0,
          ((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k).factorial) * (-z ^ 2) ^ k =
          2 * ((∫ x : ℝ in Ioi 0,
            ((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
              (2 * k).factorial) * (-z ^ 2) ^ k) := by ring
      _ = 2 * ∫ x : ℝ in Ioi 0,
          (((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
            (2 * k).factorial) * (-z ^ 2) ^ k := by
        rw [MeasureTheory.integral_mul_const]
      _ = 2 * ∫ x : ℝ in Ioi 0,
          ((-1 : ℂ) ^ k * z ^ (2 * k)) *
            ((x ^ (2 * k) * thetaCuspFullSource x : ℝ) : ℂ) /
              (2 * k).factorial := by
        congr 2
        funext x
        push_cast
        rw [neg_pow, ← pow_mul]
        ring
  · intro k _
    have hcomp := integrableOn_pow_mul_thetaCuspFullSource_complex (2 * k)
    have hscaled := hcomp.const_mul (((-1 : ℂ) ^ k * z ^ (2 * k)))
    have hdiv := hscaled.mul_const (((2 * k).factorial : ℂ)⁻¹)
    simpa only [div_eq_mul_inv, mul_assoc] using hdiv

theorem integrableOn_thetaCuspFullSource_mul_truncatedCosineSection
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ) * truncatedCosineSection d z x) (Ioi 0) := by
  unfold truncatedCosineSection
  rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) / (2 * k).factorial) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (thetaCuspFullSource x : ℂ) *
          ((-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) /
            (2 * k).factorial) by
    funext x
    rw [Finset.mul_sum]]
  exact MeasureTheory.integrable_finset_sum _ fun k _ => by
    have hbase := integrableOn_pow_mul_thetaCuspFullSource_complex (2 * k)
    have hscaled := hbase.const_mul
      (((-1 : ℂ) ^ k * z ^ (2 * k)) /
        (((2 * k).factorial : ℕ) : ℂ))
    convert hscaled using 1
    funext x
    push_cast
    rw [mul_pow]
    ring

/-- The cosine transform of the canonical density splits into one raw-tail section plus twice the
actual Xi Taylor section.  Hence the completed-source part of `rho` cannot be treated as an
independent positive error term: it feeds the target section back into the identity. -/
theorem integral_thetaCuspTailSecondDensity_mul_truncatedCosine_eq_tail_add_taylor
    (d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensity x : ℂ) * truncatedCosineSection d z x) =
      (∫ x : ℝ in Ioi 0,
        (thetaCuspTailDerivative 0 x : ℂ) * truncatedCosineSection d z x) +
        2 * xiCTaylorApprox (2 * d + 1) z := by
  have htail :=
    integrableOn_thetaCuspTailDerivative_mul_truncatedCosineSection d z
  have hfull :=
    integrableOn_thetaCuspFullSource_mul_truncatedCosineSection d z
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * truncatedCosineSection d z x) =
      fun x : ℝ =>
        (thetaCuspTailDerivative 0 x : ℂ) * truncatedCosineSection d z x +
          4 * ((thetaCuspFullSource x : ℂ) *
            truncatedCosineSection d z x) by
    funext x
    rw [thetaCuspTailSecondDensity_eq_tail_add_four_fullSource]
    push_cast
    ring]
  rw [integral_add htail (hfull.const_mul 4), integral_const_mul]
  have hP := xiCTaylorApprox_oddCutoff_eq_fullSource_truncatedCosine d z
  rw [show (4 : ℂ) *
      (∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x : ℂ) * truncatedCosineSection d z x) =
      2 * xiCTaylorApprox (2 * d + 1) z by rw [hP]; ring]

/-- The completed-source contribution to the shifted core is not an independent positive
component.  After the exact completion multiplier it is the actual next Xi Taylor section, up to
the fixed central seam. -/
theorem sq_mul_two_fullSource_coreAtom_integral_eq_completion_mul_taylor_sub_seam
    (d : ℕ) (z : ℂ) :
    z ^ 2 *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondCoreAtom d z x) =
      (z ^ 2 + 1 / 4) * xiCTaylorApprox (2 * (d + 1) + 1) z -
        (1 / 4) * xiCTaylorApprox 1 0 := by
  have hfull : IntegrableOn (fun x : ℝ =>
      (thetaCuspFullSource x : ℂ)) (Ioi 0) := by
    simpa using integrableOn_pow_mul_thetaCuspFullSource_complex 0
  have hcos :=
    integrableOn_thetaCuspFullSource_mul_truncatedCosineSection (d + 1) z
  have hP :=
    xiCTaylorApprox_oddCutoff_eq_fullSource_truncatedCosine (d + 1) z
  have hP0 : xiCTaylorApprox 1 0 =
      2 * ∫ x : ℝ in Ioi 0, (thetaCuspFullSource x : ℂ) := by
    have h := xiCTaylorApprox_oddCutoff_eq_fullSource_truncatedCosine 0 0
    simpa [truncatedCosineSection] using h
  calc
    z ^ 2 *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ) * thetaCuspTailSecondCoreAtom d z x) =
      2 * ∫ x : ℝ in Ioi 0,
        z ^ 2 * ((thetaCuspFullSource x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) := by
            rw [MeasureTheory.integral_const_mul]
            ring
    _ = 2 * ∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x : ℂ) *
          ((z ^ 2 + 1 / 4) * truncatedCosineSection (d + 1) z x - 1 / 4) := by
            congr 2
            funext x
            rw [← sq_mul_thetaCuspTailSecondCoreAtom_eq_completion_mul_cosine_sub]
            ring
    _ = 2 * ((z ^ 2 + 1 / 4) *
          (∫ x : ℝ in Ioi 0,
            (thetaCuspFullSource x : ℂ) *
              truncatedCosineSection (d + 1) z x) -
        (1 / 4) * ∫ x : ℝ in Ioi 0,
          (thetaCuspFullSource x : ℂ)) := by
            rw [show (fun x : ℝ => (thetaCuspFullSource x : ℂ) *
                ((z ^ 2 + 1 / 4) * truncatedCosineSection (d + 1) z x - 1 / 4)) =
              fun x : ℝ => (z ^ 2 + 1 / 4) *
                  ((thetaCuspFullSource x : ℂ) *
                    truncatedCosineSection (d + 1) z x) -
                (1 / 4) * (thetaCuspFullSource x : ℂ) by
              funext x
              ring]
            rw [integral_sub (hcos.const_mul (z ^ 2 + 1 / 4))
              (hfull.const_mul (1 / 4)), integral_const_mul, integral_const_mul]
    _ = (z ^ 2 + 1 / 4) * xiCTaylorApprox (2 * (d + 1) + 1) z -
        (1 / 4) * xiCTaylorApprox 1 0 := by
          rw [hP, hP0]
          ring

/-- Every coefficient in the raw theta-tail section is strictly positive. -/
theorem thetaCuspTailEvenCoefficient_pos (n : ℕ) :
    0 < thetaCuspTailEvenCoefficient n := by
  rw [thetaCuspTailEvenCoefficient_eq_second_integral]
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x /
      (2 * n + 2).factorial
  have hfcont : Continuous f := by
    dsimp [f]
    exact ((continuous_id.pow _).mul
      (differentiable_thetaCuspTailDerivative 2).continuous).div_const _
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_pow_mul_thetaCuspTailDerivative (2 * n + 2) 2
    simpa [f, div_eq_mul_inv] using h.mul_const
      (((2 * n + 2).factorial : ℝ)⁻¹)
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f]
    exact div_nonneg
      (mul_nonneg (pow_nonneg hx.le _) (thetaCuspTailDerivative_two_pos hx.le).le)
      (Nat.cast_nonneg _)
  have hpos : 0 < ∫ x : ℝ in Ioi 0, f x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
    have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
      hfcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change f 1 ≠ 0
    dsimp [f]
    positivity [thetaCuspTailDerivative_two_pos (x := 1) (by norm_num)]
  change 0 < 2 * ∫ x : ℝ in Ioi 0, f x
  positivity

/-- The raw tail section is strictly positive at the completion value `w=1/4`. -/
theorem thetaCuspTailEvenPolynomial_eval_quarter_pos (d : ℕ) :
    0 < (thetaCuspTailEvenPolynomial d).eval (1 / 4) := by
  rw [thetaCuspTailEvenPolynomial]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_pos
  · intro k _hk
    exact mul_pos (thetaCuspTailEvenCoefficient_pos k) (by positivity)
  · exact ⟨0, by simp⟩

/-- Every finite theta-tail core is pinned to the central seam value at the upper completion
boundary. -/
theorem xiCTaylorThetaTailCorePolynomial_eval_half_mul_I (d : ℕ) :
    (xiCTaylorThetaTailCorePolynomial d).eval ((1 / 2 : ℂ) * I) = 1 / 2 := by
  rw [xiCTaylorThetaTailCorePolynomial, evenMagnitudeLift_eval]
  simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_sub, eval₂_X]
  rw [show -(((1 / 2 : ℂ) * I) ^ 2) = (1 / 4 : ℂ) by
    rw [mul_pow, I_sq]
    ring]
  push_cast
  ring

/-- At the upper completion boundary, the derivative is exactly the negative imaginary raw-tail
section. -/
theorem xiCTaylorThetaTailCorePolynomial_derivative_eval_half_mul_I (d : ℕ) :
    (xiCTaylorThetaTailCorePolynomial d).derivative.eval ((1 / 2 : ℂ) * I) =
      -I * (evenMagnitudeLift (thetaCuspTailEvenPolynomial d)).eval
        ((1 / 2 : ℂ) * I) := by
  rw [xiCTaylorThetaTailCorePolynomial_derivative_eval]
  rw [show (((1 / 2 : ℂ) * I) ^ 2 + 1 / 4) = 0 by
    rw [mul_pow, I_sq]
    ring]
  ring

/-- Exact upper-boundary current: the seam turns the positive raw-tail value into a negative
oriented current. -/
theorem xiCTaylorThetaTailCorePolynomial_current_half_mul_I (d : ℕ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d)
        ((1 / 2 : ℂ) * I) =
      -(1 / 2) * (thetaCuspTailEvenPolynomial d).eval (1 / 4) := by
  rw [orientedPolynomialCurrent,
    xiCTaylorThetaTailCorePolynomial_derivative_eval_half_mul_I,
    xiCTaylorThetaTailCorePolynomial_eval_half_mul_I,
    evenMagnitudeLift_eval]
  rw [show -(((1 / 2 : ℂ) * I) ^ 2) = (1 / 4 : ℂ) by
    rw [mul_pow, I_sq]
    ring]
  rw [show (1 / 4 : ℂ) = algebraMap ℝ ℂ (1 / 4 : ℝ) by norm_num]
  rw [Polynomial.eval₂_at_apply]
  simp
  ring

/-- The exact theta-tail/seam cancellation is strictly favorable on the upper completion
boundary for every finite degree. -/
theorem xiCTaylorThetaTailCorePolynomial_current_half_mul_I_neg (d : ℕ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d)
        ((1 / 2 : ℂ) * I) < 0 := by
  rw [xiCTaylorThetaTailCorePolynomial_current_half_mul_I]
  nlinarith [thetaCuspTailEvenPolynomial_eval_quarter_pos d]

end
end RHTower
