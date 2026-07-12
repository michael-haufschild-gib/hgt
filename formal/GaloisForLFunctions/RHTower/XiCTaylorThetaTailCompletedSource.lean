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

end
end RHTower
