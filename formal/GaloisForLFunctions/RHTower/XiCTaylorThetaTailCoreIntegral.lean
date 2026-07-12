import GaloisForLFunctions.RHTower.XiCTaylorThetaTailRapidDecay

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

def truncatedCosineSection (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    ((-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k)) / (2 * k).factorial

theorem thetaCuspTailEvenCoefficient_eq_complex_integral (k : ℕ) :
    (thetaCuspTailEvenCoefficient k : ℂ) =
      2 * ∫ x : ℝ in Ioi 0,
        ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
          (2 * k).factorial := by
  rw [thetaCuspTailEvenCoefficient, thetaCuspTailRawEvenMoment]
  push_cast
  simp_rw [div_eq_mul_inv]
  rw [MeasureTheory.integral_mul_const]
  have hcast :
      (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (2 * k) *
        (thetaCuspTailDerivative 0 x : ℂ)) =
        ((∫ x : ℝ in Ioi 0,
          x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) := by
    rw [show (fun x : ℝ => (x : ℂ) ^ (2 * k) *
        (thetaCuspTailDerivative 0 x : ℂ)) =
        fun x : ℝ => ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) by
          funext x
          push_cast
          rfl]
    exact integral_ofReal
  rw [hcast]
  ring

theorem thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_integral
    (d : ℕ) (z : ℂ) :
    (thetaCuspTailEvenPolynomial d).eval₂ (algebraMap ℝ ℂ) (-z ^ 2) =
      2 * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailDerivative 0 x : ℂ) * truncatedCosineSection d z x := by
  rw [thetaCuspTailEvenPolynomial]
  unfold truncatedCosineSection
  rw [show (fun x : ℝ => (thetaCuspTailDerivative 0 x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k) / (2 * k).factorial) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (((-1 : ℂ) ^ k * z ^ (2 * k)) *
          ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
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
          C (thetaCuspTailEvenCoefficient k) * X ^ k) =
        ∑ k ∈ Finset.range (d + 1),
          eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
            (C (thetaCuspTailEvenCoefficient k) * X ^ k) by
      change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) (-z ^ 2))
          (∑ k ∈ Finset.range (d + 1),
            C (thetaCuspTailEvenCoefficient k) * X ^ k) = _
      rw [map_sum]
      simp only [Polynomial.coe_eval₂RingHom]]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (thetaCuspTailEvenCoefficient k : ℂ) * (-z ^ 2) ^ k = _
    rw [thetaCuspTailEvenCoefficient_eq_complex_integral]
    calc
      (2 * ∫ x : ℝ in Ioi 0,
          ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
            (2 * k).factorial) * (-z ^ 2) ^ k =
          2 * ((∫ x : ℝ in Ioi 0,
            ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
              (2 * k).factorial) * (-z ^ 2) ^ k) := by ring
      _ = 2 * ∫ x : ℝ in Ioi 0,
          (((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
            (2 * k).factorial) * (-z ^ 2) ^ k := by
        rw [MeasureTheory.integral_mul_const]
      _ = 2 * ∫ x : ℝ in Ioi 0,
          ((-1 : ℂ) ^ k * z ^ (2 * k)) *
            ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
              (2 * k).factorial := by
        congr 2
        funext x
        push_cast
        rw [neg_pow, ← pow_mul]
        ring
  · intro k _
    have hcomp : IntegrableOn
        (fun x : ℝ => ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ))
        (Ioi 0) :=
      (integrableOn_pow_mul_thetaCuspTailDerivative (2 * k) 0).ofReal
    have hscaled := hcomp.const_mul (((-1 : ℂ) ^ k * z ^ (2 * k)))
    have hdiv := hscaled.mul_const (((2 * k).factorial : ℂ)⁻¹)
    simpa only [div_eq_mul_inv, mul_assoc] using hdiv

theorem xiCTaylorThetaTailCorePolynomial_eval_eq_integral
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).eval z =
      1 / 2 - (z ^ 2 + 1 / 4) *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspTailDerivative 0 x : ℂ) * truncatedCosineSection d z x) := by
  rw [xiCTaylorThetaTailCorePolynomial, evenMagnitudeLift_eval]
  simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_sub, eval₂_X]
  rw [thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_integral]
  push_cast
  ring

end
end RHTower
