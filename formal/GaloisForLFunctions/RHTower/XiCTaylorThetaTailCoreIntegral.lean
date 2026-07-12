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
  · simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [thetaCuspTailEvenCoefficient_eq_complex_integral]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_mul_const]
    rw [neg_pow, pow_two, ← pow_mul]
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
