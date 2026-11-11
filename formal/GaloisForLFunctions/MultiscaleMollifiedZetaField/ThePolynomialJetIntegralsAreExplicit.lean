import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectedPolynomialJetsConverge

/-!
# Explicit integrands for polynomial arithmetic jets

Multiplication of a profile by `1−x` sends its differential profile `A`
to `tA−P` at `x=1−t`. The directional recurrence therefore gives the
first two jet integrands by polynomial algebra, before any evaluation.
-/

open MeasureTheory Polynomial

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The differential profile in the harmonic coordinate. -/
def polynomialDifferentialProfile (P : ℝ[X]) (v t : ℝ) : ℝ :=
  P.derivative.eval (1 - t) - v * P.eval (1 - t)

private theorem continuous_differentialProfile (P : ℝ[X]) (v : ℝ) :
    Continuous (polynomialDifferentialProfile P v) := by
  unfold polynomialDifferentialProfile
  fun_prop

private theorem complement_at_one_sub (P : ℝ[X]) (t : ℝ) :
    (complementPolynomial P).eval (1 - t) = t * P.eval (1 - t) := by
  simp only [complementPolynomial, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X]
  ring

/-- The complement operation acts affinely on differential profiles. -/
theorem polynomialDifferentialProfile_complement (P : ℝ[X]) (v t : ℝ) :
    polynomialDifferentialProfile (complementPolynomial P) v t =
      t * polynomialDifferentialProfile P v t - P.eval (1 - t) := by
  simp only [polynomialDifferentialProfile, complementPolynomial,
    Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_X]
  ring

private theorem integral_three_terms {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (a b c : ℝ) :
    a * (∫ t in (0 : ℝ)..1, f t) + b * (∫ t in (0 : ℝ)..1, g t) +
      c * (∫ t in (0 : ℝ)..1, h t) =
      ∫ t in (0 : ℝ)..1, a * f t + b * g t + c * h t := by
  rw [intervalIntegral.integral_add (f := fun t => a * f t + b * g t) (g := fun t => c * h t)
    (((hf.const_mul a).add (hg.const_mul b)).intervalIntegrable 0 1)
    ((hh.const_mul c).intervalIntegrable 0 1),
    intervalIntegral.integral_add (f := fun t => a * f t) (g := fun t => b * g t)
      ((hf.const_mul a).intervalIntegrable 0 1)
      ((hg.const_mul b).intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_const_mul]

/-- The first jet inserts the harmonic coordinate and differentiates the two profiles. -/
theorem polynomialProfileFirstLimit_eq_integral (P Q : ℝ[X]) (v κ ν : ℝ) (k : ℕ) :
    polynomialProfileFirstLimit P Q v κ ν k =
      ∫ t : ℝ in 0..1, t ^ k *
        ((κ + 2 * ν) * t * polynomialDifferentialProfile P v t * polynomialDifferentialProfile Q v t -
          ν * (P.eval (1 - t) * polynomialDifferentialProfile Q v t +
            polynomialDifferentialProfile P v t * Q.eval (1 - t))) := by
  unfold polynomialProfileFirstLimit polynomialProfilePairIntegral
  change κ * (∫ t : ℝ in 0..1, t ^ (k + 1) *
      (polynomialDifferentialProfile P v t * polynomialDifferentialProfile Q v t)) +
    ν * (∫ t : ℝ in 0..1, t ^ k *
      (polynomialDifferentialProfile (complementPolynomial P) v t * polynomialDifferentialProfile Q v t)) +
    ν * (∫ t : ℝ in 0..1, t ^ k *
      (polynomialDifferentialProfile P v t * polynomialDifferentialProfile (complementPolynomial Q) v t)) = _
  have hc (A B : ℝ[X]) (j : ℕ) : Continuous (fun t : ℝ => t ^ j *
      (polynomialDifferentialProfile A v t * polynomialDifferentialProfile B v t)) :=
    (continuous_id.pow j).mul ((continuous_differentialProfile A v).mul
      (continuous_differentialProfile B v))
  rw [integral_three_terms (hc P Q (k + 1)) (hc (complementPolynomial P) Q k)
    (hc P (complementPolynomial Q) k)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [polynomialDifferentialProfile_complement, pow_succ]
  ring

/-- The second jet includes both profile derivatives and their mixed term. -/
theorem polynomialProfileSecondLimit_eq_integral (P Q : ℝ[X]) (v κ ν : ℝ) (k : ℕ) :
    polynomialProfileSecondLimit P Q v κ ν k =
      ∫ t : ℝ in 0..1, t ^ k *
        ((κ + 2 * ν) ^ 2 * t ^ 2 * polynomialDifferentialProfile P v t * polynomialDifferentialProfile Q v t -
          2 * ν * (κ + 2 * ν) * t *
            (P.eval (1 - t) * polynomialDifferentialProfile Q v t +
              polynomialDifferentialProfile P v t * Q.eval (1 - t)) +
          2 * ν ^ 2 * P.eval (1 - t) * Q.eval (1 - t)) := by
  unfold polynomialProfileSecondLimit
  rw [polynomialProfileFirstLimit_eq_integral, polynomialProfileFirstLimit_eq_integral,
    polynomialProfileFirstLimit_eq_integral]
  have hc (A B : ℝ[X]) (j : ℕ) : Continuous (fun t : ℝ => t ^ j *
      ((κ + 2 * ν) * t * polynomialDifferentialProfile A v t * polynomialDifferentialProfile B v t -
        ν * (A.eval (1 - t) * polynomialDifferentialProfile B v t +
          polynomialDifferentialProfile A v t * B.eval (1 - t)))) := by
    unfold polynomialDifferentialProfile
    fun_prop
  rw [integral_three_terms (hc P Q (k + 1)) (hc (complementPolynomial P) Q k)
    (hc P (complementPolynomial Q) k)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [polynomialDifferentialProfile_complement, complement_at_one_sub, pow_succ]
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
