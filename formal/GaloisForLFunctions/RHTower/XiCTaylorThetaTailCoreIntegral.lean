import GaloisForLFunctions.RHTower.XiCTaylorThetaTailRapidDecay

/-!
# Integral form of the truncated theta-tail core polynomial

Let `Θ(x) = Σ_(n ≥ 1) e^(x/2) exp(-π n^2 e^(2x))` be the logarithmic Gaussian theta tail and
`c_k = 2 ∫_0^∞ x^(2k) Θ(x) dx / (2k)!` its normalized even moments. With the truncated cosine
section `C_d(z x) = Σ_(k ≤ d) (-1)^k (z x)^(2k) / (2k)!`, this module rewrites the tail-moment
polynomial `P_d(w) = Σ_(k ≤ d) c_k w^k` at `w = -z^2` as `2 ∫_0^∞ Θ(x) C_d(z x) dx`, and hence the
finite theta-tail core polynomial as `1/2 - (z^2 + 1/4) · 2 ∫_0^∞ Θ(x) C_d(z x) dx`.

## Main results

- `thetaCuspTailEvenCoefficient_eq_complex_integral`: `c_k = 2 ∫_0^∞ x^(2k) Θ(x) / (2k)! dx`.
- `thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_integral`: `P_d(-z^2) = 2 ∫_0^∞ Θ(x) C_d(z x) dx`.
- `xiCTaylorThetaTailCorePolynomial_eval_eq_integral`: the core polynomial at `z` equals
  `1/2 - (z^2 + 1/4) · 2 ∫_0^∞ Θ(x) C_d(z x) dx`.

## Hypotheses

Unconditional; the moment integrals converge by the rapid decay of `Θ`.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- The degree-`2d` Taylor section `Σ_(k ≤ d) (-1)^k (z x)^(2k) / (2k)!` of `cos(z x)`. -/
def truncatedCosineSection (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    ((-1 : ℂ) ^ k * (z * (x : ℂ)) ^ (2 * k)) / (2 * k).factorial

/-- The normalized even moment is `c_k = 2 ∫_0^∞ x^(2k) Θ(x) / (2k)! dx`, as a complex integral. -/
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

/-- The tail-moment polynomial at `w = -z^2` equals `2 ∫_0^∞ Θ(x) C_d(z x) dx`, with `C_d` the
truncated cosine section. -/
theorem thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_integral
    (d : ℕ) (z : ℂ) :
    (thetaCuspTailEvenPolynomial d).eval₂ (algebraMap ℝ ℂ) (-z ^ (2 : ℕ)) =
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
  rw [MeasureTheory.integral_finsetSum]
  · rw [show eval₂ (algebraMap ℝ ℂ) (-z ^ (2 : ℕ))
        (∑ k ∈ Finset.range (d + 1),
          C (thetaCuspTailEvenCoefficient k) * X ^ k) =
        ∑ k ∈ Finset.range (d + 1),
          eval₂ (algebraMap ℝ ℂ) (-z ^ (2 : ℕ))
            (C (thetaCuspTailEvenCoefficient k) * X ^ k) by
      change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) (-z ^ (2 : ℕ)))
          (∑ k ∈ Finset.range (d + 1),
            C (thetaCuspTailEvenCoefficient k) * X ^ k) = _
      rw [map_sum]
      simp only [Polynomial.coe_eval₂RingHom]]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (thetaCuspTailEvenCoefficient k : ℂ) * (-z ^ (2 : ℕ)) ^ k = _
    rw [thetaCuspTailEvenCoefficient_eq_complex_integral]
    calc
      (2 * ∫ x : ℝ in Ioi 0,
          ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
            (2 * k).factorial) * (-z ^ (2 : ℕ)) ^ k =
          2 * ((∫ x : ℝ in Ioi 0,
            ((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
              (2 * k).factorial) * (-z ^ (2 : ℕ)) ^ k) := by ring
      _ = 2 * ∫ x : ℝ in Ioi 0,
          (((x ^ (2 * k) * thetaCuspTailDerivative 0 x : ℝ) : ℂ) /
            (2 * k).factorial) * (-z ^ (2 : ℕ)) ^ k := by
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

/-- The truncated theta-tail core polynomial at `z` equals
`1/2 - (z^2 + 1/4) · 2 ∫_0^∞ Θ(x) C_d(z x) dx`. -/
theorem xiCTaylorThetaTailCorePolynomial_eval_eq_integral
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).eval z =
      1 / 2 - (z ^ (2 : ℕ) + 1 / 4) *
        (2 * ∫ x : ℝ in Ioi 0,
          (thetaCuspTailDerivative 0 x : ℂ) * truncatedCosineSection d z x) := by
  rw [xiCTaylorThetaTailCorePolynomial, evenMagnitudeLift_eval]
  simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_sub, eval₂_X]
  rw [thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_integral]
  push_cast
  ring

end
end RHTower
