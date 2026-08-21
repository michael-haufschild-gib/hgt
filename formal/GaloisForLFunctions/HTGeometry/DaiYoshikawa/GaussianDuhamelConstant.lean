import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Gaussian constant of the Duhamel estimate

Lemma 2.8 and Proposition 2.10 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small
eigenvalues of the Laplacian* (arXiv:2509.06151v2), bound the Duhamel correction `H_k` by an
explicit convolution.  After the Gaussian factors of the parametrix and of the heat kernel are
multiplied, the exponent is

```text
−(‖ξ‖²/8)(1/τ + 1/(t−τ))  =  −t‖ξ‖² / (8 τ (t−τ)) ,
```

so the spatial integral over `ℝ^{2n}` equals `(8π τ(t−τ)/t)^n`.  That cancels the prefactor
`(τ(t−τ)/t)^{−n}` exactly, leaving a factor `(8π)^n` independent of the intermediate time `τ`, and
the remaining time integral `∫_0^t τ^k dτ = t^{k+1}/(k+1)` produces the power `t^{k+1−n}` quoted in
the paper.

The two computations are proved here; the `d`-dimensional Gaussian integral is obtained from the
one-dimensional one by Fubini over the product measure.
-/

open MeasureTheory Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **The `d`-dimensional Gaussian integral.**  `∫_{ℝ^d} e^{−a‖ξ‖²} dξ = (π/a)^{d/2}`. -/
theorem integral_gaussian_pi (d : ℕ) (a : ℝ) :
    (∫ ξ : Fin d → ℝ, Real.exp (-(a * ∑ i, (ξ i) ^ 2))) = Real.sqrt (π / a) ^ d := by
  have hprod : ∀ ξ : Fin d → ℝ,
      Real.exp (-(a * ∑ i, (ξ i) ^ 2)) = ∏ i, Real.exp (-a * (ξ i) ^ 2) := by
    intro ξ
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hprod]
  rw [MeasureTheory.volume_pi,
    integral_fintype_prod_eq_prod (f := fun _ : Fin d => fun x : ℝ => Real.exp (-a * x ^ 2))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [integral_gaussian]

/-- **The Duhamel Gaussian factor is independent of the intermediate time.**

For `0 < τ < t` the spatial Gaussian integral cancels the prefactor `(τ(t−τ)/t)^{−n}` exactly,
leaving `(8π)^n`. -/
theorem integral_duhamelGaussian_mul_inv (n : ℕ) {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ)
    (hτt : τ < t) :
    ((τ * (t - τ) / t) ^ n)⁻¹
        * ∫ ξ : Fin (2 * n) → ℝ,
            Real.exp (-((t / (8 * (τ * (t - τ)))) * ∑ i, (ξ i) ^ 2))
      = (8 * π) ^ n := by
  have hd : 0 < t - τ := by linarith
  have hden : 0 < τ * (t - τ) := mul_pos hτ hd
  have hq : 0 < τ * (t - τ) / t := div_pos hden ht
  have hgauss := integral_gaussian_pi (2 * n) (t / (8 * (τ * (t - τ))))
  rw [hgauss]
  have hratio : π / (t / (8 * (τ * (t - τ)))) = 8 * π * (τ * (t - τ) / t) := by
    field_simp
  rw [hratio]
  have hsq2 : Real.sqrt (8 * π * (τ * (t - τ) / t)) ^ (2 * n)
      = (8 * π * (τ * (t - τ) / t)) ^ n := by
    rw [pow_mul, Real.sq_sqrt (by positivity)]
  rw [hsq2, mul_pow]
  field_simp

/-- **The Duhamel time integral.**  `∫_0^t τ^k · C dτ = C t^{k+1}/(k+1)`. -/
theorem integral_duhamelTime (k : ℕ) (C t : ℝ) :
    (∫ τ in (0 : ℝ)..t, τ ^ k * C) = C * t ^ (k + 1) / (k + 1) := by
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp
  ring

/-- **The constant of Proposition 2.10.**

The full Duhamel convolution, with the prefactor `τ^k t^{−n} (τ(t−τ)/t)^{−n}` and the spatial
Gaussian, evaluates to `(8π)^n t^{k+1}/((k+1) t^n)` — the power `t^{k+1−n}` of the paper. -/
theorem integral_duhamelProfile (n k : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ τ in (0 : ℝ)..t, τ ^ k * ((8 * π) ^ n / t ^ n))
      = (8 * π) ^ n * t ^ (k + 1) / ((k + 1) * t ^ n) := by
  rw [integral_duhamelTime k ((8 * π) ^ n / t ^ n) t]
  field_simp

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
