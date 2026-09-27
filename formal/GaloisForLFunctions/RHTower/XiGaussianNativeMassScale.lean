import GaloisForLFunctions.RHTower.PolynomialGaussianFourierAperture

/-!
# Exact native mass and Gaussian energy normalization

Positive heat time and positive Gaussian scale are interchangeable. Polynomial
rescaling is invertible and preserves degree; the native mass is exactly the
whole Gaussian polynomial norm squared divided by scale.
-/

open scoped Real SchwartzMap
open MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Positive heat time associated with the spatial Gaussian scale. -/
def xiGaussianScaleHeat (r : {r : ℝ // 0 < r}) : {t : ℝ // 0 < t} :=
  ⟨2 * π * (r : ℝ) ^ 2, mul_pos (mul_pos (by positivity) Real.pi_pos) (pow_pos r.property _)⟩

/-- Every positive heat time has its canonical positive Gaussian scale. -/
def xiGaussianHeatScale (t : {t : ℝ // 0 < t}) : {r : ℝ // 0 < r} :=
  ⟨Real.sqrt ((t : ℝ) / (2 * π)), Real.sqrt_pos.2 (div_pos t.property (by positivity))⟩

@[simp] theorem xiGaussianScaleHeat_heatScale (t : {t : ℝ // 0 < t}) :
    xiGaussianScaleHeat (xiGaussianHeatScale t) = t := by
  apply Subtype.ext
  change 2 * π * Real.sqrt ((t : ℝ) / (2 * π)) ^ 2 = (t : ℝ)
  rw [Real.sq_sqrt (div_nonneg t.property.le (by positivity))]
  field_simp

/-- Inverse rescaling acts on the entire polynomial, including every cross term. -/
def xiGaussianUnscalePolynomial (Q : Polynomial ℝ) (r : {r : ℝ // 0 < r}) : Polynomial ℝ :=
  Q.comp (Polynomial.C (((r : ℝ) ^ 2)⁻¹) * Polynomial.X)

@[simp] theorem xiGaussianUnscalePolynomial_comp_scale (Q : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    (xiGaussianUnscalePolynomial Q r).comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X) = Q := by
  rw [xiGaussianUnscalePolynomial, Polynomial.comp_assoc]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
    ← Polynomial.C_mul, inv_mul_cancel₀ (pow_ne_zero 2 r.property.ne'),
    Polynomial.C_1, one_mul, Polynomial.comp_X]

@[simp] theorem natDegree_xiGaussianUnscalePolynomial (Q : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    (xiGaussianUnscalePolynomial Q r).natDegree = Q.natDegree := by
  rw [xiGaussianUnscalePolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_C_mul_X _ (inv_ne_zero (pow_ne_zero 2 r.property.ne')), mul_one]

/-- The native density is literally the scaled full polynomial energy. -/
theorem routeUPolynomialGaussianDensity_scale (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (x : ℝ) :
    routeUPolynomialGaussianDensity (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
        (xiGaussianScaleHeat r) x =
      polynomialGaussianEnergy (evenSquarePolynomial P) ((r : ℝ) * x) := by
  unfold routeUPolynomialGaussianDensity polynomialGaussianEnergy evenSquarePolynomial
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, xiGaussianScaleHeat, mul_pow]
  congr 3
  ring

/-- Exact Jacobian bridge from native mass to the whole Gaussian norm. -/
theorem routeUPolynomialGaussianMass_scale (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    routeUPolynomialGaussianMass (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
        (xiGaussianScaleHeat r) =
      (r : ℝ)⁻¹ * ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2
        (volume : Measure ℝ)‖ ^ 2 := by
  unfold routeUPolynomialGaussianMass
  simp_rw [routeUPolynomialGaussianDensity_scale]
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun x : ℝ => ‖polynomialGaussianEnergy (evenSquarePolynomial P) x‖),
    abs_of_pos (inv_pos.mpr r.property), smul_eq_mul, integral_norm_polynomialGaussianEnergy]

/-- Every native polynomial and every positive heat time has this exact norm normalization. -/
theorem xiGaussianUnscalePolynomial_norm_sq (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    ‖(polyGaussSchwartz (evenSquarePolynomial
        (xiGaussianUnscalePolynomial Q (xiGaussianHeatScale t)))).toLp 2
          (volume : Measure ℝ)‖ ^ 2 =
      (xiGaussianHeatScale t : ℝ) * routeUPolynomialGaussianMass Q t := by
  have h := routeUPolynomialGaussianMass_scale
    (xiGaussianUnscalePolynomial Q (xiGaussianHeatScale t)) (xiGaussianHeatScale t)
  rw [xiGaussianUnscalePolynomial_comp_scale, xiGaussianScaleHeat_heatScale] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (xiGaussianHeatScale t).property.ne', one_mul]

end RHTower
