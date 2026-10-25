import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity

/-!
# The exact inverse series of the golden datum

The golden numerator factors through its two reciprocal Frobenius roots. Damping rescales
those roots and the two polar factors. Its inverse coefficients are an exact difference
of geometric towers, with the ordinary unit coefficient restored at degree zero.
-/

noncomputable section
open PowerSeries
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Damping multiplies each norm-five power-series variable by `t`. -/
def goldenZetaSeriesAt (t : ℂ) : ℂ⟦X⟧ :=
  geom t * geom (5 * t) *
    ((1 - C (goldenDatum.alpha 0 * t) * X) * (1 - C (goldenDatum.alpha 1 * t) * X))

/-- The inverse golden series, expressed entirely in geometric factors. -/
def goldenInverseSeriesAt (t : ℂ) : ℂ⟦X⟧ :=
  ((1 - C t * X) * (1 - C (5 * t) * X)) *
    (geom (goldenDatum.alpha 0 * t) * geom (goldenDatum.alpha 1 * t))

theorem goldenZetaSeriesAt_one : goldenZetaSeriesAt 1 = goldenDatum.zetaSeries := by
  simp only [goldenZetaSeriesAt, mul_one, CurveDatum.zetaSeries, CurveDatum.poleZeta,
    CurveDatum.hOnePoly, Fin.prod_univ_two]
  rfl

/-- The displayed series is the actual multiplicative inverse at every damping parameter. -/
theorem goldenInverseSeriesAt_mul (t : ℂ) :
    goldenInverseSeriesAt t * goldenZetaSeriesAt t = 1 := by
  unfold goldenInverseSeriesAt goldenZetaSeriesAt
  calc
    _ = ((1 - C t * X) * geom t) * ((1 - C (5 * t) * X) * geom (5 * t)) *
      ((1 - C (goldenDatum.alpha 0 * t) * X) * geom (goldenDatum.alpha 0 * t)) *
      ((1 - C (goldenDatum.alpha 1 * t) * X) * geom (goldenDatum.alpha 1 * t)) := by ring
    _ = 1 := by rw [one_sub_mul_geom, one_sub_mul_geom, one_sub_mul_geom, one_sub_mul_geom]; ring

/-- The two golden Frobenius roots differ by the positive square root of five. -/
theorem golden_alpha_sub : goldenDatum.alpha 0 - goldenDatum.alpha 1 = (Real.sqrt 5 : ℂ) := by
  show (Real.sqrt 5 : ℂ) * (Real.goldenRatio : ℂ) -
      (Real.sqrt 5 : ℂ) * ((Real.goldenRatio⁻¹ : ℝ) : ℂ) = (Real.sqrt 5 : ℂ)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  rw [← mul_sub, Real.inv_goldenRatio, sub_neg_eq_add, Real.goldenRatio_add_goldenConj,
    mul_one]

private theorem golden_damped_factor_identity (t : ℂ) :
    (1 - C (goldenDatum.alpha 0 * t) * X) * (1 - C (goldenDatum.alpha 1 * t) * X) =
      (1 - C t * X) * (1 - C (5 * t) * X) + C t * X := by
  calc
    _ = 1 - C ((goldenDatum.alpha 0 + goldenDatum.alpha 1) * t) * X +
        C ((goldenDatum.alpha 0 * goldenDatum.alpha 1) * t ^ 2) * X ^ 2 := by
      simp only [map_add, map_mul, map_pow]
      ring
    _ = 1 - C (5 * t) * X + C (5 * t ^ 2) * X ^ 2 := by
      rw [goldenDatum_alpha_sum, goldenDatum_alpha_mul]
    _ = _ := by
      simp only [map_mul, map_pow]
      ring

/-- An exact partial-fraction identity, including the constant coefficient. -/
theorem goldenInverseSeriesAt_tower_difference (t : ℂ) :
    geom (goldenDatum.alpha 0 * t) - geom (goldenDatum.alpha 1 * t) =
      C (Real.sqrt 5 : ℂ) * (1 - goldenInverseSeriesAt t) := by
  let a := goldenDatum.alpha 0 * t
  let b := goldenDatum.alpha 1 * t
  have ha := one_sub_mul_geom a
  have hb := one_sub_mul_geom b
  have hdiff : geom a - geom b = C (a - b) * X * (geom a * geom b) := by
    rw [map_sub]
    linear_combination (geom b) * ha - (geom a) * hb
  have hab : a - b = (Real.sqrt 5 : ℂ) * t := by
    dsimp [a, b]
    rw [← sub_mul, golden_alpha_sub]
  have hp : ((1 - C a * X) * (1 - C b * X)) * (geom a * geom b) = 1 := by
    calc
      _ = ((1 - C a * X) * geom a) * ((1 - C b * X) * geom b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  have hf : (1 - C a * X) * (1 - C b * X) =
      (1 - C t * X) * (1 - C (5 * t) * X) + C t * X := golden_damped_factor_identity t
  rw [hf] at hp
  have hmu : 1 - goldenInverseSeriesAt t = C t * X * (geom a * geom b) := by
    change 1 - ((1 - C t * X) * (1 - C (5 * t) * X)) * (geom a * geom b) = _
    linear_combination -hp
  change geom a - geom b = _
  rw [hdiff, hab, map_mul, hmu]
  ring

theorem goldenInverseSeriesAt_constantCoeff (t : ℂ) :
    constantCoeff (goldenInverseSeriesAt t) = 1 := by
  simp [goldenInverseSeriesAt, geom]

/-- Every positive coefficient is the difference of the two damped geometric towers. -/
theorem goldenInverseSeriesAt_coeff (t : ℂ) (n : ℕ) (hn : n ≠ 0) :
    coeff n (goldenInverseSeriesAt t) =
      -((goldenDatum.alpha 0 * t) ^ n - (goldenDatum.alpha 1 * t) ^ n) /
        (Real.sqrt 5 : ℂ) := by
  have h := congrArg (coeff n) (goldenInverseSeriesAt_tower_difference t)
  simp only [map_sub, coeff_C_mul, geom, coeff_mk, coeff_one, hn, if_false, zero_sub] at h
  have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  apply (eq_div_iff hs).mpr
  linear_combination h

end GaloisForLFunctions.BiarithmeticGeometry
