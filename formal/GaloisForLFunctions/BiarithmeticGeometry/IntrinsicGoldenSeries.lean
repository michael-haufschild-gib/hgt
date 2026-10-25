import GaloisForLFunctions.BiarithmeticGeometry.GoldenArithmeticSource

/-!
# The intrinsic golden counting receiver

The generalized-integer counting series is the golden zeta series itself. Centering its
convolution with the damped inverse cancels the counting pole exactly. The remaining
factorization separates the two Frobenius roots from the double cumulative-count pole.
-/

noncomputable section
open PowerSeries GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The cumulative generalized-integer counting series of the golden datum. -/
def goldenIntrinsicCountSeries : ℂ⟦X⟧ := goldenDatum.zetaSeries * geom 1

/-- The exact counting partial fractions separate the exponential and affine terms. -/
theorem goldenIntrinsicCountSeries_partialFractions :
    C 16 * goldenIntrinsicCountSeries =
      C 5 * geom 5 - C 4 * geom 1 ^ 2 + C 15 * geom 1 := by
  have h1 : (1 - X) * geom (1 : ℂ) = 1 := by
    simpa only [map_one, one_mul] using one_sub_mul_geom (1 : ℂ)
  have h5 : (1 - 5 * X) * geom (5 : ℂ) = 1 := by
    simpa only [map_ofNat] using one_sub_mul_geom (5 : ℂ)
  have hp : 16 * goldenDatum.hOnePoly =
      5 * (1 - X) ^ 2 - 4 * (1 - 5 * X) + 15 * (1 - X) * (1 - 5 * X) := by
    rw [goldenDatum_hOnePoly]
    simp only [map_ofNat]
    ring
  simp only [map_ofNat]
  rw [goldenIntrinsicCountSeries, CurveDatum.zetaSeries, CurveDatum.poleZeta]
  change 16 * ((geom 1 * geom 5 * goldenDatum.hOnePoly) * geom 1) = _
  calc
    _ = (16 * goldenDatum.hOnePoly) * (geom 1 ^ 2 * geom 5) := by ring
    _ = (5 * (1 - X) ^ 2 - 4 * (1 - 5 * X) +
        15 * (1 - X) * (1 - 5 * X)) * (geom 1 ^ 2 * geom 5) := by rw [hp]
    _ = 5 * geom 5 * ((1 - X) * geom 1) ^ 2 -
        4 * geom 1 ^ 2 * ((1 - 5 * X) * geom 5) +
        15 * geom 1 * ((1 - X) * geom 1) * ((1 - 5 * X) * geom 5) := by ring
    _ = _ := by rw [h1, h5]; ring

private theorem coeff_geom_one_sq (M : ℕ) :
    coeff M (geom (1 : ℂ) ^ 2) = (M : ℂ) + 1 := by
  simp [pow_two, coeff_mul, geom]

/-- Every cumulative counting coefficient has an exact exponential-affine formula. -/
theorem coeff_goldenIntrinsicCountSeries (M : ℕ) :
    coeff M goldenIntrinsicCountSeries = (5 / 16 : ℂ) * 5 ^ M - (M : ℂ) / 4 + 11 / 16 := by
  have h := congrArg (coeff M) goldenIntrinsicCountSeries_partialFractions
  simp only [map_sub, map_add, coeff_C_mul] at h
  rw [coeff_geom_one_sq] at h
  simp only [geom, coeff_mk, one_pow] at h
  linear_combination (1 / 16 : ℂ) * h

/-- The real cumulative generalized-integer count at norm `5^M`. -/
def goldenIntrinsicCount (M : ℕ) : ℝ := (coeff M goldenIntrinsicCountSeries).re

theorem goldenIntrinsicCount_eq (M : ℕ) :
    goldenIntrinsicCount M = (5 / 16 : ℝ) * 5 ^ M - (M : ℝ) / 4 + 11 / 16 := by
  rw [goldenIntrinsicCount, coeff_goldenIntrinsicCountSeries]
  norm_cast
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re]
  change (((5 : ℝ) : ℂ) ^ M).re = (5 : ℝ) ^ M
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Successive cumulative counts have an exact positive exponential increment. -/
theorem goldenIntrinsicCount_increment (M : ℕ) :
    goldenIntrinsicCount (M + 1) - goldenIntrinsicCount M =
      (5 / 4 : ℝ) * 5 ^ M - 1 / 4 := by
  rw [goldenIntrinsicCount_eq, goldenIntrinsicCount_eq, pow_succ]
  push_cast
  ring

/-- The exact count lies between zero and its ambient exponential scale. -/
theorem goldenIntrinsicCount_bounds (M : ℕ) :
    0 ≤ goldenIntrinsicCount M ∧ goldenIntrinsicCount M ≤ (5 : ℝ) ^ M := by
  have hpow : (M : ℝ) + 1 ≤ (5 : ℝ) ^ M := by
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith only [ih, Nat.cast_nonneg (α := ℝ) M]
  rw [goldenIntrinsicCount_eq]
  constructor <;> nlinarith only [hpow, Nat.cast_nonneg (α := ℝ) M]

/-- Center the intrinsic cumulative counting response by the actual arithmetic source mean. -/
def goldenIntrinsicReceiverSeries (t : ℝ) : ℂ⟦X⟧ :=
  goldenDatum.zetaSeries * geom 1 *
    (goldenInverseSeriesAt (t : ℂ) -
      C ((∑' n : ℕ, goldenArithmeticSource t n / n : ℝ) : ℂ))

private theorem golden_damped_numerator (t : ℂ) :
    (1 - C (goldenDatum.alpha 0 * t) * X) * (1 - C (goldenDatum.alpha 1 * t) * X) =
      1 - C (5 * t) * X + C (5 * t ^ 2) * X ^ 2 := by
  calc
    _ = 1 - C ((goldenDatum.alpha 0 + goldenDatum.alpha 1) * t) * X +
        C ((goldenDatum.alpha 0 * goldenDatum.alpha 1) * t ^ 2) * X ^ 2 := by
      simp only [map_add, map_mul, map_pow]
      ring
    _ = _ := by rw [goldenDatum_alpha_sum, goldenDatum_alpha_mul]

private theorem golden_intrinsic_pole_cancellation (t : ℝ) (ht1 : t ≤ 1) :
    (1 - C (t : ℂ) * X) * (1 - C (5 * (t : ℂ)) * X) -
      C (goldenArithmeticMean t : ℂ) *
        ((1 - C (goldenDatum.alpha 0 * (t : ℂ)) * X) *
          (1 - C (goldenDatum.alpha 1 * (t : ℂ)) * X)) =
      C ((t / (5 - 5 * t + t ^ 2) : ℝ) : ℂ) *
        (1 - C 5 * X) * (1 - C ((t ^ 2 : ℝ) : ℂ) * X) := by
  have hD : 5 - 5 * t + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg (t - 1), ht1])
  have h0 : 1 - goldenArithmeticMean t = t / (5 - 5 * t + t ^ 2) := by
    unfold goldenArithmeticMean
    rw [show 5 - 6 * t + t ^ 2 = (5 - 5 * t + t ^ 2) - t by ring,
      sub_div, div_self hD]
    ring
  have h1 : t * (5 * goldenArithmeticMean t - 6) =
      -(t / (5 - 5 * t + t ^ 2)) * (5 + t ^ 2) := by
    have hc : (t / (5 - 5 * t + t ^ 2)) * (5 - 5 * t + t ^ 2) = t :=
      div_mul_cancel₀ t hD
    linear_combination -(5 * t) * h0 + hc
  rw [golden_damped_numerator]
  calc
    _ = C ((1 - goldenArithmeticMean t : ℝ) : ℂ) +
        C ((t * (5 * goldenArithmeticMean t - 6) : ℝ) : ℂ) * X +
        C ((5 * t ^ 2 * (1 - goldenArithmeticMean t) : ℝ) : ℂ) * X ^ 2 := by
      push_cast
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat]
      ring
    _ = _ := by
      rw [h0, h1]
      push_cast
      simp only [map_neg, map_add, map_mul, map_pow, map_ofNat]
      ring

/-- The actual centered counting series has its counting pole cancelled, at every damping. -/
theorem goldenIntrinsicReceiverSeries_factorization (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    goldenIntrinsicReceiverSeries t =
      C ((t / (5 - 5 * t + t ^ 2) : ℝ) : ℂ) * goldenDatum.hOnePoly *
        (1 - C ((t ^ 2 : ℝ) : ℂ) * X) * geom 1 ^ 2 *
          (geom (goldenDatum.alpha 0 * (t : ℂ)) * geom (goldenDatum.alpha 1 * (t : ℂ))) := by
  let P : ℂ⟦X⟧ := (1 - C (goldenDatum.alpha 0 * (t : ℂ)) * X) *
    (1 - C (goldenDatum.alpha 1 * (t : ℂ)) * X)
  let Q : ℂ⟦X⟧ := (1 - C (t : ℂ) * X) * (1 - C (5 * (t : ℂ)) * X)
  let G : ℂ⟦X⟧ := geom (goldenDatum.alpha 0 * (t : ℂ)) *
    geom (goldenDatum.alpha 1 * (t : ℂ))
  have hPG : P * G = 1 := by
    dsimp [P, G]
    calc
      _ = ((1 - C (goldenDatum.alpha 0 * (t : ℂ)) * X) *
          geom (goldenDatum.alpha 0 * (t : ℂ))) *
        ((1 - C (goldenDatum.alpha 1 * (t : ℂ)) * X) *
          geom (goldenDatum.alpha 1 * (t : ℂ))) := by ring
      _ = 1 := by rw [one_sub_mul_geom, one_sub_mul_geom, one_mul]
  have hsub : goldenInverseSeriesAt (t : ℂ) - C (goldenArithmeticMean t : ℂ) =
      (Q - C (goldenArithmeticMean t : ℂ) * P) * G := by
    change Q * G - C (goldenArithmeticMean t : ℂ) = _
    linear_combination C (goldenArithmeticMean t : ℂ) * hPG
  have hcancel : Q - C (goldenArithmeticMean t : ℂ) * P =
      C ((t / (5 - 5 * t + t ^ 2) : ℝ) : ℂ) *
        (1 - C 5 * X) * (1 - C ((t ^ 2 : ℝ) : ℂ) * X) :=
    golden_intrinsic_pole_cancellation t ht1
  rw [goldenIntrinsicReceiverSeries, goldenArithmeticSource_mean t ht0 ht1, hsub, hcancel]
  rw [CurveDatum.zetaSeries, CurveDatum.poleZeta]
  change (geom 1 * geom 5 * goldenDatum.hOnePoly) * geom 1 * _ = _
  calc
    _ = ((1 - C 5 * X) * geom 5) *
        (C ((t / (5 - 5 * t + t ^ 2) : ℝ) : ℂ) * goldenDatum.hOnePoly *
          (1 - C ((t ^ 2 : ℝ) : ℂ) * X) * geom 1 ^ 2 * G) := by ring
    _ = _ := by rw [one_sub_mul_geom, one_mul]

/-- At maximal damping the inverse source is the unit and its centered intrinsic row vanishes. -/
theorem goldenIntrinsicReceiverSeries_zero : goldenIntrinsicReceiverSeries 0 = 0 := by
  simpa using goldenIntrinsicReceiverSeries_factorization 0 (by norm_num) (by norm_num)

/-- At zero damping the intrinsic inverse cancels the whole zeta series. -/
theorem goldenIntrinsicReceiverSeries_one : goldenIntrinsicReceiverSeries 1 = geom 1 := by
  rw [goldenIntrinsicReceiverSeries, goldenArithmeticSource_mean 1 (by norm_num) (by norm_num)]
  norm_num only [goldenArithmeticMean, mul_one, one_pow, sub_self, zero_add, zero_div,
    Complex.ofReal_zero, Complex.ofReal_one, map_zero, sub_zero]
  calc
    _ = geom 1 * (goldenInverseSeriesAt 1 * goldenZetaSeriesAt 1) := by
      rw [goldenZetaSeriesAt_one]
      ring
    _ = geom 1 := by rw [goldenInverseSeriesAt_mul, mul_one]

end GaloisForLFunctions.BiarithmeticGeometry
