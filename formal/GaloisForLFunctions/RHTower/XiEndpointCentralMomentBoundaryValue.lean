import GaloisForLFunctions.RHTower.XiEndpointCentralMomentDyadicBridge
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# The endpoint curvature is a boundary value of the central moment germ

The centered reciprocal-square moment germ and the completed endpoint source are not independent
coordinates.  The source-pure height gap puts every centered reciprocal-square coordinate inside
the unit disk, so the divisor resolvent expansion remains valid at `z = I / 2`.  At that point its
individual terms are exactly the FE--Schwarz endpoint cross terms.  Consequently

`xiCentralMomentGerm (I / 2) = xiEndpointCompletedCurvature`.

Equivalently, the completed endpoint curvature is the convergent signed value

`sum n, normalizedPrimeArchMoment n * (-1 / 4)^n`.

This is an unconditional source-to-source value relation.  It removes the endpoint calibration as
independent input from any continuation or finite-moment argument using the central Taylor germ;
it does not assert moment positivity or RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- The strong endpoint height gap puts every centered reciprocal-square divisor coordinate
strictly inside the unit disk. -/
theorem xiZeroCopyReciprocalSquare_norm_lt_one (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ < 1 := by
  have hheight := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have himAbs : 1 < |(q.1 : ℂ).im| := by
    nlinarith [sq_abs (q.1 : ℂ).im, abs_nonneg (q.1 : ℂ).im]
  have himNorm : |(q.1 : ℂ).im| ≤ ‖(q.1 : ℂ) - 1 / 2‖ := by
    simpa using Complex.abs_im_le_norm ((q.1 : ℂ) - 1 / 2)
  have hspec : 1 < ‖xiSpectralPoint q‖ := by
    rw [norm_xiSpectralPoint]
    exact himAbs.trans_le himNorm
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv]
  exact pow_lt_one₀ (inv_nonneg.mpr (norm_nonneg _))
    (inv_lt_one_of_one_lt₀ hspec) (by omega)

/-- The even powers at the endpoint reduce to the signed quarter-geometric coordinate. -/
theorem I_half_pow_two_mul (n : ℕ) :
    (I / 2 : ℂ) ^ (2 * n) = (-1 / 4 : ℂ) ^ n := by
  rw [pow_mul]
  congr 1
  field_simp
  rw [I_sq]
  ring

/-- The centered reciprocal-moment endpoint series is absolutely summable. -/
theorem summable_xiCentralReciprocalMoment_endpointSeries :
    Summable (fun n : ℕ =>
      xiCentralReciprocalMoment n * (-1 / 4 : ℂ) ^ n) := by
  let S : ℝ := ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmajor : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n * S) :=
    hgeom.mul_right S
  apply Summable.of_norm_bounded hmajor
  intro n
  have hmoment := norm_xiCentralReciprocalMoment_le
    (fun q => (xiZeroCopyReciprocalSquare_norm_lt_one q).le) n
  have hmoment' : ‖xiCentralReciprocalMoment n‖ ≤ S := by
    simpa only [one_pow, one_mul, S] using hmoment
  rw [norm_mul, norm_pow]
  have hquarter : ‖(-1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
  rw [hquarter]
  exact mul_le_mul_of_nonneg_right hmoment'
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n)

/-- At the endpoint, the central moment germ is the exact FE--Schwarz endpoint cross trace. -/
theorem xiCentralMomentGerm_I_half_eq_endpointCrossTrace :
    xiCentralMomentGerm (I / 2) =
      ∑' q : XiZeroCopy,
        xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)) := by
  rw [xiCentralMomentGerm_eq_reciprocalSquareResolvent
    (M := 1) le_rfl
    (fun q => (xiZeroCopyReciprocalSquare_norm_lt_one q).le) (z := I / 2)]
  · apply tsum_congr
    exact endpoint_term_eq
  · norm_num

/-- The real part of the boundary value is the completed endpoint curvature. -/
theorem xiCentralMomentGerm_I_half_re_eq_endpointCompletedCurvature :
    (xiCentralMomentGerm (I / 2)).re = xiEndpointCompletedCurvature := by
  rw [xiCentralMomentGerm_I_half_eq_endpointCrossTrace,
    xiEndpointCompletedCurvature_eq_cross_re]

/-- The boundary value is real because every centered reciprocal moment is real and the endpoint
even powers are real. -/
theorem xiCentralMomentGerm_I_half_im_eq_zero :
    (xiCentralMomentGerm (I / 2)).im = 0 := by
  have hsum : Summable (fun n : ℕ =>
      xiCentralReciprocalMoment n * (I / 2 : ℂ) ^ (2 * n)) :=
    summable_xiCentralReciprocalMoment_endpointSeries.congr (fun n => by
      rw [I_half_pow_two_mul])
  rw [xiCentralMomentGerm_eq_tsum_even, Complex.im_tsum hsum]
  calc
    (∑' n : ℕ,
        (xiCentralReciprocalMoment n * (I / 2 : ℂ) ^ (2 * n)).im) =
        ∑' _n : ℕ, 0 := by
      apply tsum_congr
      intro n
      rw [I_half_pow_two_mul]
      have hmoment := xiCentralReciprocalMoment_im_eq_zero n
      simp [Complex.mul_im, hmoment]
    _ = 0 := tsum_zero

/-- **Endpoint/central boundary value law.**  The completed endpoint curvature is exactly the
complex boundary value of the centered moment germ. -/
theorem xiCentralMomentGerm_I_half_eq_endpointCompletedCurvature :
    xiCentralMomentGerm (I / 2) = (xiEndpointCompletedCurvature : ℂ) := by
  apply Complex.ext
  · simpa using xiCentralMomentGerm_I_half_re_eq_endpointCompletedCurvature
  · simpa using xiCentralMomentGerm_I_half_im_eq_zero

/-- The normalized prime--archimedean moments are the same complex centered moments. -/
theorem ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment (n : ℕ) :
    (normalizedPrimeArchMoment n : ℂ) = xiCentralReciprocalMoment n := by
  simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
    primeArchSourceMoment_eq_xiCentralReciprocalMoment n

/-- The endpoint curvature is the absolutely convergent signed-quarter value of the fixed
prime--archimedean Taylor moments. -/
theorem hasSum_normalizedPrimeArchMoment_endpointCurvature :
    HasSum (fun n : ℕ =>
      (normalizedPrimeArchMoment n : ℂ) * (-1 / 4 : ℂ) ^ n)
      (xiEndpointCompletedCurvature : ℂ) := by
  have hcentral : HasSum (fun n : ℕ =>
      xiCentralReciprocalMoment n * (-1 / 4 : ℂ) ^ n)
      (xiEndpointCompletedCurvature : ℂ) := by
    have heven : HasSum (fun n : ℕ =>
        xiCentralReciprocalMoment n * (I / 2 : ℂ) ^ (2 * n))
        (xiCentralMomentGerm (I / 2)) := by
      rw [xiCentralMomentGerm_eq_tsum_even]
      exact (summable_xiCentralReciprocalMoment_endpointSeries.congr (fun n => by
        rw [I_half_pow_two_mul])).hasSum
    rw [xiCentralMomentGerm_I_half_eq_endpointCompletedCurvature] at heven
    apply HasSum.congr_fun heven
    intro n
    rw [I_half_pow_two_mul]
  apply HasSum.congr_fun hcentral
  intro n
  rw [ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment]

/-- Tsum form of the same exact source-value relation. -/
theorem tsum_normalizedPrimeArchMoment_endpointCurvature :
    (∑' n : ℕ,
      (normalizedPrimeArchMoment n : ℂ) * (-1 / 4 : ℂ) ^ n) =
      (xiEndpointCompletedCurvature : ℂ) :=
  hasSum_normalizedPrimeArchMoment_endpointCurvature.tsum_eq

end

end RHTower
