import GaloisForLFunctions.RHTower.SquaredXiThreePointOrbitPositivity
import GaloisForLFunctions.RHTower.XiSquaredEulerApertureHilbertCorrelation

/-!
# Three-point/derivative-Hankel polarity split for actual Xi orbits

The protected three-point response matrix of `SquaredXiThreePointOrbitPositivity` is genuinely
positive for every actual squared-Xi conjugate orbit: the current source height gap and critical
strip place its parameters in the exact theorem chamber.

That positivity has the wrong polarization for the mass-shifted Hankel face.  The same genuinely
off-critical orbit has a strictly negative first confluent derivative-Hankel minor, by the exact
transverse-charge identity in `XiSquaredEulerApertureHilbertCorrelation`.  This file closes the
actual-Xi specialization and packages both signs in one unconditional classification theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every actual squared-Xi orbit has longitudinal parameter strictly above the protected
three-point threshold. -/
theorem two_lt_xiSquaredEulerOrbitT (q : XiZeroCopy) :
    2 < xiSquaredEulerOrbitT q := by
  have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  unfold xiSquaredEulerOrbitT
  linarith

/-- The actual transverse orbit charge is nonnegative. -/
theorem xiSquaredEulerOrbitCharge_nonneg (q : XiZeroCopy) :
    0 ≤ xiSquaredEulerOrbitCharge q := by
  unfold xiSquaredEulerOrbitCharge
  positivity

/-- The critical strip gives the sharper linear chamber wall required by the protected
three-point matrix. -/
theorem xiSquaredEulerOrbitCharge_lt_t_add_quarter (q : XiZeroCopy) :
    xiSquaredEulerOrbitCharge q < xiSquaredEulerOrbitT q + 1 / 4 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  have hu : u < 1 / 4 := by
    simpa only [u] using xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hv : 41 / 2 < v := by
    simpa only [v] using xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hfactor : 0 < (1 - 4 * u) * (v + 1 / 4) :=
    mul_pos (by linarith) (by linarith)
  change 4 * u * v < (v - u) + 1 / 4
  nlinarith

/-- **Actual-Xi protected three-point positivity.**  The abstract orbit matrix theorem applies to
every Xi zero copy, with no numerical zero input and no RH premise. -/
theorem xiSquaredEulerOrbitMatrix_posDef (q : XiZeroCopy) :
    Matrix.PosDef
      (orbitMatrix (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q)) := by
  exact orbitMatrix_posDef (two_lt_xiSquaredEulerOrbitT q)
    (xiSquaredEulerOrbitCharge_nonneg q)
    (xiSquaredEulerOrbitCharge_lt_t_add_quarter q).le

/-- On-line orbits have zero confluent first derivative-Hankel minor. -/
theorem xiSquaredEulerAperture_singleOrbitCentralMinor_eq_zero_of_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    xiSquaredEulerFiniteApertureCentralMinor {q} = 0 := by
  rw [xiSquaredEulerAperture_singleOrbitCentralMinor_eq]
  have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mpr hline
  rw [him]
  norm_num

/-- **Closed separated/confluent polarity classification.**  Every actual orbit has a positive
separated-point matrix.  Its first confluent derivative-Hankel minor is zero on the critical line
and strictly negative off it.  Thus protected three-point positivity cannot orient the shifted
Hankel boundary. -/
theorem xiSquaredEulerOrbitSeparatedConfluentPolarity :
    ∀ q : XiZeroCopy,
      Matrix.PosDef
          (orbitMatrix (xiSquaredEulerOrbitT q) (xiSquaredEulerOrbitCharge q)) ∧
      ((q.1 : ℂ).re = 1 / 2 →
        xiSquaredEulerFiniteApertureCentralMinor {q} = 0) ∧
      ((q.1 : ℂ).re ≠ 1 / 2 →
        xiSquaredEulerFiniteApertureCentralMinor {q} < 0) := by
  intro q
  exact ⟨xiSquaredEulerOrbitMatrix_posDef q,
    xiSquaredEulerAperture_singleOrbitCentralMinor_eq_zero_of_eq_half q,
    xiSquaredEulerAperture_singleOrbitCentralMinor_neg_of_ne_half q⟩

end

end RHTower
