import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import GaloisForLFunctions.RHTower.XiEndpointCentralMomentBoundaryValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The complete reciprocal-frequency sine response of the actual Xi divisor

The odd factorial source response is the sine trace over every analytic multiplicity copy.
Absolute summability on the product of zero copies and Taylor orders closes the interchange;
no square-root branch or zero-location hypothesis occurs.
-/

open scoped BigOperators

namespace RHTower
noncomputable section


/-- The branch-free sine contribution of one analytic multiplicity copy. -/
def liEvenCrossActualClockSineAtom (t : ℝ) (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q)⁻¹ * Complex.sin ((t : ℂ) * (xiSpectralPoint q)⁻¹)

/-- The odd sine coefficient with the reciprocal-square source atom kept explicit. -/
def liEvenCrossActualClockSineTaylorTerm (t : ℝ) (q : XiZeroCopy) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * (t : ℂ)^(2*j+1) * xiZeroCopyReciprocalSquare q^(j+1) /
    ((2*j+1).factorial : ℂ)

/-- The reciprocal-square coefficient is exactly the sine Taylor coefficient. -/
private theorem sineTaylorTerm_eq (t : ℝ) (q : XiZeroCopy) (j : ℕ) :
    liEvenCrossActualClockSineTaylorTerm t q j = (xiSpectralPoint q)⁻¹ *
      ((-1 : ℂ)^j * ((t : ℂ)*(xiSpectralPoint q)⁻¹)^(2*j+1) /
        ((2*j+1).factorial : ℂ)) := by
  unfold liEvenCrossActualClockSineTaylorTerm xiZeroCopyReciprocalSquare
  rw [← pow_mul]
  have hr : (xiSpectralPoint q)⁻¹^(2*(j+1)) =
      (xiSpectralPoint q)⁻¹^(2*j+1) * (xiSpectralPoint q)⁻¹ := by
    rw [show 2*(j+1)=2*j+1+1 by omega, pow_succ]
  rw [hr, mul_pow]
  ring

/-- Each source atom has its entire odd sine expansion. -/
theorem hasSum_liEvenCrossActualClockSineTaylorTerm (t : ℝ) (q : XiZeroCopy) :
    HasSum (liEvenCrossActualClockSineTaylorTerm t q)
      (liEvenCrossActualClockSineAtom t q) := by
  change HasSum (fun j : ℕ => liEvenCrossActualClockSineTaylorTerm t q j) _
  simp_rw [sineTaylorTerm_eq]
  simpa only [liEvenCrossActualClockSineAtom] using
    (Complex.hasSum_sin ((t : ℂ)*(xiSpectralPoint q)⁻¹)).mul_left
      ((xiSpectralPoint q)⁻¹)

/-- The complete source radius separates the zero-copy and Taylor-order envelopes. -/
theorem norm_liEvenCrossActualClockSineTaylorTerm_le (t : ℝ) (q : XiZeroCopy) (j : ℕ) :
    ‖liEvenCrossActualClockSineTaylorTerm t q j‖ ≤
      ‖xiZeroCopyReciprocalSquare q‖ * |t| *
        ((t^2/150)^j / ((2*j+1).factorial : ℝ)) := by
  have hq := pow_le_pow_left₀ (norm_nonneg (xiZeroCopyReciprocalSquare q))
    (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le j
  have ht : |t|^(2*j+1) = (t^2)^j * |t| := by
    rw [pow_add, pow_mul, pow_one, sq_abs]
  unfold liEvenCrossActualClockSineTaylorTerm
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, one_mul]
  rw [ht, show ‖xiZeroCopyReciprocalSquare q‖^(j+1) =
    ‖xiZeroCopyReciprocalSquare q‖^j * ‖xiZeroCopyReciprocalSquare q‖ by rw [pow_succ]]
  calc
    (t^2)^j * |t| * (‖xiZeroCopyReciprocalSquare q‖^j *
      ‖xiZeroCopyReciprocalSquare q‖) / ((2*j+1).factorial : ℝ)
      = ‖xiZeroCopyReciprocalSquare q‖ * |t| *
        ((t^2)^j * ‖xiZeroCopyReciprocalSquare q‖^j /
          ((2*j+1).factorial : ℝ)) := by ring
    _ ≤ ‖xiZeroCopyReciprocalSquare q‖ * |t| *
        ((t^2)^j * (1/150 : ℝ)^j / ((2*j+1).factorial : ℝ)) := by gcongr
    _ = ‖xiZeroCopyReciprocalSquare q‖ * |t| *
        ((t^2/150)^j / ((2*j+1).factorial : ℝ)) := by
      rw [← mul_pow, show t^2*(1/150:ℝ)=t^2/150 by ring]


/-- Absolute convergence holds on the full product of multiplicity copies and Taylor orders. -/
theorem summable_norm_liEvenCrossActualClockSineTaylorTerm (t : ℝ) :
    Summable (fun p : XiZeroCopy × ℕ =>
      ‖liEvenCrossActualClockSineTaylorTerm t p.1 p.2‖) := by
  have hq : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa using summable_xiShiftAbsoluteMass 0
  have hj := (summable_liEvenCrossActualCurrentClockFactorialEnvelope (t^2/150)
    (by positivity)).mul_left |t|
  have hmajor := hq.mul_of_nonneg hj (fun q => norm_nonneg _)
    (fun j => by positivity)
  apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ hmajor
  intro p
  exact (norm_liEvenCrossActualClockSineTaylorTerm_le t p.1 p.2).trans_eq
    (by ring)

/-- The double complex source series is summable without a zero-location premise. -/
theorem summable_liEvenCrossActualClockSineTaylorTerm (t : ℝ) :
    Summable (fun p : XiZeroCopy × ℕ =>
      liEvenCrossActualClockSineTaylorTerm t p.1 p.2) :=
  (summable_norm_liEvenCrossActualClockSineTaylorTerm t).of_norm

/-- The complete sine trace is absolutely summable at every real clock. -/
theorem summable_norm_liEvenCrossActualClockSineAtom (t : ℝ) :
    Summable (fun q : XiZeroCopy => ‖liEvenCrossActualClockSineAtom t q‖) := by
  have hd := summable_norm_liEvenCrossActualClockSineTaylorTerm t
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hd.prod
  intro q
  rw [← (hasSum_liEvenCrossActualClockSineTaylorTerm t q).tsum_eq]
  exact norm_tsum_le_tsum_norm (hd.prod_factor q)

/-- Every real clock admits the full multiplicity-exact sine trace. -/
theorem summable_liEvenCrossActualClockSineAtom (t : ℝ) :
    Summable (liEvenCrossActualClockSineAtom t) :=
  (summable_norm_liEvenCrossActualClockSineAtom t).of_norm

/-- Summing one odd coefficient over all zero copies recovers the literal source moment. -/
theorem tsum_liEvenCrossActualClockSineTaylorTerm (t : ℝ) (j : ℕ) :
    (∑' q : XiZeroCopy, liEvenCrossActualClockSineTaylorTerm t q j) =
      (liEvenCrossActualClockResponseTerm t j : ℂ) := by
  unfold liEvenCrossActualClockSineTaylorTerm
  rw [tsum_div_const, tsum_mul_left, tsum_xiZeroCopyReciprocalSquare_pow,
    ← ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment]
  unfold liEvenCrossActualClockResponseTerm
  push_cast
  ring

/-- The literal real response equals the full complex reciprocal-frequency sine trace. -/
theorem liEvenCrossActualClockResponse_ofReal_eq_tsum_sine (t : ℝ) :
    (liEvenCrossActualClockResponse t : ℂ) =
      ∑' q : XiZeroCopy, liEvenCrossActualClockSineAtom t q := by
  rw [liEvenCrossActualClockResponse_eq_tsum, Complex.ofReal_tsum]
  simp_rw [← tsum_liEvenCrossActualClockSineTaylorTerm]
  have hcomm : (∑' j : ℕ, ∑' q : XiZeroCopy,
      liEvenCrossActualClockSineTaylorTerm t q j) =
      ∑' q : XiZeroCopy, ∑' j : ℕ, liEvenCrossActualClockSineTaylorTerm t q j :=
    Summable.tsum_comm (f := fun q j => liEvenCrossActualClockSineTaylorTerm t q j)
      (summable_liEvenCrossActualClockSineTaylorTerm t)
  rw [hcomm]
  apply tsum_congr
  intro q
  exact (hasSum_liEvenCrossActualClockSineTaylorTerm t q).tsum_eq

/-- Taking the real part preserves the exact normalization of the literal response. -/
theorem liEvenCrossActualClockResponse_eq_re_tsum_sine (t : ℝ) :
    liEvenCrossActualClockResponse t =
      (∑' q : XiZeroCopy, liEvenCrossActualClockSineAtom t q).re := by
  simpa using congrArg Complex.re (liEvenCrossActualClockResponse_ofReal_eq_tsum_sine t)

/-- The full complex source trace is real at every real clock. -/
theorem im_tsum_liEvenCrossActualClockSineAtom_eq_zero (t : ℝ) :
    (∑' q : XiZeroCopy, liEvenCrossActualClockSineAtom t q).im = 0 := by
  rw [← liEvenCrossActualClockResponse_ofReal_eq_tsum_sine]
  rfl

end
end RHTower
