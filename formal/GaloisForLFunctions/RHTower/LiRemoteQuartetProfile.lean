import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact Li profile of a polar quartet

This module isolates the finite algebraic core of the remote-quartet visibility law.  If
`q = exp (ell + i theta)` is the Li Möbius coordinate of one zero, the symmetry-complete orbit
`q, q⁻¹, conj q, (conj q)⁻¹` contributes exactly

`4 * (1 - cosh (n * ell) * cos (n * theta))`.

Deleting only the radial coordinate gives the nonnegative unit-circle shadow.  Their exact
difference and its uniform finite-prefix bound separate angular oscillation from transverse
off-line displacement without any asymptotic or numerical input.
-/

namespace RHTower

noncomputable section

/-- Polar Li coordinate `exp (ell + i theta)`. -/
def liQuartetPolarCoordinate (ell theta : ℝ) : ℂ :=
  Complex.exp ((ell : ℂ) + (theta : ℂ) * Complex.I)

/-- Contribution of the symmetry-complete Möbius orbit
`q, q⁻¹, conj q, (conj q)⁻¹` to the `n`th Li sum. -/
def liPolarQuartetContribution (n : ℕ) (q : ℂ) : ℂ :=
  4 - (q ^ n + q⁻¹ ^ n + (starRingEnd ℂ q) ^ n + (starRingEnd ℂ q)⁻¹ ^ n)

/-- Exact real hyperbolic--oscillatory profile of a polar Li quartet. -/
def liRemoteQuartetProfile (n : ℕ) (ell theta : ℝ) : ℝ :=
  4 * (1 - Real.cosh ((n : ℝ) * ell) * Real.cos ((n : ℝ) * theta))

/-- Unit-circle shadow obtained by deleting only the radial defect `ell`. -/
def liUnitarizedQuartetProfile (n : ℕ) (theta : ℝ) : ℝ :=
  4 * (1 - Real.cos ((n : ℝ) * theta))

/-- Upper member `1/2 - a + iT` of the off-critical quartet used by the card. -/
def liRemoteQuartetZero (a T : ℝ) : ℂ :=
  ((1 / 2 - a : ℝ) : ℂ) + (T : ℂ) * Complex.I

/-- Li Möbius coordinate `1 - 1/rho`. -/
def liMobiusCoordinate (rho : ℂ) : ℂ := 1 - rho⁻¹

/-- Exact Cartesian Li coordinate of a point `beta + iT`. -/
theorem liMobiusCoordinate_realPart_height {beta T : ℝ} (hT : T ≠ 0) :
    liMobiusCoordinate ((beta : ℂ) + (T : ℂ) * Complex.I) =
      (((T ^ 2 - beta * (1 - beta)) / (T ^ 2 + beta ^ 2) : ℝ) : ℂ) +
        (((T / (T ^ 2 + beta ^ 2) : ℝ) : ℂ) * Complex.I) := by
  have hden : T ^ 2 + beta ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hT]
  have hden' : beta ^ 2 + T ^ 2 ≠ 0 := by
    simpa [add_comm] using hden
  apply Complex.ext
  · rw [liMobiusCoordinate, Complex.sub_re, Complex.one_re, Complex.inv_re]
    simp only [Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
      sub_zero, zero_add]
    field_simp [hden, hden']
    ring
  · rw [liMobiusCoordinate, Complex.sub_im, Complex.one_im, Complex.inv_im]
    simp only [Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, zero_add]
    field_simp [hden, hden']
    ring

/-- Card equation (2): exact Cartesian Li coordinate of `1/2 - a + iT`. -/
theorem liMobiusCoordinate_remoteQuartetZero {a T : ℝ} (hT : T ≠ 0) :
    liMobiusCoordinate (liRemoteQuartetZero a T) =
      (((T ^ 2 - (1 / 2 - a) * (1 - (1 / 2 - a))) /
          (T ^ 2 + (1 / 2 - a) ^ 2) : ℝ) : ℂ) +
        (((T / (T ^ 2 + (1 / 2 - a) ^ 2) : ℝ) : ℂ) * Complex.I) := by
  simpa only [liRemoteQuartetZero] using
    (liMobiusCoordinate_realPart_height (beta := 1 / 2 - a) hT)

/-- Squared modulus of the Li coordinate of `beta + iT`. -/
theorem normSq_liMobiusCoordinate_realPart_height {beta T : ℝ} (hT : T ≠ 0) :
    Complex.normSq
        (liMobiusCoordinate ((beta : ℂ) + (T : ℂ) * Complex.I)) =
      (T ^ 2 + (1 - beta) ^ 2) / (T ^ 2 + beta ^ 2) := by
  rw [liMobiusCoordinate_realPart_height hT, Complex.normSq_apply]
  have hden : T ^ 2 + beta ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hT]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, zero_add]
  field_simp [hden]
  ring

/-- Card equation (3) before taking logarithms: the squared radial defect is exactly
`1 + 2a / (T² + (1/2-a)²)`. -/
theorem normSq_liMobiusCoordinate_remoteQuartetZero {a T : ℝ} (hT : T ≠ 0) :
    Complex.normSq (liMobiusCoordinate (liRemoteQuartetZero a T)) =
      1 + 2 * a / (T ^ 2 + (1 / 2 - a) ^ 2) := by
  rw [liRemoteQuartetZero,
    normSq_liMobiusCoordinate_realPart_height (beta := 1 / 2 - a) hT]
  have hden : T ^ 2 + (1 / 2 - a) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hT]
  field_simp [hden]
  ring

/-- Card equation (3): logarithmic radial coordinate of the remote Li quartet. -/
def liRemoteRadialCoordinate (a T : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + 2 * a / (T ^ 2 + (1 / 2 - a) ^ 2))

/-- A genuine horizontal displacement gives a strictly positive radial coordinate. -/
theorem liRemoteRadialCoordinate_pos {a T : ℝ} (ha : 0 < a) (hT : T ≠ 0) :
    0 < liRemoteRadialCoordinate a T := by
  have hden : 0 < T ^ 2 + (1 / 2 - a) ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hT]
  have hfrac : 0 < 2 * a / (T ^ 2 + (1 / 2 - a) ^ 2) :=
    div_pos (by positivity) hden
  unfold liRemoteRadialCoordinate
  exact mul_pos (by norm_num) (Real.log_pos (by linarith))

/-- The exponential of twice the logarithmic radius is exactly the Li coordinate's squared
modulus. -/
theorem exp_two_mul_liRemoteRadialCoordinate {a T : ℝ}
    (ha : 0 < a) (hT : T ≠ 0) :
    Real.exp (2 * liRemoteRadialCoordinate a T) =
      Complex.normSq (liMobiusCoordinate (liRemoteQuartetZero a T)) := by
  rw [normSq_liMobiusCoordinate_remoteQuartetZero hT,
    liRemoteRadialCoordinate]
  have hden : 0 < T ^ 2 + (1 / 2 - a) ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hT]
  have hfrac : 0 < 2 * a / (T ^ 2 + (1 / 2 - a) ^ 2) :=
    div_pos (by positivity) hden
  convert Real.exp_log (by linarith :
      0 < 1 + 2 * a / (T ^ 2 + (1 / 2 - a) ^ 2)) using 1
  ring_nf

/-- The symmetry-complete complex Li sum is exactly the real cosh--cos profile. -/
theorem liPolarQuartetContribution_eq_profile (n : ℕ) (ell theta : ℝ) :
    liPolarQuartetContribution n (liQuartetPolarCoordinate ell theta) =
      (liRemoteQuartetProfile n ell theta : ℂ) := by
  let z : ℂ := (ell : ℂ) + (theta : ℂ) * Complex.I
  have hzre : z.re = ell := by simp [z]
  have hzim : z.im = theta := by simp [z]
  have hconjre : ((starRingEnd ℂ) z).re = ell := by simp [hzre]
  have hconjim : ((starRingEnd ℂ) z).im = -theta := by simp [hzim]
  rw [liPolarQuartetContribution, liQuartetPolarCoordinate]
  change 4 -
      (Complex.exp z ^ n + (Complex.exp z)⁻¹ ^ n +
        ((starRingEnd ℂ) (Complex.exp z)) ^ n +
        ((starRingEnd ℂ) (Complex.exp z))⁻¹ ^ n) = _
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_nat_mul,
    ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_neg,
    ← Complex.exp_nat_mul]
  have hprofile :
      4 - Real.exp ((n : ℝ) * ell) * Real.cos ((n : ℝ) * theta) * 2 -
          Real.cos ((n : ℝ) * theta) * Real.exp (-((n : ℝ) * ell)) * 2 =
        liRemoteQuartetProfile n ell theta := by
    rw [liRemoteQuartetProfile, Real.cosh_eq]
    ring
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.exp_re,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero, Complex.neg_re, hzre, hzim, hconjre,
      hconjim, Complex.ofReal_re]
    norm_num
    rw [hzim]
    calc
      4 -
          (Real.exp ((n : ℝ) * ell) * Real.cos ((n : ℝ) * theta) +
            Real.exp (-((n : ℝ) * ell)) * Real.cos ((n : ℝ) * theta) +
            Real.exp ((n : ℝ) * ell) * Real.cos ((n : ℝ) * theta) +
            Real.exp (-((n : ℝ) * ell)) * Real.cos ((n : ℝ) * theta)) =
          4 - Real.exp ((n : ℝ) * ell) * Real.cos ((n : ℝ) * theta) * 2 -
            Real.cos ((n : ℝ) * theta) * Real.exp (-((n : ℝ) * ell)) * 2 := by
        ring
      _ = liRemoteQuartetProfile n ell theta := hprofile
  · simp [Complex.exp_im, z]

/-- Exact transverse difference from the unit-circle shadow. -/
theorem liRemoteQuartetProfile_sub_unitarized (n : ℕ) (ell theta : ℝ) :
    liRemoteQuartetProfile n ell theta - liUnitarizedQuartetProfile n theta =
      -4 * Real.cos ((n : ℝ) * theta) *
        (Real.cosh ((n : ℝ) * ell) - 1) := by
  unfold liRemoteQuartetProfile liUnitarizedQuartetProfile
  ring

/-- Every unitarized quartet contribution is nonnegative. -/
theorem liUnitarizedQuartetProfile_nonneg (n : ℕ) (theta : ℝ) :
    0 ≤ liUnitarizedQuartetProfile n theta := by
  unfold liUnitarizedQuartetProfile
  nlinarith [Real.cos_le_one ((n : ℝ) * theta)]

/-- Uniform finite-prefix defect bound, strengthened to arbitrary signed radial coordinate. -/
theorem abs_liRemoteQuartetProfile_sub_unitarized_le {n N : ℕ}
    (hn : n ≤ N) (ell theta : ℝ) :
    |liRemoteQuartetProfile n ell theta - liUnitarizedQuartetProfile n theta| ≤
      4 * (Real.cosh ((N : ℝ) * |ell|) - 1) := by
  rw [liRemoteQuartetProfile_sub_unitarized, abs_mul, abs_mul]
  have hncast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have harg : |(n : ℝ) * ell| ≤ |(N : ℝ) * abs ell| := by
    simpa [abs_mul] using
      (mul_le_mul_of_nonneg_right hncast (abs_nonneg ell))
  have hcosh := Real.cosh_le_cosh.mpr harg
  have hsmall : 0 ≤ Real.cosh ((n : ℝ) * ell) - 1 := by
    linarith [Real.one_le_cosh ((n : ℝ) * ell)]
  have hlarge : 0 ≤ Real.cosh ((N : ℝ) * |ell|) - 1 := by
    linarith [Real.one_le_cosh ((N : ℝ) * |ell|)]
  rw [abs_of_nonneg hsmall]
  norm_num
  nlinarith [Real.abs_cos_le_one ((n : ℝ) * theta),
    abs_nonneg (Real.cos ((n : ℝ) * theta))]

/-- Uniform lower bound for every member of a finite Li prefix. -/
theorem liRemoteQuartetProfile_lower_bound {n N : ℕ}
    (hn : n ≤ N) (ell theta : ℝ) :
    -4 * (Real.cosh ((N : ℝ) * |ell|) - 1) ≤
      liRemoteQuartetProfile n ell theta := by
  have hdefect := neg_le_of_abs_le
    (abs_liRemoteQuartetProfile_sub_unitarized_le hn ell theta)
  have hunit := liUnitarizedQuartetProfile_nonneg n theta
  linarith

/-- Card form of the defect estimate for a nonnegative polar radius. -/
theorem abs_liRemoteQuartetProfile_sub_unitarized_le_of_nonneg {n N : ℕ}
    (hn : n ≤ N) {ell : ℝ} (hell : 0 ≤ ell) (theta : ℝ) :
    |liRemoteQuartetProfile n ell theta - liUnitarizedQuartetProfile n theta| ≤
      4 * (Real.cosh ((N : ℝ) * ell) - 1) := by
  simpa [abs_of_nonneg hell] using
    (abs_liRemoteQuartetProfile_sub_unitarized_le hn ell theta)

/-- Card form of the profile lower bound for a nonnegative polar radius. -/
theorem liRemoteQuartetProfile_lower_bound_of_nonneg {n N : ℕ}
    (hn : n ≤ N) {ell : ℝ} (hell : 0 ≤ ell) (theta : ℝ) :
    -4 * (Real.cosh ((N : ℝ) * ell) - 1) ≤
      liRemoteQuartetProfile n ell theta := by
  simpa [abs_of_nonneg hell] using
    (liRemoteQuartetProfile_lower_bound hn ell theta)

/-- Exact phase alignment exposes a strictly negative transverse signal at every positive order. -/
theorem liRemoteQuartetProfile_neg_of_phase_aligned {n : ℕ} (hn : 1 ≤ n)
    {ell theta : ℝ} (hell : ell ≠ 0)
    (hphase : Real.cos ((n : ℝ) * theta) = 1) :
    liRemoteQuartetProfile n ell theta < 0 := by
  rw [liRemoteQuartetProfile, hphase, mul_one]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hne : (n : ℝ) * ell ≠ 0 := mul_ne_zero hn0 hell
  nlinarith [Real.one_lt_cosh.mpr hne]

end

end RHTower
