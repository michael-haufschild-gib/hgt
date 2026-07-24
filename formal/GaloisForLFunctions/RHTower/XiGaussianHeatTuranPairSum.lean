import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder

/-!
# The Turán minor as a pair sum, and its exact negative core

Writing `w q = xiSpectralPoint q ^ 2` and `E t q = exp (-t * w q)`, the second Hankel minor of the
Gaussian-damped moments has the variance form

`2 (M0 M2 - M1^2) = sum_(q,q') (w q - w q')^2 * E t q * E t q'`.

Every ordered pair of copies with a **common real part** contributes a nonpositive real number,
because the difference of two points on one vertical line is purely imaginary.  The extreme case is
a copy paired with its own critical-line conjugate, where the contribution is computed exactly:

`(w q - conj (w q))^2 * E t q * E t (lineConj q) = -4 (Im (w q))^2 * exp (-2 t Re (w q))`.

This is the negative signal of an off-critical zero inside the Turán minor, isolated with no
estimate: it is a closed-form term of the pair expansion, strictly negative exactly when the copy
is off the critical line, and exponentially graded by the shell coordinate `Re (w q)`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One ordered pair of the variance expansion of the Turán minor. -/
def xiHeatPairTerm (t : ℝ) (z : XiZeroCopy × XiZeroCopy) : ℂ :=
  (xiSpectralPoint z.1 ^ 2 - xiSpectralPoint z.2 ^ 2) ^ 2 *
    (xiGaussianHeatTerm t z.1 * xiGaussianHeatTerm t z.2)

/-- Absolute summability of the monomial heat families. -/
theorem summable_norm_xiGaussianHeatMonomialTerm {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ‖(xiSpectralPoint q ^ 2) ^ j * xiGaussianHeatTerm t q‖) :=
  summable_norm_iff.mpr (summable_xiGaussianHeatMonomialTerm ht j)

/-- The pair family of the variance expansion is summable. -/
theorem summable_xiHeatPairTerm {t : ℝ} (ht : 0 < t) :
    Summable (xiHeatPairTerm t) := by
  have h0 := summable_norm_xiGaussianHeatMonomialTerm ht 0
  have h1 := summable_norm_xiGaussianHeatMonomialTerm ht 1
  have h2 := summable_norm_xiGaussianHeatMonomialTerm ht 2
  have hA := summable_mul_of_summable_norm h2 h0
  have hB := summable_mul_of_summable_norm h1 h1
  have hC := summable_mul_of_summable_norm h0 h2
  refine ((hA.sub (hB.mul_left 2)).add hC).congr fun z => ?_
  rw [xiHeatPairTerm]
  simp only [pow_zero, one_mul, pow_one]
  ring

/-- **The variance expansion of the Turán minor.**  Twice the second Hankel minor is the sum of the
squared differences over all ordered pairs of divisor copies. -/
theorem two_mul_xiHeatTuranMinor_eq_tsum_pair {t : ℝ} (ht : 0 < t) :
    2 * (xiGaussianHeatMoment 0 t * xiGaussianHeatMoment 2 t -
        xiGaussianHeatMoment 1 t ^ 2) =
      ∑' z : XiZeroCopy × XiZeroCopy, xiHeatPairTerm t z := by
  have h0 := summable_norm_xiGaussianHeatMonomialTerm ht 0
  have h1 := summable_norm_xiGaussianHeatMonomialTerm ht 1
  have h2 := summable_norm_xiGaussianHeatMonomialTerm ht 2
  have hA := tsum_mul_tsum_of_summable_norm h2 h0
  have hB := tsum_mul_tsum_of_summable_norm h1 h1
  have hC := tsum_mul_tsum_of_summable_norm h0 h2
  have hsumA := summable_mul_of_summable_norm h2 h0
  have hsumB := summable_mul_of_summable_norm h1 h1
  have hsumC := summable_mul_of_summable_norm h0 h2
  have hpt : ∀ z : XiZeroCopy × XiZeroCopy, xiHeatPairTerm t z =
      (((xiSpectralPoint z.1 ^ 2) ^ 2 * xiGaussianHeatTerm t z.1) *
          ((xiSpectralPoint z.2 ^ 2) ^ 0 * xiGaussianHeatTerm t z.2) -
        2 * (((xiSpectralPoint z.1 ^ 2) ^ 1 * xiGaussianHeatTerm t z.1) *
          ((xiSpectralPoint z.2 ^ 2) ^ 1 * xiGaussianHeatTerm t z.2))) +
        ((xiSpectralPoint z.1 ^ 2) ^ 0 * xiGaussianHeatTerm t z.1) *
          ((xiSpectralPoint z.2 ^ 2) ^ 2 * xiGaussianHeatTerm t z.2) := by
    intro z
    rw [xiHeatPairTerm]
    simp only [pow_zero, one_mul, pow_one]
    ring
  rw [xiGaussianHeatMoment, xiGaussianHeatMoment, xiGaussianHeatMoment,
    tsum_congr hpt, (hsumA.sub (hsumB.mul_left 2)).tsum_add hsumC,
    hsumA.tsum_sub (hsumB.mul_left 2), tsum_mul_left, ← hA, ← hB, ← hC]
  ring

/-! ## The exact negative core -/

/-- The line conjugate of a copy conjugates its squared spectral point. -/
theorem xiSpectralSq_lineConj (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyLineConjEquiv q) ^ 2 =
      (starRingEnd ℂ) (xiSpectralPoint q ^ 2) := by
  rw [xiSpectralPoint_lineConj, ← map_pow]

/-- **The exact negative core of the Turán minor.**  Pairing a copy with its critical-line
conjugate contributes the closed-form real number `-4 (Im w)^2 exp (-2 t Re w)`: strictly negative
exactly when the copy is off the critical line, and graded by the shell coordinate. -/
theorem xiHeatPairTerm_lineConj (t : ℝ) (q : XiZeroCopy) :
    xiHeatPairTerm t (q, xiZeroCopyLineConjEquiv q) =
      (((-4 * (xiSpectralPoint q ^ 2).im ^ 2 *
        Real.exp (-(2 * t * (xiSpectralPoint q ^ 2).re))) : ℝ) : ℂ) := by
  have hsq : (xiSpectralPoint q ^ 2 -
      xiSpectralPoint (xiZeroCopyLineConjEquiv q) ^ 2) ^ 2 =
      (((-4 * (xiSpectralPoint q ^ 2).im ^ 2) : ℝ) : ℂ) := by
    rw [xiSpectralSq_lineConj, Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hheat : xiGaussianHeatTerm t q *
      xiGaussianHeatTerm t (xiZeroCopyLineConjEquiv q) =
      ((Real.exp (-(2 * t * (xiSpectralPoint q ^ 2).re)) : ℝ) : ℂ) := by
    rw [xiGaussianHeatTerm, xiGaussianHeatTerm, ← Complex.exp_add, xiSpectralSq_lineConj,
      ← mul_add, Complex.add_conj]
    have hsum : -(t : ℂ) * ((2 * (xiSpectralPoint q ^ 2).re : ℝ) : ℂ) =
        ((-(2 * t * (xiSpectralPoint q ^ 2).re) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsum, ← Complex.ofReal_exp]
  rw [xiHeatPairTerm, hsq, hheat, ← Complex.ofReal_mul]

/-- The negative core is strictly negative exactly at an off-critical copy. -/
theorem xiHeatPairTerm_lineConj_neg_of_im_ne_zero {t : ℝ} {q : XiZeroCopy}
    (h : (xiSpectralPoint q ^ 2).im ≠ 0) :
    (xiHeatPairTerm t (q, xiZeroCopyLineConjEquiv q)).re < 0 := by
  rw [xiHeatPairTerm_lineConj, Complex.ofReal_re]
  have hsq : 0 < (xiSpectralPoint q ^ 2).im ^ 2 := by positivity
  have hexp : 0 < Real.exp (-(2 * t * (xiSpectralPoint q ^ 2).re)) := Real.exp_pos _
  nlinarith

/-- The pair sum is real, so it computes twice the Turán minor. -/
theorem two_mul_xiHeatTuranDefect_eq_re_tsum_pair {t : ℝ} (ht : 0 < t) :
    2 * xiHeatTuranDefect t =
      (∑' z : XiZeroCopy × XiZeroCopy, xiHeatPairTerm t z).re := by
  have him : ∀ n : ℕ, (xiGaussianHeatMoment n t).im = 0 := fun n =>
    Complex.conj_eq_iff_im.mp (star_xiGaussianHeatMoment n t)
  rw [← two_mul_xiHeatTuranMinor_eq_tsum_pair ht, xiHeatTuranDefect,
    xiGaussianHeatMomentReal, xiGaussianHeatMomentReal, xiGaussianHeatMomentReal]
  simp only [Complex.mul_re, Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat,
    pow_two, him, mul_zero, zero_mul, sub_zero]


/-! ## Tail primitives for the pair sum -/

/-- The norm of a pair term: squared separation of the two shell points times the Gaussian damping
at their combined shell coordinate. -/
theorem norm_xiHeatPairTerm (t : ℝ) (z : XiZeroCopy × XiZeroCopy) :
    ‖xiHeatPairTerm t z‖ =
      ‖xiSpectralPoint z.1 ^ 2 - xiSpectralPoint z.2 ^ 2‖ ^ 2 *
        Real.exp (-(t * ((xiSpectralPoint z.1 ^ 2).re +
          (xiSpectralPoint z.2 ^ 2).re))) := by
  rw [xiHeatPairTerm, norm_mul, norm_pow, norm_mul, xiGaussianHeatTerm,
    xiGaussianHeatTerm, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **Damping transfer for the pair sum.**  Beyond a reference time the pair term decays at least
like the exponential of its combined shell coordinate, so a lower bound on that coordinate turns
into a uniform exponential factor. -/
theorem norm_xiHeatPairTerm_le_of_le {t₁ t m : ℝ} (ht : t₁ ≤ t)
    {z : XiZeroCopy × XiZeroCopy}
    (hm : m ≤ (xiSpectralPoint z.1 ^ 2).re + (xiSpectralPoint z.2 ^ 2).re) :
    ‖xiHeatPairTerm t z‖ ≤
      ‖xiHeatPairTerm t₁ z‖ * Real.exp (-((t - t₁) * m)) := by
  rw [norm_xiHeatPairTerm, norm_xiHeatPairTerm]
  set S : ℝ := (xiSpectralPoint z.1 ^ 2).re + (xiSpectralPoint z.2 ^ 2).re with hS
  set N : ℝ := ‖xiSpectralPoint z.1 ^ 2 - xiSpectralPoint z.2 ^ 2‖ ^ 2 with hN
  have hNnn : 0 ≤ N := by positivity
  have hexp : Real.exp (-(t * S)) ≤
      Real.exp (-(t₁ * S)) * Real.exp (-((t - t₁) * m)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [ht, hm]
  calc
    N * Real.exp (-(t * S))
        ≤ N * (Real.exp (-(t₁ * S)) * Real.exp (-((t - t₁) * m))) :=
          mul_le_mul_of_nonneg_left hexp hNnn
    _ = N * Real.exp (-(t₁ * S)) * Real.exp (-((t - t₁) * m)) := by ring

end

end RHTower
