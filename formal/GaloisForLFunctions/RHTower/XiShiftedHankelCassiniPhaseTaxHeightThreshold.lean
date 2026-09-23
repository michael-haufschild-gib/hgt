import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniOneOrbitContactOrientation

/-!
# Phase-tax height threshold behind degree-one Cassini orientation

The sharp one-orbit contact law says that a positive real reciprocal atom stabilizes an
off-critical conjugate pair exactly when it lies above the pair's intrinsic velocity

`Re(lambda^(2 : ℕ)) / Re(lambda)`.

For a shifted squared-Xi denominator `A+iB`, this velocity is

`(A^(2 : ℕ)-B^(2 : ℕ))/(A(A^(2 : ℕ)+B^(2 : ℕ)))`.

A critical-line atom at height `eta` is `1/(y+eta^(2 : ℕ))`.  Comparing the two gives the exact height
threshold

`eta^(2 : ℕ) > (A-y) + 2 A B^(2 : ℕ)/(A^(2 : ℕ)-B^(2 : ℕ))`.

For an off-critical Xi zero with centered horizontal displacement `delta` and ordinate `gamma`,
`A-y=gamma^(2 : ℕ)-delta^(2 : ℕ)` and `B^(2 : ℕ)=4 delta^(2 : ℕ) gamma^(2 : ℕ)`.  The second summand is a strictly positive
phase tax.  Thus sector bounds alone lose the decisive order information: critical zeros below
the taxed height stabilize contact, while those above it drive the adverse orientation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Intrinsic radial velocity of a complex reciprocal pair. -/
def cassiniPairIntrinsicVelocity (lam : ℂ) : ℝ :=
  (lam ^ (2 : ℕ)).re / lam.re

/-- Positive reciprocal atom attached to a critical-line height at mass shift `y`. -/
def cassiniCriticalHeightAtom (y eta : ℝ) : ℝ :=
  (y + eta ^ (2 : ℕ))⁻¹

/-- Intrinsic velocity of the inverse of a denominator `A+iB`. -/
theorem cassiniPairIntrinsicVelocity_inv_cartesian
    {A B : ℝ} (hA : 0 < A) :
    cassiniPairIntrinsicVelocity (((A : ℂ) + (B : ℂ) * I)⁻¹) =
      (A ^ (2 : ℕ) - B ^ (2 : ℕ)) / (A * (A ^ (2 : ℕ) + B ^ (2 : ℕ))) := by
  have hden : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  rw [cassiniPairIntrinsicVelocity, pow_two, Complex.mul_re,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
  field_simp [hA.ne', hden.ne']

/-- Exact conversion from reciprocal radial order to the phase-tax height order. -/
theorem cassiniCriticalHeightAtom_lt_intrinsicVelocity_iff_phaseTax
    {y eta A B : ℝ} (hy : 0 < y) (hA : 0 < A) (hsector : B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    cassiniCriticalHeightAtom y eta <
        (A ^ (2 : ℕ) - B ^ (2 : ℕ)) / (A * (A ^ (2 : ℕ) + B ^ (2 : ℕ))) ↔
      A - y + 2 * A * B ^ (2 : ℕ) / (A ^ (2 : ℕ) - B ^ (2 : ℕ)) < eta ^ (2 : ℕ) := by
  have hyeta : 0 < y + eta ^ (2 : ℕ) := by nlinarith [sq_nonneg eta]
  have hgap : 0 < A ^ (2 : ℕ) - B ^ (2 : ℕ) := sub_pos.mpr hsector
  have hnorm : 0 < A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_pos hA, sq_nonneg B]
  rw [cassiniCriticalHeightAtom, inv_eq_one_div,
    div_lt_div_iff₀ hyeta (mul_pos hA hnorm)]
  constructor
  · intro h
    have hmul :
        2 * A * B ^ (2 : ℕ) < (A ^ (2 : ℕ) - B ^ (2 : ℕ)) * (eta ^ (2 : ℕ) - A + y) := by
      nlinarith
    have hdiv :
        2 * A * B ^ (2 : ℕ) / (A ^ (2 : ℕ) - B ^ (2 : ℕ)) < eta ^ (2 : ℕ) - A + y :=
      (div_lt_iff₀ hgap).2 (by simpa [mul_comm] using hmul)
    linarith
  · intro h
    have hdiv :
        2 * A * B ^ (2 : ℕ) / (A ^ (2 : ℕ) - B ^ (2 : ℕ)) < eta ^ (2 : ℕ) - A + y := by
      linarith
    have hmul := (div_lt_iff₀ hgap).1 hdiv
    nlinarith

/-- Intrinsic velocity of one actual shifted squared-Xi conjugate orbit. -/
def xiShiftedPairIntrinsicVelocity (y : ℝ) (q : XiZeroCopy) : ℝ :=
  cassiniPairIntrinsicVelocity (xiShiftedReciprocalSquare y q)

/-- Critical height separating stabilizing and adverse radial transport for an actual shifted Xi
orbit. -/
def xiShiftedPairPhaseTaxHeightSq (y : ℝ) (q : XiZeroCopy) : ℝ :=
  let delta := (q.1 : ℂ).re - 1 / 2
  let gamma := (q.1 : ℂ).im
  let A := y + gamma ^ (2 : ℕ) - delta ^ (2 : ℕ)
  gamma ^ (2 : ℕ) - delta ^ (2 : ℕ) +
    8 * A * delta ^ (2 : ℕ) * gamma ^ (2 : ℕ) /
      (A ^ (2 : ℕ) - 4 * delta ^ (2 : ℕ) * gamma ^ (2 : ℕ))

/-- The actual Xi denominator lies in the strict velocity sector at every positive shift. -/
theorem xiShiftedPair_denominator_phase_sector
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    let delta := (q.1 : ℂ).re - 1 / 2
    let gamma := (q.1 : ℂ).im
    let A := y + gamma ^ (2 : ℕ) - delta ^ (2 : ℕ)
    let B := -(2 * delta * gamma)
    0 < A ∧ B ^ (2 : ℕ) < A ^ (2 : ℕ) := by
  dsimp only
  let delta : ℝ := (q.1 : ℂ).re - 1 / 2
  let gamma : ℝ := (q.1 : ℂ).im
  let A : ℝ := y + gamma ^ (2 : ℕ) - delta ^ (2 : ℕ)
  let B : ℝ := -(2 * delta * gamma)
  have hdelta : delta ^ (2 : ℕ) < 1 / 4 := by
    simpa only [delta] using xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hgamma : 41 / 2 < gamma ^ (2 : ℕ) := by
    simpa only [gamma] using xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hgamma0 : 0 < gamma ^ (2 : ℕ) := by linarith
  have hA : 0 < A := by
    dsimp only [A]
    linarith
  have hB : B ^ (2 : ℕ) < gamma ^ (2 : ℕ) := by
    dsimp only [B]
    have hfour : 4 * delta ^ (2 : ℕ) < 1 := by linarith
    nlinarith
  have hgammaA : gamma ^ (2 : ℕ) < A ^ (2 : ℕ) := by
    have hAlarge : 20 < A := by
      dsimp only [A]
      linarith
    have hgamma_lt : gamma ^ (2 : ℕ) < A + 1 / 4 := by
      dsimp only [A]
      linarith
    nlinarith
  exact ⟨hA, hB.trans hgammaA⟩

/-- Exact actual-Xi phase-tax law.  A critical-line atom is adverse for this one-orbit contact
precisely when its squared height exceeds the off-critical orbit's taxed height. -/
theorem cassiniCriticalHeightAtom_lt_xiShiftedPairIntrinsicVelocity_iff
    {y eta : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    cassiniCriticalHeightAtom y eta < xiShiftedPairIntrinsicVelocity y q ↔
      xiShiftedPairPhaseTaxHeightSq y q < eta ^ (2 : ℕ) := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hsector : 0 < A ∧ B ^ (2 : ℕ) < A ^ (2 : ℕ) := by
    rcases xiShiftedPair_denominator_phase_sector hy q with ⟨hA, hB⟩
    constructor
    · dsimp only [A]
      rw [xiSquaredNode_re]
      linarith
    · dsimp only [A, B]
      rw [xiSquaredNode_re, xiSquaredNode_im]
      nlinarith
  have hcoord : (y : ℂ) + xiSquaredNode q =
      (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  have hvelocity :
      xiShiftedPairIntrinsicVelocity y q =
        (A ^ (2 : ℕ) - B ^ (2 : ℕ)) / (A * (A ^ (2 : ℕ) + B ^ (2 : ℕ))) := by
    rw [xiShiftedPairIntrinsicVelocity, xiShiftedReciprocalSquare_eq_inv hy.le,
      hcoord]
    exact cassiniPairIntrinsicVelocity_inv_cartesian hsector.1
  rw [hvelocity,
    cassiniCriticalHeightAtom_lt_intrinsicVelocity_iff_phaseTax
      hy hsector.1 hsector.2]
  unfold xiShiftedPairPhaseTaxHeightSq
  dsimp only [A, B]
  rw [xiSquaredNode_re, xiSquaredNode_im]
  ring

/-- The phase tax is strictly positive for every genuinely off-critical orbit. -/
theorem xiShiftedPair_phaseTax_pos_of_offCritical
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < xiShiftedPairPhaseTaxHeightSq y q -
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) := by
  let delta : ℝ := (q.1 : ℂ).re - 1 / 2
  let gamma : ℝ := (q.1 : ℂ).im
  let A : ℝ := y + gamma ^ (2 : ℕ) - delta ^ (2 : ℕ)
  let B : ℝ := -(2 * delta * gamma)
  have hsector := xiShiftedPair_denominator_phase_sector hy q
  change 0 < A ∧ B ^ (2 : ℕ) < A ^ (2 : ℕ) at hsector
  have hdelta : delta ≠ 0 := sub_ne_zero.mpr hoff
  have hgamma : 0 < gamma ^ (2 : ℕ) := by
    simpa only [gamma] using
      (lt_trans (by norm_num : (0 : ℝ) < 41 / 2)
        (xiZeroCopy_fortyOne_div_two_lt_im_sq q))
  have hnum : 0 < 8 * A * delta ^ (2 : ℕ) * gamma ^ (2 : ℕ) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) hsector.1) (sq_pos_of_ne_zero hdelta)) hgamma
  have hden : 0 < A ^ (2 : ℕ) - 4 * delta ^ (2 : ℕ) * gamma ^ (2 : ℕ) := by
    have hBsq : B ^ (2 : ℕ) = 4 * delta ^ (2 : ℕ) * gamma ^ (2 : ℕ) := by
      dsimp only [B]
      ring
    rw [← hBsq]
    exact sub_pos.mpr hsector.2
  unfold xiShiftedPairPhaseTaxHeightSq
  dsimp only [A, delta, gamma]
  rw [show (q.1 : ℂ).re - 1 / 2 = delta by rfl,
    show (q.1 : ℂ).im = gamma by rfl]
  have hquot := div_pos hnum hden
  linarith

end

end RHTower
