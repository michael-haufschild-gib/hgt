import GaloisForLFunctions.RHTower.SuzukiRelativeTiltReciprocalConcavity
import GaloisForLFunctions.RHTower.XiSquaredEulerApertureHilbertCorrelation

/-!
# Suzuki's safe-shift response/charge cancellation law

Suzuki's second disk-jet gate is the first Hankel minor of the multiplicity-exact reciprocal Xi
moments at the safe squared shift `y = 1`.  This module resolves that minor into two complete
infinite-divisor terms.

For the shifted reciprocal atom `λ_q(y)`, put

`a_q = Re λ_q`, `τ_q = Re(λ_q²) / a_q`,
`χ_q = Im(λ_q)² |λ_q|² / a_q`.

Then

`A C - B² = [A ∑ a_q τ_q² - (∑ a_q τ_q)²] - A ∑ χ_q`.

The bracket is a nonnegative Hilbert dispersion.  The transverse charge is nonnegative and its
zero radical is exactly RH.  Thus the finite Suzuki Schur wall can pass to the Xi target only when
cross-orbit response dispersion dominates the complete shifted transverse RH charge.

No RH assumption and no numerical computation occur in the decomposition.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Shifted orbit coordinates -/

/-- Positive oriented mass of one shifted reciprocal Xi atom. -/
def xiShiftedResponseMass (y : ℝ) (q : XiZeroCopy) : ℝ :=
  (xiShiftedReciprocalSquare y q).re

/-- Radial response slope of one shifted reciprocal Xi atom. -/
def xiShiftedResponseSlope (y : ℝ) (q : XiZeroCopy) : ℝ :=
  (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re /
    xiShiftedResponseMass y q

/-- Transverse charge density of one shifted reciprocal Xi atom. -/
def xiShiftedTransverseChargeDensity (y : ℝ) (q : XiZeroCopy) : ℝ :=
  (xiShiftedReciprocalSquare y q).im ^ (2 : ℕ) *
      Complex.normSq (xiShiftedReciprocalSquare y q) /
    xiShiftedResponseMass y q

theorem xiShiftedResponseMass_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < xiShiftedResponseMass y q := by
  simpa only [xiShiftedResponseMass, pow_one] using
    (re_xiShiftedReciprocalSquare_pow_pos hy q (m := 1) (by norm_num))

/-- Two-power positivity already gives the strict longitudinal/transverse sector needed for all
summability estimates below. -/
theorem xiShiftedReciprocalSquare_im_sq_lt_re_sq
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q).im ^ (2 : ℕ) <
      (xiShiftedReciprocalSquare y q).re ^ (2 : ℕ) := by
  have hsq :=
    re_xiShiftedReciprocalSquare_pow_pos hy q (m := 2) (by norm_num)
  rw [pow_two, Complex.mul_re] at hsq
  nlinarith

theorem xiShiftedResponseSlope_pos {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 < xiShiftedResponseSlope y q := by
  exact div_pos
    (re_xiShiftedReciprocalSquare_pow_pos hy q (m := 2) (by norm_num))
    (xiShiftedResponseMass_pos hy q)

theorem xiShiftedTransverseChargeDensity_nonneg
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 ≤ xiShiftedTransverseChargeDensity y q := by
  unfold xiShiftedTransverseChargeDensity
  exact div_nonneg
    (mul_nonneg (sq_nonneg _)
      (by
        rw [Complex.normSq_apply]
        exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)))
    (xiShiftedResponseMass_pos hy q).le

/-- The second response coefficient is mass times shifted slope. -/
theorem xiShiftedReciprocalSquare_sq_re_eq_mass_mul_slope
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re =
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q := by
  unfold xiShiftedResponseSlope
  field_simp [(xiShiftedResponseMass_pos hy q).ne']

/-- The third response coefficient is the positive slope square minus transverse charge. -/
theorem xiShiftedReciprocalSquare_cube_re_eq_mass_mul_slope_sq_sub_charge
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q ^ (3 : ℕ)).re =
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ) -
        xiShiftedTransverseChargeDensity y q := by
  let z := xiShiftedReciprocalSquare y q
  have hz : z.re ≠ 0 := (xiShiftedResponseMass_pos hy q).ne'
  unfold xiShiftedResponseMass xiShiftedResponseSlope
    xiShiftedTransverseChargeDensity
  change (z ^ (3 : ℕ)).re =
    z.re * ((z ^ (2 : ℕ)).re / z.re) ^ (2 : ℕ) -
      z.im ^ (2 : ℕ) * Complex.normSq z / z.re
  rw [show z ^ (3 : ℕ) = z * z * z by ring, show z ^ (2 : ℕ) = z * z by ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  field_simp [hz]
  ring

/-! ## Absolute summability of the complete shifted response/charge -/

private theorem summable_norm_xiShiftedReciprocalSquare_cube
    {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun q : XiZeroCopy => ‖xiShiftedReciprocalSquare y q‖ ^ (3 : ℕ)) := by
  simpa only [norm_pow] using
    (summable_xiShiftedReciprocalSquare_pow hy 2).norm

theorem summable_xiShiftedResponseMass {y : ℝ} (hy : 0 ≤ y) :
    Summable (xiShiftedResponseMass y) := by
  change Summable (fun q : XiZeroCopy => (xiShiftedReciprocalSquare y q).re)
  simpa using
    Complex.reCLM.summable (summable_xiShiftedReciprocalSquare_pow hy 0)

theorem summable_xiShiftedResponseMass_mul_slope
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q) := by
  have hsum :=
    Complex.reCLM.summable (summable_xiShiftedReciprocalSquare_pow hy.le 1)
  exact hsum.congr fun q =>
    xiShiftedReciprocalSquare_sq_re_eq_mass_mul_slope hy q

private theorem norm_mass_mul_slope_sq_le_cube
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    ‖xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)‖ ≤
      ‖xiShiftedReciprocalSquare y q‖ ^ (3 : ℕ) := by
  let z := xiShiftedReciprocalSquare y q
  have ha : 0 < z.re := xiShiftedResponseMass_pos hy q
  have hb : z.im ^ (2 : ℕ) < z.re ^ (2 : ℕ) :=
    xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q
  have hdiff0 : 0 ≤ z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ) := by linarith
  have hdiffle : z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ) ≤ z.re ^ (2 : ℕ) := by
    nlinarith [sq_nonneg z.im]
  have hsqle :
      (z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (z.re ^ (2 : ℕ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hdiff0 hdiffle 2
  have hdiv :
      (z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) ^ (2 : ℕ) / z.re ≤ z.re ^ (3 : ℕ) := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hrele : z.re ^ (3 : ℕ) ≤ ‖z‖ ^ (3 : ℕ) :=
    pow_le_pow_left₀ ha.le (Complex.re_le_norm z) 3
  have hterm :
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ) =
        (z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) ^ (2 : ℕ) / z.re := by
    unfold xiShiftedResponseMass xiShiftedResponseSlope
    change z.re * ((z ^ (2 : ℕ)).re / z.re) ^ (2 : ℕ) = _
    rw [show (z ^ (2 : ℕ)).re = z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ) by
      rw [pow_two, Complex.mul_re]
      ring]
    field_simp [ha.ne']
  rw [hterm, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha.le)]
  exact hdiv.trans hrele

theorem summable_xiShiftedResponseMass_mul_slope_sq
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)) := by
  exact Summable.of_norm_bounded
    (summable_norm_xiShiftedReciprocalSquare_cube hy.le)
    (norm_mass_mul_slope_sq_le_cube hy)

private theorem norm_transverseChargeDensity_le_two_mul_cube
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    ‖xiShiftedTransverseChargeDensity y q‖ ≤
      2 * ‖xiShiftedReciprocalSquare y q‖ ^ (3 : ℕ) := by
  let z := xiShiftedReciprocalSquare y q
  have ha : 0 < z.re := xiShiftedResponseMass_pos hy q
  have hb : z.im ^ (2 : ℕ) ≤ z.re ^ (2 : ℕ) :=
    (xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q).le
  have hnormSq : Complex.normSq z ≤ 2 * z.re ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    nlinarith
  have hprod :
      z.im ^ (2 : ℕ) * Complex.normSq z ≤ z.re ^ (2 : ℕ) * (2 * z.re ^ (2 : ℕ)) :=
    mul_le_mul hb hnormSq
      (by
        rw [Complex.normSq_apply]
        exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (sq_nonneg _)
  have hdiv :
      z.im ^ (2 : ℕ) * Complex.normSq z / z.re ≤ 2 * z.re ^ (3 : ℕ) := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hrele : 2 * z.re ^ (3 : ℕ) ≤ 2 * ‖z‖ ^ (3 : ℕ) := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ha.le (Complex.re_le_norm z) 3) (by norm_num)
  have hterm :
      xiShiftedTransverseChargeDensity y q =
        z.im ^ (2 : ℕ) * Complex.normSq z / z.re := rfl
  rw [hterm, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg
      (mul_nonneg (sq_nonneg _)
        (by
          rw [Complex.normSq_apply]
          exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))) ha.le)]
  exact hdiv.trans hrele

theorem summable_xiShiftedTransverseChargeDensity
    {y : ℝ} (hy : 0 < y) :
    Summable (xiShiftedTransverseChargeDensity y) := by
  exact Summable.of_norm_bounded
    ((summable_norm_xiShiftedReciprocalSquare_cube hy.le).mul_left 2)
    (norm_transverseChargeDensity_le_two_mul_cube hy)

/-! ## Complete moment and Hilbert identities -/

theorem tsum_xiShiftedResponseMass_eq_moment_re
    {y : ℝ} (hy : 0 ≤ y) :
    ∑' q : XiZeroCopy, xiShiftedResponseMass y q =
      (xiShiftedReciprocalMoment y 0).re := by
  rw [xiShiftedReciprocalMoment,
    Complex.re_tsum (summable_xiShiftedReciprocalSquare_pow hy 0)]
  simp [xiShiftedResponseMass]

theorem tsum_xiShiftedResponseMass_mul_slope_eq_moment_re
    {y : ℝ} (hy : 0 < y) :
    ∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q =
      (xiShiftedReciprocalMoment y 1).re := by
  calc
    ∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q =
        ∑' q : XiZeroCopy, (xiShiftedReciprocalSquare y q ^ (2 : ℕ)).re := by
          apply tsum_congr
          intro q
          exact (xiShiftedReciprocalSquare_sq_re_eq_mass_mul_slope hy q).symm
    _ = (xiShiftedReciprocalMoment y 1).re := by
      rw [xiShiftedReciprocalMoment,
        Complex.re_tsum (summable_xiShiftedReciprocalSquare_pow hy.le 1)]

theorem tsum_xiShiftedResponseSlopeSq_sub_charge_eq_moment_re
    {y : ℝ} (hy : 0 < y) :
    (∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)) -
      ∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q =
        (xiShiftedReciprocalMoment y 2).re := by
  rw [← (summable_xiShiftedResponseMass_mul_slope_sq hy).tsum_sub
    (summable_xiShiftedTransverseChargeDensity hy)]
  calc
    ∑' q : XiZeroCopy,
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ) -
          xiShiftedTransverseChargeDensity y q) =
        ∑' q : XiZeroCopy, (xiShiftedReciprocalSquare y q ^ (3 : ℕ)).re := by
          apply tsum_congr
          intro q
          exact
            (xiShiftedReciprocalSquare_cube_re_eq_mass_mul_slope_sq_sub_charge
              hy q).symm
    _ = (xiShiftedReciprocalMoment y 2).re := by
      rw [xiShiftedReciprocalMoment,
        Complex.re_tsum (summable_xiShiftedReciprocalSquare_pow hy.le 2)]

/-- Complete shifted Hilbert response dispersion. -/
def xiShiftedResponseHilbertDispersion (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 0).re *
      ∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ) -
    (xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ)

/-- Complete shifted transverse charge, with the same zeroth-moment normalization as the Hankel
minor. -/
def xiShiftedTransverseCharge (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 0).re *
    ∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q

/-- **Infinite-divisor response/charge cancellation.** -/
theorem xiShiftedHankelMinor_eq_hilbertDispersion_sub_transverseCharge
    {y : ℝ} (hy : 0 < y) :
    (xiShiftedReciprocalMoment y 0).re *
          (xiShiftedReciprocalMoment y 2).re -
        (xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ) =
      xiShiftedResponseHilbertDispersion y -
        xiShiftedTransverseCharge y := by
  rw [xiShiftedResponseHilbertDispersion, xiShiftedTransverseCharge,
    ← tsum_xiShiftedResponseSlopeSq_sub_charge_eq_moment_re hy]
  ring

/-- The complete Hilbert response term is genuinely nonnegative, not merely a named remainder. -/
theorem xiShiftedResponseHilbertDispersion_nonneg
    {y : ℝ} (hy : 0 < y) :
    0 ≤ xiShiftedResponseHilbertDispersion y := by
  let e : XiZeroCopy → ℝ := xiShiftedResponseMass y
  let x : XiZeroCopy → ℝ := xiShiftedResponseSlope y
  have hepos (q : XiZeroCopy) : 0 < e q :=
    xiShiftedResponseMass_pos hy q
  have hxpos (q : XiZeroCopy) : 0 < x q :=
    xiShiftedResponseSlope_pos hy q
  have hS0 : Summable e := summable_xiShiftedResponseMass hy.le
  have hS1 : Summable (fun q => x q * e q) := by
    have h := summable_xiShiftedResponseMass_mul_slope hy
    simpa only [e, x, mul_comm] using h
  have hS2 : Summable (fun q => x q ^ (2 : ℕ) * e q) := by
    have h := summable_xiShiftedResponseMass_mul_slope_sq hy
    simpa only [e, x, mul_comm] using h
  have hS0nn : 0 ≤ ∑' q, e q := tsum_nonneg fun q => (hepos q).le
  have hS1nn : 0 ≤ ∑' q, x q * e q :=
    tsum_nonneg fun q => mul_nonneg (hxpos q).le (hepos q).le
  have hS2nn : 0 ≤ ∑' q, x q ^ (2 : ℕ) * e q :=
    tsum_nonneg fun q =>
      mul_nonneg (sq_nonneg _) (hepos q).le
  have hbound : ∀ s : Finset XiZeroCopy,
      ∑ q ∈ s, x q * e q ≤
        Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) := by
    intro s
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun q => Real.sqrt (e q)) (fun q => x q * Real.sqrt (e q))
    have hprod : ∀ q,
        Real.sqrt (e q) * (x q * Real.sqrt (e q)) = x q * e q := by
      intro q
      calc
        Real.sqrt (e q) * (x q * Real.sqrt (e q)) =
            x q * (Real.sqrt (e q) * Real.sqrt (e q)) := by ring
        _ = x q * e q := by rw [Real.mul_self_sqrt (hepos q).le]
    have hsq1 : ∀ q, Real.sqrt (e q) ^ (2 : ℕ) = e q := fun q =>
      Real.sq_sqrt (hepos q).le
    have hsq2 : ∀ q,
        (x q * Real.sqrt (e q)) ^ (2 : ℕ) = x q ^ (2 : ℕ) * e q := by
      intro q
      rw [mul_pow, hsq1]
    rw [Finset.sum_congr rfl (fun q _ => hprod q),
      Finset.sum_congr rfl (fun q _ => hsq1 q),
      Finset.sum_congr rfl (fun q _ => hsq2 q)] at hcs
    have hle0 : ∑ q ∈ s, e q ≤ ∑' q, e q :=
      hS0.sum_le_tsum s (fun q _ => (hepos q).le)
    have hle2 : ∑ q ∈ s, x q ^ (2 : ℕ) * e q ≤ ∑' q, x q ^ (2 : ℕ) * e q :=
      hS2.sum_le_tsum s (fun q _ =>
        mul_nonneg (sq_nonneg _) (hepos q).le)
    have hnn : 0 ≤ ∑ q ∈ s, x q * e q :=
      Finset.sum_nonneg fun q _ => mul_nonneg (hxpos q).le (hepos q).le
    have hchain : (∑ q ∈ s, x q * e q) ^ (2 : ℕ) ≤
        (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q := by
      refine le_trans hcs ?_
      have h0nn : 0 ≤ ∑ q ∈ s, e q :=
        Finset.sum_nonneg fun q _ => (hepos q).le
      have h2nn : 0 ≤ ∑ q ∈ s, x q ^ (2 : ℕ) * e q :=
        Finset.sum_nonneg fun q _ =>
          mul_nonneg (sq_nonneg _) (hepos q).le
      nlinarith
    exact (Real.le_sqrt hnn (mul_nonneg hS0nn hS2nn)).mpr hchain
  have hS1le : (∑' q, x q * e q) ≤
      Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) :=
    hS1.tsum_le_of_sum_le hbound
  have hsq : (∑' q, x q * e q) ^ (2 : ℕ) ≤
      (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q := by
    calc
      (∑' q, x q * e q) ^ (2 : ℕ) ≤
          Real.sqrt ((∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q) ^ (2 : ℕ) := by
            exact pow_le_pow_left₀ hS1nn hS1le 2
      _ = (∑' q, e q) * ∑' q, x q ^ (2 : ℕ) * e q :=
        Real.sq_sqrt (mul_nonneg hS0nn hS2nn)
  rw [xiShiftedResponseHilbertDispersion,
    ← tsum_xiShiftedResponseMass_eq_moment_re hy.le,
    ← tsum_xiShiftedResponseMass_mul_slope_eq_moment_re hy]
  change 0 ≤ (∑' q, e q) *
      ∑' q, e q * x q ^ (2 : ℕ) - (∑' q, e q * x q) ^ (2 : ℕ)
  simpa only [mul_comm] using sub_nonneg.mpr hsq

theorem xiShiftedTransverseCharge_nonneg
    {y : ℝ} (hy : 0 < y) :
    0 ≤ xiShiftedTransverseCharge y := by
  rw [xiShiftedTransverseCharge]
  exact mul_nonneg
    (re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num)).le
    (tsum_nonneg fun q => xiShiftedTransverseChargeDensity_nonneg hy q)

/-! ## RH-exact transverse radical -/

theorem xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q).im = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [xiShiftedReciprocalSquare_im_eq_zero_iff hy.le,
    xiZeroCopyReciprocalSquare_eq,
    xiCentralReciprocalSquare_im_eq_zero_iff]

theorem xiShiftedTransverseChargeDensity_eq_zero_iff
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity y q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  let z := xiShiftedReciprocalSquare y q
  have ha : z.re ≠ 0 := (xiShiftedResponseMass_pos hy q).ne'
  have hnorm : Complex.normSq z ≠ 0 := by
    apply (Complex.normSq_pos.mpr ?_).ne'
    intro hzero
    have := xiShiftedResponseMass_pos hy q
    rw [show xiShiftedResponseMass y q = z.re by rfl, hzero, Complex.zero_re] at this
    exact lt_irrefl _ this
  rw [xiShiftedTransverseChargeDensity]
  constructor
  · intro h
    rcases (div_eq_zero_iff.mp h) with hnum | hden
    · rcases mul_eq_zero.mp hnum with himsq | hnormZero
      · exact (xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine hy q).mp
          (sq_eq_zero_iff.mp himsq)
      · exact False.elim (hnorm hnormZero)
    · exact False.elim (ha hden)
  · intro hline
    have him :=
      (xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine hy q).mpr hline
    rw [him, zero_pow, zero_mul, zero_div]
    norm_num

/-- **The complete shifted transverse charge has RH as its exact zero radical.** -/
theorem xiShiftedTransverseCharge_eq_zero_iff_riemannHypothesis
    {y : ℝ} (hy : 0 < y) :
    xiShiftedTransverseCharge y = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    have hA : 0 < (xiShiftedReciprocalMoment y 0).re :=
      re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num)
    have hsumZero :
        (∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q) = 0 := by
      rw [xiShiftedTransverseCharge] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hA.ne'
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      have hle :=
        (summable_xiShiftedTransverseChargeDensity hy).le_tsum q
          (fun r _ => xiShiftedTransverseChargeDensity_nonneg hy r)
      have hqnonneg := xiShiftedTransverseChargeDensity_nonneg hy q
      have hqzero : xiShiftedTransverseChargeDensity y q = 0 := by
        apply le_antisymm
        · simpa only [hsumZero] using hle
        · exact hqnonneg
      exact (xiShiftedTransverseChargeDensity_eq_zero_iff hy q).mp hqzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH
    rw [xiShiftedTransverseCharge]
    have hterm : ∀ q : XiZeroCopy,
        xiShiftedTransverseChargeDensity y q = 0 := by
      intro q
      apply (xiShiftedTransverseChargeDensity_eq_zero_iff hy q).mpr
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      have him := congrArg Complex.im ht
      simp [xiSpectralPoint] at him
      linarith
    simp_rw [hterm, tsum_zero, mul_zero]

/-! ## Suzuki safe-shift source specialization -/

/-- **Safe-shift source cancellation.**  Suzuki's exact source-only first Hankel minor is the
nonnegative shifted response dispersion minus the RH-complete transverse charge. -/
theorem primeArchSafeShiftHankelMinor_eq_hilbertDispersion_sub_transverseCharge :
    (primeArchShiftedReciprocalMoment 1 0).re *
          (primeArchShiftedReciprocalMoment 1 2).re -
        (primeArchShiftedReciprocalMoment 1 1).re ^ (2 : ℕ) =
      xiShiftedResponseHilbertDispersion 1 -
        xiShiftedTransverseCharge 1 := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 0,
    ← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1,
    ← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 2]
  exact xiShiftedHankelMinor_eq_hilbertDispersion_sub_transverseCharge
    (y := 1) (by norm_num)

/-- Suzuki's target two-jet wall is exactly domination of complete shifted transverse charge by
cross-orbit shifted response dispersion. -/
theorem primeArchSafeShiftHankelMinor_nonneg_iff_transverseCharge_le_dispersion :
    0 ≤
        (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re -
          (primeArchShiftedReciprocalMoment 1 1).re ^ (2 : ℕ) ↔
      xiShiftedTransverseCharge 1 ≤
        xiShiftedResponseHilbertDispersion 1 := by
  rw [primeArchSafeShiftHankelMinor_eq_hilbertDispersion_sub_transverseCharge]
  exact sub_nonneg

end

end RHTower
