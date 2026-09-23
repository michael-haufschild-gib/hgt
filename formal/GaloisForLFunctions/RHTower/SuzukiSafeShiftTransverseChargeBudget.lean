import GaloisForLFunctions.RHTower.SuzukiSafeShiftResponseChargeCancellation
import GaloisForLFunctions.RHTower.XiThermalQuartetCubicChargeBound
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction

/-!
# Quantitative transverse-charge budget at Suzuki's safe shift

The response/charge decomposition leaves Suzuki's first nonlinear target wall in the form

`safe minor = response dispersion - shifted transverse charge`.

This file makes the charge side quantitatively source-controlled.  Write the squared centered
Xi node as `N = A + iB`.  The endpoint height gap gives `A > 81/4`, while the safe shifted atom
is `(1 + N)⁻¹`.  Two pointwise consequences follow:

* safe shifting decreases the positive response mass;
* its transverse charge density is at most `4/85` of the central orientation density.

After summation,

`Q₁ ≤ (4/85) μ₀ E`,

where `μ₀` is the zeroth prime--Gamma moment and `E` is the complete central orientation energy.
The exact cubic endpoint estimate then gives a source-dependent cap and, finally, the absolute
rational bound

`Q₁ < 116 / 7_968_750_000`.

No Riemann-hypothesis assumption and no numerical computation occur.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Pointwise safe-shift damping -/

/-- Safe shifting strictly decreases each positive reciprocal-square response mass. -/
theorem xiShiftedResponseMass_one_lt_xiThermalNode (q : XiZeroCopy) :
    xiShiftedResponseMass 1 q < xiThermalNode q := by
  let A : ℝ := 1 + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  let D₀ : ℝ := (A - 1) ^ (2 : ℕ) + B ^ (2 : ℕ)
  let D₁ : ℝ := A ^ (2 : ℕ) + B ^ (2 : ℕ)
  have hnode : 81 / 4 < (xiSquaredNode q).re := by
    rw [xiSquaredNode_re]
    have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
    linarith
  have hA : 85 / 4 < A := by
    dsimp only [A]
    linarith
  have hA₀ : 0 < A - 1 := by linarith
  have hD₀ : 0 < D₀ := by
    dsimp only [D₀]
    nlinarith [sq_pos_of_pos hA₀, sq_nonneg B]
  have hD₁ : 0 < D₁ := by
    dsimp only [D₁]
    nlinarith [sq_pos_of_pos (by linarith : 0 < A), sq_nonneg B]
  have hcoord₀ :
      xiSquaredNode q = (((A - 1 : ℝ) : ℂ) + (B : ℂ) * I) := by
    apply Complex.ext <;> simp [A, B]
  have hcoord₁ :
      (((1 : ℝ) : ℂ) + xiSquaredNode q) = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  have hmassShift :
      xiShiftedResponseMass 1 q = A / D₁ := by
    rw [xiShiftedResponseMass, xiShiftedReciprocalSquare_eq_inv (by norm_num),
      hcoord₁, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    simp only [D₁, pow_two]
  have hmassCentral :
      xiThermalNode q = (A - 1) / D₀ := by
    rw [xiThermalNode, xiZeroCopyReciprocalSquare_eq_inv_node, hcoord₀,
      Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    simp only [D₀, pow_two]
  have hsector :
      84 * B ^ (2 : ℕ) < A ^ (2 : ℕ) := by
    simpa only [A, B] using
      (eightyFour_mul_xiSquaredNode_im_sq_lt (y := 1) (by norm_num) q)
  have hscale : A ^ (2 : ℕ) < 84 * (A * (A - 1)) := by
    have : 84 < 83 * A := by nlinarith
    nlinarith
  have htransverse : B ^ (2 : ℕ) < A * (A - 1) := by
    nlinarith
  rw [hmassShift, hmassCentral, div_lt_div_iff₀ hD₁ hD₀]
  dsimp only [D₀, D₁]
  nlinarith

/-- The safe-shift transverse charge density is at most `4/85` of the central orientation
density.  The factor is forced by `Re (1 + N) > 85/4`; the shifted denominator supplies an
additional strict damping which is not spent in the stated bound. -/
theorem xiShiftedTransverseChargeDensity_one_le_four_div_eightyFive_mul_orientation
    (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity 1 q ≤
      (4 / 85 : ℝ) * (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) := by
  let A : ℝ := 1 + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  let D₀ : ℝ := (A - 1) ^ (2 : ℕ) + B ^ (2 : ℕ)
  let D₁ : ℝ := A ^ (2 : ℕ) + B ^ (2 : ℕ)
  have hnode : 81 / 4 < (xiSquaredNode q).re := by
    rw [xiSquaredNode_re]
    have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
    linarith
  have hA : 85 / 4 < A := by
    dsimp only [A]
    linarith
  have hApos : 0 < A := by linarith
  have hA₀ : 0 < A - 1 := by linarith
  have hD₀ : 0 < D₀ := by
    dsimp only [D₀]
    nlinarith [sq_pos_of_pos hA₀, sq_nonneg B]
  have hD₁ : 0 < D₁ := by
    dsimp only [D₁]
    nlinarith [sq_pos_of_pos hApos, sq_nonneg B]
  have hD : D₀ < D₁ := by
    dsimp only [D₀, D₁]
    nlinarith
  have hcoord₀ :
      xiSquaredNode q = (((A - 1 : ℝ) : ℂ) + (B : ℂ) * I) := by
    apply Complex.ext <;> simp [A, B]
  have hcoord₁ :
      (((1 : ℝ) : ℂ) + xiSquaredNode q) = (A : ℂ) + (B : ℂ) * I := by
    apply Complex.ext <;> simp [A, B]
  have hnormBase :
      Complex.normSq ((A : ℂ) + (B : ℂ) * I) = D₁ := by
    simp [Complex.normSq_apply, D₁, pow_two]
  have hnormShift :
      Complex.normSq (((A : ℂ) + (B : ℂ) * I)⁻¹) = 1 / D₁ := by
    rw [Complex.normSq_apply, Complex.inv_re, Complex.inv_im, hnormBase]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    dsimp only [D₁]
    field_simp [hD₁.ne']
  have hcharge :
      xiShiftedTransverseChargeDensity 1 q =
        B ^ (2 : ℕ) / (A * D₁ ^ (2 : ℕ)) := by
    rw [xiShiftedTransverseChargeDensity, xiShiftedResponseMass,
      xiShiftedReciprocalSquare_eq_inv (by norm_num), hcoord₁,
      hnormShift, Complex.inv_re, Complex.inv_im, hnormBase]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    dsimp only [D₁]
    field_simp [hApos.ne', hD₁.ne']
  have horientation :
      (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) =
        B ^ (2 : ℕ) / D₀ ^ (2 : ℕ) := by
    rw [xiZeroCopyReciprocalSquare_eq_inv_node, hcoord₀, Complex.inv_im,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, mul_one, add_zero, zero_add]
    dsimp only [D₀]
    field_simp [hD₀.ne']
  have hden₀ : 0 < A * D₀ ^ (2 : ℕ) := mul_pos hApos (sq_pos_of_pos hD₀)
  have hden₁ : 0 < A * D₁ ^ (2 : ℕ) := mul_pos hApos (sq_pos_of_pos hD₁)
  have hstep :
      B ^ (2 : ℕ) / (A * D₁ ^ (2 : ℕ)) ≤ B ^ (2 : ℕ) / (A * D₀ ^ (2 : ℕ)) := by
    rw [div_le_div_iff₀ hden₁ hden₀]
    have hDsq : D₀ ^ (2 : ℕ) ≤ D₁ ^ (2 : ℕ) :=
      pow_le_pow_left₀ hD₀.le hD.le 2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hDsq hApos.le) (sq_nonneg B)
  have hcoef : 1 / A ≤ (4 / 85 : ℝ) := by
    rw [div_le_iff₀ hApos]
    nlinarith
  rw [hcharge, horientation]
  calc
    B ^ (2 : ℕ) / (A * D₁ ^ (2 : ℕ)) ≤ B ^ (2 : ℕ) / (A * D₀ ^ (2 : ℕ)) := hstep
    _ = (1 / A) * (B ^ (2 : ℕ) / D₀ ^ (2 : ℕ)) := by
      field_simp [hApos.ne', hD₀.ne']
    _ ≤ (4 / 85 : ℝ) * (B ^ (2 : ℕ) / D₀ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcoef (div_nonneg (sq_nonneg B) (sq_nonneg D₀))

/-! ## Strict response dispersion -/

/-- Mass-normalized mean of the positive shifted response slopes. -/
def xiShiftedResponseMeanSlope (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 1).re /
    (xiShiftedReciprocalMoment y 0).re

/-- Every positive shifted response slope is bounded by the norm of its reciprocal atom. -/
theorem xiShiftedResponseSlope_le_norm
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiShiftedResponseSlope y q ≤ ‖xiShiftedReciprocalSquare y q‖ := by
  let z := xiShiftedReciprocalSquare y q
  have hzre : 0 < z.re := by
    simpa only [z, xiShiftedResponseMass] using
      xiShiftedResponseMass_pos hy q
  have hslope :
      xiShiftedResponseSlope y q =
        (z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) / z.re := by
    rw [xiShiftedResponseSlope, xiShiftedResponseMass]
    change (z ^ (2 : ℕ)).re / z.re = _
    rw [pow_two, Complex.mul_re]
    ring
  rw [hslope]
  calc
    (z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) / z.re ≤ z.re := by
      rw [div_le_iff₀ hzre]
      nlinarith [sq_nonneg z.im]
    _ ≤ ‖z‖ := Complex.re_le_norm z

/-- Shifted response slopes vanish cofinally because the reciprocal-square atoms do. -/
theorem tendsto_xiShiftedResponseSlope_cofinite_zero
    {y : ℝ} (hy : 0 < y) :
    Filter.Tendsto (xiShiftedResponseSlope y) Filter.cofinite (nhds 0) := by
  have hnorm :
      Filter.Tendsto (fun q : XiZeroCopy => ‖xiShiftedReciprocalSquare y q‖)
        Filter.cofinite (nhds 0) := by
    simpa using
      (summable_xiShiftedReciprocalSquare_pow hy.le 0).tendsto_cofinite_zero.norm
  exact squeeze_zero
    (fun q => (xiShiftedResponseSlope_pos hy q).le)
    (fun q => xiShiftedResponseSlope_le_norm hy q)
    hnorm

/-- Complete Xi support supplies two distinct shifted response slopes. -/
theorem exists_xiShiftedResponseSlope_ne
    {y : ℝ} (hy : 0 < y) :
    ∃ q r : XiZeroCopy,
      xiShiftedResponseSlope y q ≠ xiShiftedResponseSlope y r := by
  let q₀ : XiZeroCopy := Classical.choice inferInstance
  have hslope₀ : 0 < xiShiftedResponseSlope y q₀ :=
    xiShiftedResponseSlope_pos hy q₀
  have hsmall : ∀ᶠ q : XiZeroCopy in Filter.cofinite,
      xiShiftedResponseSlope y q < xiShiftedResponseSlope y q₀ / 2 :=
    (tendsto_xiShiftedResponseSlope_cofinite_zero hy).eventually_lt_const
      (by linarith)
  obtain ⟨q₁, hq₁⟩ := Filter.Eventually.exists hsmall
  refine ⟨q₀, q₁, ?_⟩
  linarith

/-- Centered shifted-slope energy is absolutely summable. -/
theorem summable_xiShiftedResponseMass_mul_centeredSlopeSq
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q *
        (xiShiftedResponseSlope y q -
          xiShiftedResponseMeanSlope y) ^ (2 : ℕ)) := by
  let e : XiZeroCopy → ℝ := xiShiftedResponseMass y
  let x : XiZeroCopy → ℝ := xiShiftedResponseSlope y
  let μ : ℝ := xiShiftedResponseMeanSlope y
  have hS₀ : Summable e := summable_xiShiftedResponseMass hy.le
  have hS₁ : Summable (fun q => e q * x q) := by
    simpa only [e, x] using
      summable_xiShiftedResponseMass_mul_slope hy
  have hS₂ : Summable (fun q => e q * x q ^ (2 : ℕ)) := by
    simpa only [e, x] using
      summable_xiShiftedResponseMass_mul_slope_sq hy
  have hexpand :
      (fun q => e q * (x q - μ) ^ (2 : ℕ)) =
        fun q => e q * x q ^ (2 : ℕ) + (-2 * μ) * (e q * x q) + μ ^ (2 : ℕ) * e q := by
    funext q
    ring
  rw [show (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q *
        (xiShiftedResponseSlope y q -
          xiShiftedResponseMeanSlope y) ^ (2 : ℕ)) =
      fun q => e q * (x q - μ) ^ (2 : ℕ) by rfl, hexpand]
  exact (hS₂.add (hS₁.mul_left (-2 * μ))).add (hS₀.mul_left (μ ^ (2 : ℕ)))

/-- Hilbert response dispersion is total mass times centered slope energy. -/
theorem xiShiftedResponseHilbertDispersion_eq_centeredSlopeEnergy
    {y : ℝ} (hy : 0 < y) :
    xiShiftedResponseHilbertDispersion y =
      (xiShiftedReciprocalMoment y 0).re *
        ∑' q : XiZeroCopy,
          xiShiftedResponseMass y q *
            (xiShiftedResponseSlope y q -
              xiShiftedResponseMeanSlope y) ^ (2 : ℕ) := by
  let e : XiZeroCopy → ℝ := xiShiftedResponseMass y
  let x : XiZeroCopy → ℝ := xiShiftedResponseSlope y
  let μ : ℝ := xiShiftedResponseMeanSlope y
  have hS₀ : Summable e := summable_xiShiftedResponseMass hy.le
  have hS₁ : Summable (fun q => e q * x q) := by
    simpa only [e, x] using
      summable_xiShiftedResponseMass_mul_slope hy
  have hS₂ : Summable (fun q => e q * x q ^ (2 : ℕ)) := by
    simpa only [e, x] using
      summable_xiShiftedResponseMass_mul_slope_sq hy
  have hcenter :
      (∑' q : XiZeroCopy, e q * (x q - μ) ^ (2 : ℕ)) =
        (∑' q : XiZeroCopy, e q * x q ^ (2 : ℕ)) +
          (-2 * μ) * (∑' q : XiZeroCopy, e q * x q) +
          μ ^ (2 : ℕ) * (∑' q : XiZeroCopy, e q) := by
    calc
      (∑' q : XiZeroCopy, e q * (x q - μ) ^ (2 : ℕ)) =
          ∑' q : XiZeroCopy, (
            (e q * x q ^ (2 : ℕ) + (-2 * μ) * (e q * x q)) +
              μ ^ (2 : ℕ) * e q) := by
            apply tsum_congr
            intro q
            ring
      _ = (∑' q : XiZeroCopy, e q * x q ^ (2 : ℕ)) +
          (-2 * μ) * (∑' q : XiZeroCopy, e q * x q) +
          μ ^ (2 : ℕ) * (∑' q : XiZeroCopy, e q) := by
            rw [(hS₂.add (hS₁.mul_left (-2 * μ))).tsum_add
                (hS₀.mul_left (μ ^ (2 : ℕ))),
              hS₂.tsum_add (hS₁.mul_left (-2 * μ)),
              tsum_mul_left, tsum_mul_left]
  have hA :
      (xiShiftedReciprocalMoment y 0).re ≠ 0 :=
    (re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num)).ne'
  dsimp only [e, x, μ] at hcenter
  rw [xiShiftedResponseHilbertDispersion,
    show (∑' q : XiZeroCopy,
      xiShiftedResponseMass y q *
        (xiShiftedResponseSlope y q -
          xiShiftedResponseMeanSlope y) ^ (2 : ℕ)) =
      ∑' q : XiZeroCopy, e q * (x q - μ) ^ (2 : ℕ) by rfl,
    hcenter,
    tsum_xiShiftedResponseMass_eq_moment_re hy.le,
    tsum_xiShiftedResponseMass_mul_slope_eq_moment_re hy]
  change
    (xiShiftedReciprocalMoment y 0).re *
          (∑' q : XiZeroCopy,
            xiShiftedResponseMass y q *
              xiShiftedResponseSlope y q ^ (2 : ℕ)) -
        (xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ) =
      (xiShiftedReciprocalMoment y 0).re *
        ((∑' q : XiZeroCopy,
            xiShiftedResponseMass y q *
              xiShiftedResponseSlope y q ^ (2 : ℕ)) +
          (-2 * xiShiftedResponseMeanSlope y) *
            (xiShiftedReciprocalMoment y 1).re +
          xiShiftedResponseMeanSlope y ^ (2 : ℕ) *
            (xiShiftedReciprocalMoment y 0).re)
  rw [xiShiftedResponseMeanSlope]
  field_simp [hA]
  ring

/-- **Strict dispersion law.**  Infinite Xi support forces nonconstant shifted response slopes,
so Suzuki's Hilbert response term is strictly positive at every positive shift. -/
theorem xiShiftedResponseHilbertDispersion_pos
    {y : ℝ} (hy : 0 < y) :
    0 < xiShiftedResponseHilbertDispersion y := by
  obtain ⟨q, r, hqr⟩ := exists_xiShiftedResponseSlope_ne hy
  let μ : ℝ := xiShiftedResponseMeanSlope y
  obtain ⟨q₀, hq₀⟩ :
      ∃ q₀ : XiZeroCopy, xiShiftedResponseSlope y q₀ ≠ μ := by
    by_cases hq : xiShiftedResponseSlope y q = μ
    · refine ⟨r, ?_⟩
      intro hr
      exact hqr (hq.trans hr.symm)
    · exact ⟨q, hq⟩
  have hsumPos :
      0 < ∑' p : XiZeroCopy,
        xiShiftedResponseMass y p *
          (xiShiftedResponseSlope y p - μ) ^ (2 : ℕ) := by
    have hsum :
        Summable (fun p : XiZeroCopy =>
          xiShiftedResponseMass y p *
            (xiShiftedResponseSlope y p - μ) ^ (2 : ℕ)) := by
      simpa only [μ] using
        summable_xiShiftedResponseMass_mul_centeredSlopeSq hy
    exact hsum.tsum_pos
      (fun p => mul_nonneg (xiShiftedResponseMass_pos hy p).le (sq_nonneg _))
      q₀
      (mul_pos (xiShiftedResponseMass_pos hy q₀)
        (sq_pos_of_ne_zero (sub_ne_zero.mpr hq₀)))
  have hmass :
      0 < (xiShiftedReciprocalMoment y 0).re :=
    re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num)
  rw [xiShiftedResponseHilbertDispersion_eq_centeredSlopeEnergy hy]
  exact mul_pos hmass (by simpa only [μ] using hsumPos)

/-! ## Complete source budgets -/

/-- Total safe-shift response mass is bounded by the central zeroth prime--Gamma moment. -/
theorem re_xiShiftedReciprocalMoment_one_zero_le_normalizedPrimeArchMoment_zero :
    (xiShiftedReciprocalMoment 1 0).re ≤ normalizedPrimeArchMoment 0 := by
  rw [← tsum_xiShiftedResponseMass_eq_moment_re (y := 1) (by norm_num),
    ← xiThermalPositiveMoment_zero_eq_source]
  simp only [xiThermalPositiveMoment, zero_add, pow_one]
  exact (summable_xiShiftedResponseMass (y := 1) (by norm_num)).tsum_le_tsum
    (fun q => (xiShiftedResponseMass_one_lt_xiThermalNode q).le)
    (by simpa using summable_xiThermalNode_pow 0)

/-- Complete safe-shift charge density is bounded by `4/85` of the central orientation energy. -/
theorem tsum_xiShiftedTransverseChargeDensity_one_le_orientationEnergy :
    (∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity 1 q) ≤
      (4 / 85 : ℝ) * xiThermalOrientationEnergy := by
  rw [xiThermalOrientationEnergy, ← tsum_mul_left]
  exact (summable_xiShiftedTransverseChargeDensity (y := 1) (by norm_num)).tsum_le_tsum
    xiShiftedTransverseChargeDensity_one_le_four_div_eightyFive_mul_orientation
    (summable_xiThermalOrientationTerm.mul_left (4 / 85 : ℝ))

/-- **Safe-shift transverse-charge damping law.** -/
theorem xiShiftedTransverseCharge_one_le_centralOrientationBudget :
    xiShiftedTransverseCharge 1 ≤
      (4 / 85 : ℝ) * normalizedPrimeArchMoment 0 *
        xiThermalOrientationEnergy := by
  have hA :
      0 ≤ (xiShiftedReciprocalMoment 1 0).re :=
    (re_xiShiftedReciprocalMoment_pos
      (y := 1) (by norm_num) (n := 0) (by norm_num)).le
  have hμ : 0 ≤ normalizedPrimeArchMoment 0 :=
    normalizedPrimeArchMoment_zero_pos.le
  have hE : 0 ≤ xiThermalOrientationEnergy :=
    xiThermalOrientationEnergy_nonneg
  rw [xiShiftedTransverseCharge]
  calc
    (xiShiftedReciprocalMoment 1 0).re *
          ∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity 1 q ≤
        (xiShiftedReciprocalMoment 1 0).re *
          ((4 / 85 : ℝ) * xiThermalOrientationEnergy) :=
      mul_le_mul_of_nonneg_left
        tsum_xiShiftedTransverseChargeDensity_one_le_orientationEnergy hA
    _ ≤ normalizedPrimeArchMoment 0 *
          ((4 / 85 : ℝ) * xiThermalOrientationEnergy) :=
      mul_le_mul_of_nonneg_right
        re_xiShiftedReciprocalMoment_one_zero_le_normalizedPrimeArchMoment_zero
        (mul_nonneg (by norm_num) hE)
    _ = (4 / 85 : ℝ) * normalizedPrimeArchMoment 0 *
          xiThermalOrientationEnergy := by ring

/-- Source-dependent cubic endpoint cap for the complete safe-shift charge. -/
theorem xiShiftedTransverseCharge_one_le_exactCubicEndpointBudget :
    xiShiftedTransverseCharge 1 ≤
      (4 / 85 : ℝ) * normalizedPrimeArchMoment 0 *
        xiThermalExactCubicEndpointBudget := by
  refine xiShiftedTransverseCharge_one_le_centralOrientationBudget.trans ?_
  exact mul_le_mul_of_nonneg_left
    xiThermalOrientationEnergy_le_exactCubicEndpointBudget
    (mul_nonneg (by norm_num) normalizedPrimeArchMoment_zero_pos.le)

/-- **Absolute safe-shift charge cap.**  The remaining Suzuki response dispersion need only
dominate this explicit rational scale. -/
theorem xiShiftedTransverseCharge_one_lt_absoluteBudget :
    xiShiftedTransverseCharge 1 < (116 / 7968750000 : ℝ) := by
  have hμ := normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  have hE := xiThermalOrientationEnergy_lt_one_over_oneHundredFiftyThousand
  have hμpos : 0 < normalizedPrimeArchMoment 0 :=
    normalizedPrimeArchMoment_zero_pos
  have hEpos : 0 < (1 / 150000 : ℝ) := by norm_num
  calc
    xiShiftedTransverseCharge 1 ≤
        (4 / 85 : ℝ) * normalizedPrimeArchMoment 0 *
          xiThermalOrientationEnergy :=
      xiShiftedTransverseCharge_one_le_centralOrientationBudget
    _ < (4 / 85 : ℝ) * normalizedPrimeArchMoment 0 * (1 / 150000 : ℝ) :=
      mul_lt_mul_of_pos_left hE
        (mul_pos (by norm_num) hμpos)
    _ < (4 / 85 : ℝ) * (29 / 625 : ℝ) * (1 / 150000 : ℝ) := by
      have hscale : 0 < (4 / 85 : ℝ) * (1 / 150000 : ℝ) := by positivity
      nlinarith [mul_lt_mul_of_pos_left hμ hscale]
    _ = (116 / 7968750000 : ℝ) := by norm_num

/-- A single explicit source-dispersion floor now suffices for strict passage of Suzuki's first
nonlinear target wall. -/
theorem primeArchSafeShiftHankelMinor_pos_of_absoluteBudget_le_dispersion
    (hfloor :
      (116 / 7968750000 : ℝ) ≤ xiShiftedResponseHilbertDispersion 1) :
    0 <
      (primeArchShiftedReciprocalMoment 1 0).re *
          (primeArchShiftedReciprocalMoment 1 2).re -
        (primeArchShiftedReciprocalMoment 1 1).re ^ (2 : ℕ) := by
  rw [primeArchSafeShiftHankelMinor_eq_hilbertDispersion_sub_transverseCharge]
  have hcharge := xiShiftedTransverseCharge_one_lt_absoluteBudget
  linarith

end

end RHTower
