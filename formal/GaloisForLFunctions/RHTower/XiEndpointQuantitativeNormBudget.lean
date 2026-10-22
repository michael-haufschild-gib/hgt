import GaloisForLFunctions.RHTower.XiEndpointReflectionDefectEnergy
import GaloisForLFunctions.RHTower.CCM.CCMRectangularTwoEdge

/-!
# A quantitative endpoint norm budget from the Xi height gap

For a zero `rho = beta + i gamma`, pair `rho` with its critical-line reflection
`1 - conj rho`.  The Hermitian-to-holomorphic endpoint ratio of that orbit is exactly

`(gamma^(2 : ℕ) + 1/4 + delta^(2 : ℕ)) / (gamma^(2 : ℕ) + 1/4 - delta^(2 : ℕ))`,

where `delta = beta - 1/2`.  The critical strip gives `|delta| < 1/2`; the unconditional
global Xi height gap gives `eta ≤ |gamma|`.  This yields a genuine quantitative estimate on the
missing Connes norm budget:

`H_raw ≤ (1 + 1 / (2 * eta^(2 : ℕ))) * C_endpoint`.

The factor is finite and strictly larger than the sharp RH value `1`.  Its excess isolates the
remaining analytic task: a cofinal source estimate must remove the transverse `delta^(2 : ℕ)` loss.
-/

open Complex

namespace RHTower

noncomputable section

lemma endpoint_defect_term_eq (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ) =
      (1 - 2 * (q.1 : ℂ).re) ^ (2 : ℕ) /
        (((q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) *
          ((1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ))) := by
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hA : (q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero him]
  have hB : (1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero him]
  rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate]
  change ‖((q.1 : ℂ))⁻¹ -
      (1 - (starRingEnd ℂ) (q.1 : ℂ))⁻¹‖ ^ (2 : ℕ) = _
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.inv_re, Complex.inv_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    sub_neg_eq_add, zero_add, Complex.normSq_apply]
  field_simp [hA, hB]
  ring

lemma endpoint_cross_term_re_eq (q : XiZeroCopy) :
    (xiRawReciprocalCoordinate q *
      (starRingEnd ℂ)
        (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re =
      ((q.1 : ℂ).im ^ (2 : ℕ) + (q.1 : ℂ).re * (1 - (q.1 : ℂ).re)) /
        (((q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) *
          ((1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ))) := by
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hA : (q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero him]
  have hB : (1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero him]
  rw [xiRawReciprocalCoordinate, xiRawReciprocalCoordinate]
  change (((q.1 : ℂ))⁻¹ * (starRingEnd ℂ)
      ((1 - (starRingEnd ℂ) (q.1 : ℂ))⁻¹)).re = _
  simp only [map_inv₀, map_sub, map_one]
  have hstar : (starRingEnd ℂ) ((starRingEnd ℂ) (q.1 : ℂ)) = (q.1 : ℂ) := by simp
  rw [hstar]
  simp only [mul_re, Complex.inv_re, Complex.inv_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
  field_simp [hA, hB]
  ring

theorem endpoint_defect_term_le_cross_of_height
    {η : ℝ} (hη : 0 < η)
    (hheight : ∀ q : XiZeroCopy, η ≤ |(q.1 : ℂ).im|)
    (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ) ≤
      (1 / η ^ (2 : ℕ)) *
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
  rw [endpoint_defect_term_eq, endpoint_cross_term_re_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hηsq : η ^ (2 : ℕ) ≤ (q.1 : ℂ).im ^ (2 : ℕ) := by
    have hpow := pow_le_pow_left₀ (le_of_lt hη) (hheight q) 2
    simpa only [sq_abs] using hpow
  have hApos : 0 < (q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hBpos : 0 < (1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hdenpos : 0 <
      ((q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) *
        ((1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) :=
    mul_pos hApos hBpos
  rw [div_le_iff₀ hdenpos]
  field_simp [ne_of_gt hη]
  nlinarith [sq_nonneg (1 - 2 * (q.1 : ℂ).re),
    mul_nonneg hstrip.1.le (sub_nonneg.mpr hstrip.2.le)]

theorem endpoint_cross_term_re_nonneg (q : XiZeroCopy) :
    0 ≤ (xiRawReciprocalCoordinate q *
      (starRingEnd ℂ)
        (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
  rw [endpoint_cross_term_re_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hApos : 0 < (q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hBpos : 0 < (1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  exact div_nonneg
    (add_nonneg (sq_nonneg _) (mul_nonneg hstrip.1.le (sub_nonneg.mpr hstrip.2.le)))
    (mul_pos hApos hBpos).le

/-- Every endpoint cross term dominates the reciprocal quadratic height weight.

This is the pointwise source estimate behind the endpoint height law.  It uses only the
critical-strip location `0 < re rho < 1`; no zero-free region or RH input enters. -/
theorem endpoint_cross_term_re_ge_inv_one_add_im_sq (q : XiZeroCopy) :
    1 / ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ≤
      (xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
  rw [endpoint_cross_term_re_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  let β : ℝ := (q.1 : ℂ).re
  let γ : ℝ := (q.1 : ℂ).im
  have hApos : 0 < β ^ (2 : ℕ) + γ ^ (2 : ℕ) := by
    dsimp [β, γ]
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hBpos : 0 < (1 - β) ^ (2 : ℕ) + γ ^ (2 : ℕ) := by
    dsimp [β, γ]
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hGpos : 0 < γ ^ (2 : ℕ) + 1 := by positivity
  have htail : 0 ≤ 3 * γ ^ (2 : ℕ) + β ^ (2 : ℕ) - β + 1 := by
    nlinarith [sq_nonneg γ, sq_nonneg (β - 1 / 2)]
  have hprod : 0 ≤ β * (1 - β) *
      (3 * γ ^ (2 : ℕ) + β ^ (2 : ℕ) - β + 1) := by
    exact mul_nonneg
      (mul_nonneg hstrip.1.le (sub_nonneg.mpr hstrip.2.le)) htail
  have hid :
      (γ ^ (2 : ℕ) + β * (1 - β)) * (γ ^ (2 : ℕ) + 1) -
          ((β ^ (2 : ℕ) + γ ^ (2 : ℕ)) * ((1 - β) ^ (2 : ℕ) + γ ^ (2 : ℕ))) =
        β * (1 - β) * (3 * γ ^ (2 : ℕ) + β ^ (2 : ℕ) - β + 1) := by
    ring
  change 1 / (γ ^ (2 : ℕ) + 1) ≤
      (γ ^ (2 : ℕ) + β * (1 - β)) /
        ((β ^ (2 : ℕ) + γ ^ (2 : ℕ)) * ((1 - β) ^ (2 : ℕ) + γ ^ (2 : ℕ)))
  rw [div_le_div_iff₀ hGpos (mul_pos hApos hBpos)]
  nlinarith

/-- A single positive endpoint cross term is bounded by the full completed endpoint curvature. -/
theorem endpoint_cross_term_re_le_curvature (q : XiZeroCopy) :
    (xiRawReciprocalCoordinate q *
      (starRingEnd ℂ)
        (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re ≤
      xiEndpointCompletedCurvature := by
  have hR : Summable (fun q : XiZeroCopy =>
      (xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) := by
    exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun q => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  rw [xiEndpointCompletedCurvature_eq_cross_re,
    Complex.re_tsum summable_xiEndpointCrossTerm]
  exact hR.le_tsum q (fun j _ => endpoint_cross_term_re_nonneg j)

/-- **Source-controlled zero-height law.**  Every nontrivial Xi zero pays at least one unit after
its squared height is weighted by the single completed prime--Gamma endpoint value. -/
theorem xiZeroCopy_endpoint_source_height_law (q : XiZeroCopy) :
    1 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have hupper := endpoint_cross_term_re_le_curvature q
  have h := hlower.trans hupper
  rw [div_le_iff₀ (by positivity : 0 < (q.1 : ℂ).im ^ (2 : ℕ) + 1)] at h
  simpa [mul_comm] using h

/-- Every nontrivial Xi zero satisfies the inverse endpoint-source height inequality.  When the
endpoint curvature is below one, its left side is a strictly positive global height gap. -/
theorem xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap (q : XiZeroCopy) :
    1 / xiEndpointCompletedCurvature - 1 ≤ (q.1 : ℂ).im ^ (2 : ℕ) := by
  have hbudget := xiZeroCopy_endpoint_source_height_law q
  have hCpos : 0 < xiEndpointCompletedCurvature := by
    by_contra hnonpos
    have hnonpos' : xiEndpointCompletedCurvature ≤ 0 := le_of_not_gt hnonpos
    have hheight : 0 < (q.1 : ℂ).im ^ (2 : ℕ) + 1 := by positivity
    have : xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos' hheight.le
    linarith
  have hinv : 1 / xiEndpointCompletedCurvature ≤ (q.1 : ℂ).im ^ (2 : ℕ) + 1 := by
    rw [div_le_iff₀ hCpos]
    simpa [mul_comm] using hbudget
  linarith

/-- A scalar endpoint source bound below one converts the pointwise height law into a defect-to-
cross-term estimate whose factor depends only on that same source value. -/
theorem endpoint_defect_term_le_source_factor_cross
    (hC : xiEndpointCompletedCurvature < 1) (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℕ) ≤
      (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
  rw [endpoint_defect_term_eq, endpoint_cross_term_re_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hbudget := xiZeroCopy_endpoint_source_height_law q
  have hApos : 0 < (q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hBpos : 0 < (1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  have hdenpos : 0 <
      ((q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) *
        ((1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) :=
    mul_pos hApos hBpos
  have hCnonneg : 0 ≤ xiEndpointCompletedCurvature := by
    by_contra hneg
    have hnonpos : xiEndpointCompletedCurvature < 0 := lt_of_not_ge hneg
    have hheight : 0 < (q.1 : ℂ).im ^ (2 : ℕ) + 1 := by positivity
    have : xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ (2 : ℕ) + 1) < 0 :=
      mul_neg_of_neg_of_pos hnonpos hheight
    linarith
  have hsq : (1 - 2 * (q.1 : ℂ).re) ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg hstrip.1.le (sub_nonneg.mpr hstrip.2.le)]
  have hnum :
      (1 - xiEndpointCompletedCurvature) *
          (1 - 2 * (q.1 : ℂ).re) ^ (2 : ℕ) ≤
        xiEndpointCompletedCurvature *
          ((q.1 : ℂ).im ^ (2 : ℕ) +
            (q.1 : ℂ).re * (1 - (q.1 : ℂ).re)) := by
    have hleft :
        (1 - xiEndpointCompletedCurvature) *
            (1 - 2 * (q.1 : ℂ).re) ^ (2 : ℕ) ≤
          1 - xiEndpointCompletedCurvature := by
      simpa using mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hC.le)
    nlinarith [mul_nonneg hCnonneg
      (mul_nonneg hstrip.1.le (sub_nonneg.mpr hstrip.2.le))]
  calc
    _ ≤ (xiEndpointCompletedCurvature *
          ((q.1 : ℂ).im ^ (2 : ℕ) +
            (q.1 : ℂ).re * (1 - (q.1 : ℂ).re)) /
          (1 - xiEndpointCompletedCurvature)) /
        (((q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) *
          ((1 - (q.1 : ℂ).re) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ))) := by
      rw [div_le_div_iff_of_pos_right hdenpos,
        le_div_iff₀ (sub_pos.mpr hC)]
      simpa [mul_comm] using hnum
    _ = _ := by ring

/-- **Source-only quantitative endpoint defect bound.**  Once the completed endpoint curvature is
known to lie below one, no external zero-height constant is needed. -/
theorem xiEndpointDefectEnergy_le_source_factor
    (hC : xiEndpointCompletedCurvature < 1) :
    xiEndpointReflectionDefectEnergy ≤
      (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
        xiEndpointCompletedCurvature := by
  have hR : Summable (fun q : XiZeroCopy =>
      (xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) := by
    exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun q => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  have hscaled := hR.mul_left
    (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature))
  have hsumle := summable_xiEndpointReflectionDefectEnergy.tsum_le_tsum
    (fun q => endpoint_defect_term_le_source_factor_cross hC q) hscaled
  have hcross :
      (∑' q : XiZeroCopy,
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) =
        xiEndpointCompletedCurvature := by
    rw [← Complex.re_tsum summable_xiEndpointCrossTerm,
      ← xiEndpointCompletedCurvature_eq_cross_re]
  rw [xiEndpointReflectionDefectEnergy]
  calc
    _ ≤ ∑' q : XiZeroCopy,
        (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
          (xiRawReciprocalCoordinate q *
            (starRingEnd ℂ)
              (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := hsumle
    _ = (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
        ∑' q : XiZeroCopy,
          (xiRawReciprocalCoordinate q *
            (starRingEnd ℂ)
              (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re :=
      tsum_mul_left
    _ = _ := by rw [hcross]

/-- The resulting Hermitian norm budget is expressed entirely through the completed endpoint
source.  Its sharp RH factor is `1`; this theorem gives the explicit factor `(2-C)/(2(1-C))`. -/
theorem xiRawMass_le_source_only_factor
    (hC : xiEndpointCompletedCurvature < 1) :
    xiRawReciprocalHermitianMass ≤
      ((2 - xiEndpointCompletedCurvature) /
        (2 * (1 - xiEndpointCompletedCurvature))) *
        xiEndpointCompletedCurvature := by
  have hgap := xiEndpointDefectEnergy_le_source_factor hC
  have hid := xiEndpointReflectionDefectEnergy_eq_mass_sub_source
  have hden : 1 - xiEndpointCompletedCurvature ≠ 0 :=
    ne_of_gt (sub_pos.mpr hC)
  calc
    xiRawReciprocalHermitianMass =
        xiEndpointCompletedCurvature + xiEndpointReflectionDefectEnergy / 2 := by
      linarith
    _ ≤ xiEndpointCompletedCurvature +
        ((xiEndpointCompletedCurvature /
          (1 - xiEndpointCompletedCurvature)) *
            xiEndpointCompletedCurvature) / 2 := by
      linarith
    _ = ((2 - xiEndpointCompletedCurvature) /
        (2 * (1 - xiEndpointCompletedCurvature))) *
          xiEndpointCompletedCurvature := by
      field_simp [hden]
      ring

theorem xiEndpointCompletedCurvature_nonneg :
    0 ≤ xiEndpointCompletedCurvature := by
  have hC := summable_xiEndpointCrossTerm
  rw [xiEndpointCompletedCurvature_eq_cross_re]
  rw [Complex.re_tsum hC]
  exact tsum_nonneg endpoint_cross_term_re_nonneg

theorem xiEndpointDefectEnergy_le_of_heightGap
    {η : ℝ} (hη : 0 < η)
    (hheight : ∀ q : XiZeroCopy, η ≤ |(q.1 : ℂ).im|) :
    xiEndpointReflectionDefectEnergy ≤
      (1 / η ^ (2 : ℕ)) * xiEndpointCompletedCurvature := by
  have hR : Summable (fun q : XiZeroCopy =>
      (xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) := by
    exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun q => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  have hscaled := hR.mul_left (1 / η ^ (2 : ℕ))
  have hsumle := summable_xiEndpointReflectionDefectEnergy.tsum_le_tsum
    (fun q => endpoint_defect_term_le_cross_of_height hη hheight q) hscaled
  have hcross :
      (∑' q : XiZeroCopy,
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) =
        xiEndpointCompletedCurvature := by
    rw [← Complex.re_tsum summable_xiEndpointCrossTerm,
      ← xiEndpointCompletedCurvature_eq_cross_re]
  rw [xiEndpointReflectionDefectEnergy]
  calc
    _ ≤ ∑' q : XiZeroCopy, (1 / η ^ (2 : ℕ)) *
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := hsumle
    _ = (1 / η ^ (2 : ℕ)) * ∑' q : XiZeroCopy,
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re :=
      tsum_mul_left
    _ = _ := by rw [hcross]

theorem xiRawReciprocalHermitianMass_le_factor_mul_endpointCurvature_of_heightGap
    {η : ℝ} (hη : 0 < η)
    (hheight : ∀ q : XiZeroCopy, η ≤ |(q.1 : ℂ).im|) :
    xiRawReciprocalHermitianMass ≤
      (1 + 1 / (2 * η ^ (2 : ℕ))) * xiEndpointCompletedCurvature := by
  have hgap := xiEndpointDefectEnergy_le_of_heightGap hη hheight
  have hid := xiEndpointReflectionDefectEnergy_eq_mass_sub_source
  calc
    xiRawReciprocalHermitianMass =
        xiEndpointCompletedCurvature + xiEndpointReflectionDefectEnergy / 2 := by
      linarith
    _ ≤ xiEndpointCompletedCurvature +
        ((1 / η ^ (2 : ℕ)) * xiEndpointCompletedCurvature) / 2 := by
      linarith
    _ = (1 + 1 / (2 * η ^ (2 : ℕ))) * xiEndpointCompletedCurvature := by
      field_simp [ne_of_gt hη]

theorem exists_xiEndpointQuantitativeNormBudget :
    ∃ η : ℝ, 0 < η ∧
      xiEndpointReflectionDefectEnergy ≤
        (1 / η ^ (2 : ℕ)) * xiEndpointCompletedCurvature ∧
      xiRawReciprocalHermitianMass ≤
        (1 + 1 / (2 * η ^ (2 : ℕ))) * xiEndpointCompletedCurvature := by
  obtain ⟨η, hη, hheight⟩ := exists_xiZeroCopy_abs_im_lower_bound
  exact ⟨η, hη, xiEndpointDefectEnergy_le_of_heightGap hη hheight,
    xiRawReciprocalHermitianMass_le_factor_mul_endpointCurvature_of_heightGap
      hη hheight⟩

end
end RHTower
