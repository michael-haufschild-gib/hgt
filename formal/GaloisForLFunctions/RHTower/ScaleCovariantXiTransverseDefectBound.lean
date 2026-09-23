import GaloisForLFunctions.RHTower.ScaleCovariantXiBernsteinAbelCorollary
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Unconditional Xi transverse-defect bound

The scale-covariant Bernstein--Abel recession selects the supremum of
`|lambda| - Re lambda` over the centered reciprocal-square Xi coordinates.  This file writes that
defect exactly in horizontal/vertical zero coordinates and combines the open critical strip with
the source-derived squared-height gap `41/2 < (Im rho)^(2 : ℕ)`.  The result is an unconditional uniform
bound on the exact Xi recession invariant; it does not assert that the invariant vanishes.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Norm of a centered reciprocal-square Xi coordinate in horizontal/vertical zero
coordinates. -/
theorem norm_xiZeroCopyReciprocalSquare_eq_horizontalVertical
    (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ =
      1 / (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) := by
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, norm_xiSpectralPoint,
    div_eq_mul_inv, one_mul]
  have hsq : ‖(q.1 : ℂ) - 1 / 2‖ ^ (2 : ℕ) =
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im]
    ring
  rw [← hsq, inv_pow]
  norm_num [div_eq_mul_inv]

/-- Exact horizontal/vertical formula for the transverse defect of one Xi reciprocal-square
coordinate. -/
theorem transverseDefect_xiZeroCopyReciprocalSquare_eq
    (q : XiZeroCopy) :
    HTGeometry.transverseDefect (xiZeroCopyReciprocalSquare q) =
      2 * ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) /
        (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ) := by
  rw [HTGeometry.transverseDefect,
    norm_xiZeroCopyReciprocalSquare_eq_horizontalVertical,
    xiZeroCopyReciprocalSquare_re_formula]
  have hden :
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1)]
  field_simp [hden]
  ring

/-- Every actual Xi reciprocal-square coordinate has transverse defect strictly below
`2/1681`.  The constant comes only from the open critical strip and the unconditional
source-derived squared-height gap `41/2`. -/
theorem transverseDefect_xiZeroCopyReciprocalSquare_lt_two_over_1681
    (q : XiZeroCopy) :
    HTGeometry.transverseDefect (xiZeroCopyReciprocalSquare q) < 2 / 1681 := by
  rw [transverseDefect_xiZeroCopyReciprocalSquare_eq]
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let D : ℝ := (u + v) ^ (2 : ℕ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u < 1 / 4 :=
    xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hv : 41 / 2 < v := by
    simpa only [v] using xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have huv : 41 / 2 < u + v := by linarith
  have hD : (41 / 2 : ℝ) ^ (2 : ℕ) < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos (sub_pos.mpr huv)]
  have hDpos : 0 < D := (sq_pos_of_pos (by linarith : 0 < (41 / 2 : ℝ))).trans hD
  rw [show ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) = u by rfl,
    show (q.1 : ℂ).im ^ (2 : ℕ) = v by rfl,
    show (u + v) ^ (2 : ℕ) = D by rfl]
  rw [div_lt_iff₀ hDpos]
  have hleft : 2 * u < 1 / 2 := by linarith
  have hright : (1 / 2 : ℝ) < 2 / 1681 * D := by
    nlinarith
  exact hleft.trans hright

/-- **Unconditional Xi recession estimate.**  The intrinsic transverse-defect envelope selected
by scale-covariant Bernstein--Abel tomography lies in the explicit interval `[0, 2/1681]`. -/
theorem xiScaleCovariantTransverseDefect_mem_explicitInterval :
    xiScaleCovariantTransverseDefect ∈ Set.Icc (0 : ℝ) (2 / 1681) := by
  have hupper : ∀ z ∈ xiScaleCovariantReciprocalSquareSupport,
      HTGeometry.transverseDefect z ≤ (2 / 1681 : ℝ) := by
    rintro z ⟨q, rfl⟩
    exact (transverseDefect_xiZeroCopyReciprocalSquare_lt_two_over_1681 q).le
  have hb : BddAbove
      (HTGeometry.transverseDefect '' xiScaleCovariantReciprocalSquareSupport) := by
    refine ⟨2 / 1681, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hupper z hz
  constructor
  · rw [xiScaleCovariantTransverseDefect, HTGeometry.transverseDefectEnvelope]
    obtain ⟨z, hz⟩ := xiScaleCovariantReciprocalSquareSupport_nonempty
    exact (HTGeometry.transverseDefect_nonneg z).trans
      (le_csSup hb ⟨z, hz, rfl⟩)
  · rw [xiScaleCovariantTransverseDefect, HTGeometry.transverseDefectEnvelope]
    apply csSup_le (xiScaleCovariantReciprocalSquareSupport_nonempty.image _)
    rintro y ⟨z, hz, rfl⟩
    exact hupper z hz

/-- The first Xi amplitude, Abel-radius, and Gibbs recessions therefore all have limiting value in
the explicit interval `[0, 4/1681]`. -/
theorem two_mul_xiScaleCovariantTransverseDefect_mem_explicitInterval :
    2 * xiScaleCovariantTransverseDefect ∈ Set.Icc (0 : ℝ) (4 / 1681) := by
  rcases xiScaleCovariantTransverseDefect_mem_explicitInterval with ⟨h0, hΔ⟩
  constructor <;> nlinarith

end

end RHTower
