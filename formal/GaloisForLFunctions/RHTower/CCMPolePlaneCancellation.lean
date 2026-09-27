import GaloisForLFunctions.RHTower.CCMPoleLeadingCancellation

/-!
# Uniform leading cancellation on the complete two-pole plane

The cancellation estimate holds simultaneously for all complex coefficients,
including coefficients chosen separately at each aperture. This uniform
bound retains the coefficient norm and makes no positivity assertion.
-/

noncomputable section
open Filter

namespace RHTower

theorem abs_ccmWeilPolePlane_le_entries (a : SuzukiPositiveAperture) (c d : ℂ) :
    |ccmRestrictedWeilSourceQuadratic a
      (c • ccmPolarFormVector a (1/2) + d • ccmPolarFormVector a (-1/2))| ≤
      (|ccmWeilPoleDiagonal a| + |ccmWeilPoleCross a|) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  rw [ccmWeilPoleCompression_parity_decomposition]
  have hnorm : ‖c + d‖ ^ 2 + ‖c - d‖ ^ 2 = 2 * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  calc
    _ ≤ |(ccmWeilPoleDiagonal a + ccmWeilPoleCross a) / 2 * ‖c + d‖ ^ 2| +
        |(ccmWeilPoleDiagonal a - ccmWeilPoleCross a) / 2 * ‖c - d‖ ^ 2| := abs_add_le _ _
    _ = |ccmWeilPoleDiagonal a + ccmWeilPoleCross a| / 2 * ‖c + d‖ ^ 2 +
        |ccmWeilPoleDiagonal a - ccmWeilPoleCross a| / 2 * ‖c - d‖ ^ 2 := by
      simp only [abs_mul, abs_div, abs_pow, abs_norm, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (|ccmWeilPoleDiagonal a| + |ccmWeilPoleCross a|) / 2 * ‖c + d‖ ^ 2 +
        (|ccmWeilPoleDiagonal a| + |ccmWeilPoleCross a|) / 2 * ‖c - d‖ ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)) (sq_nonneg _))
    _ = (|ccmWeilPoleDiagonal a| + |ccmWeilPoleCross a|) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
      rw [← mul_add, hnorm]
      ring

/-- One aperture threshold controls every complex vector in the actual pole plane. -/
theorem exists_uniform_ccmWeilPolePlane_cancellation (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : SuzukiPositiveAperture, ∀ a : SuzukiPositiveAperture, A ≤ a → ∀ c d : ℂ,
      |ccmRestrictedWeilSourceQuadratic a
        (c • ccmPolarFormVector a (1/2) + d • ccmPolarFormVector a (-1/2))| ≤
        epsilon * Real.exp (2 * a.1) * (‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have hlim : Tendsto (fun a : SuzukiPositiveAperture =>
      Real.exp (-(2 * a.1)) * (|ccmWeilPoleDiagonal a| + |ccmWeilPoleCross a|)) atTop (nhds 0) := by
    have h := tendsto_ccmWeilPoleDiagonal_scaled_zero.abs.add tendsto_ccmWeilPoleCross_scaled_zero.abs
    simpa only [abs_zero, add_zero, abs_mul, abs_of_pos (Real.exp_pos _), mul_add] using h
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hlim.eventually_le_const hepsilon)
  refine ⟨A, ?_⟩
  intro a ha c d
  have hs := mul_le_mul_of_nonneg_left (hA a ha) (Real.exp_pos (2 * a.1)).le
  have he : Real.exp (2 * a.1) * Real.exp (-(2 * a.1)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hs
  exact (abs_ccmWeilPolePlane_le_entries a c d).trans
    (mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hs) (by positivity))

end RHTower
