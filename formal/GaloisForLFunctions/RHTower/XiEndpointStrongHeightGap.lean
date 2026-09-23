import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Strong endpoint-source height gap

The exact endpoint curvature bound `C < 2 / 43`, together with the inverse endpoint-source height
law `1 / C - 1 ≤ (Im ρ)^(2 : ℕ)`, forces every nontrivial Xi zero above squared height `41 / 2`.
This gives a source-pure zero-free band `|Im ρ| ≤ 9 / 2`, and hence the centered zero-free slab
`|Re z| ≤ 9 / 2`, without zero enumeration or a numerical zero verification.  Radius four is
retained as the clean corollary needed after the extra half-strip displacement in the paired
resolvent estimate.
-/

open Complex

namespace RHTower

noncomputable section

/-- The sharpened endpoint source value forces every Xi multiplicity copy above squared height
`41 / 2`. -/
theorem xiZeroCopy_fortyOne_div_two_lt_im_sq (q : XiZeroCopy) :
    (41 / 2 : ℝ) < (q.1 : ℂ).im ^ (2 : ℕ) := by
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hCinv : (43 / 2 : ℝ) < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_two_over_fortyThree]
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  linarith

/-- The same squared-height gap on the actual Xi divisor support. -/
theorem xiDivisorSupport_fortyOne_div_two_lt_im_sq (rho : XiDivisorSupport) :
    (41 / 2 : ℝ) < (rho : ℂ).im ^ (2 : ℕ) := by
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    exact ⟨rho, ⟨0, hn⟩⟩
  simpa only [q] using xiZeroCopy_fortyOne_div_two_lt_im_sq q

/-- Every Xi zero satisfies the strong endpoint-source squared-height gap. -/
theorem fortyOne_div_two_lt_im_sq_of_xi_eq_zero {rho : ℂ}
    (hzero : xi rho = 0) :
    (41 / 2 : ℝ) < rho.im ^ (2 : ℕ) :=
  xiDivisorSupport_fortyOne_div_two_lt_im_sq
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩

/-- Source-pure zero-free horizontal band for Xi. -/
theorem xi_ne_zero_of_abs_im_le_nine_halves {rho : ℂ}
    (hrho : |rho.im| ≤ 9 / 2) :
    xi rho ≠ 0 := by
  intro hzero
  have hheight := fortyOne_div_two_lt_im_sq_of_xi_eq_zero hzero
  nlinarith [sq_abs rho.im, abs_nonneg rho.im]

/-- In centered coordinates, Xi is zero-free on the closed slab `|Re z| ≤ 9 / 2`. -/
theorem XiC_ne_zero_of_abs_re_le_nine_halves {z : ℂ}
    (hz : |z.re| ≤ 9 / 2) :
    XiC z ≠ 0 := by
  intro hzero
  have hheight : (41 / 2 : ℝ) < (1 / 2 + z * I).im ^ (2 : ℕ) :=
    fortyOne_div_two_lt_im_sq_of_xi_eq_zero hzero
  have him : (1 / 2 + z * I).im = z.re := by simp [mul_im]
  rw [him] at hheight
  nlinarith [sq_abs z.re, abs_nonneg z.re]

/-- Integer-radius corollary used by the paired-resolvent sign theorem. -/
theorem xi_ne_zero_of_abs_im_le_four {rho : ℂ} (hrho : |rho.im| ≤ 4) :
    xi rho ≠ 0 :=
  xi_ne_zero_of_abs_im_le_nine_halves (hrho.trans (by norm_num))

/-- Integer-radius centered corollary used by the paired-resolvent sign theorem. -/
theorem XiC_ne_zero_of_abs_re_le_four {z : ℂ} (hz : |z.re| ≤ 4) :
    XiC z ≠ 0 :=
  XiC_ne_zero_of_abs_re_le_nine_halves (hz.trans (by norm_num))

end

end RHTower
