import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure

/-!
# Schwarz-pair amplification of the Xi endpoint height gap

Ordinary conjugation has no fixed Xi divisor copy because every nontrivial zero has nonzero
ordinate.  The endpoint cross charge is nonnegative and invariant under this conjugation.  Charging
the resulting two-element orbit, including on the critical line, doubles the source-only endpoint
height law:

`2 ≤ xiEndpointCompletedCurvature * ((Im ρ)^2 + 1)`.

The corrected endpoint curvature bound then forces `(Im ρ)^2 > 9769 / 231`, hence the closed
zero-free band `|Im ρ| ≤ 13 / 2`.

These are unconditional quantitative bridge theorems, not a proof of RH.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- A nonnegative summable weight invariant under ordinary conjugation pays for both distinct
members of every Schwarz pair. -/
theorem two_mul_le_tsum_of_conj_invariant
    {f : XiZeroCopy → ℝ} (hnonneg : ∀ r, 0 ≤ f r) (hsum : Summable f)
    (hCinv : ∀ r, f (xiZeroCopyConjEquiv r) = f r) (q : XiZeroCopy) :
    2 * f q ≤ ∑' r, f r := by
  classical
  let qC := xiZeroCopyConjEquiv q
  let s : Finset XiZeroCopy := {q, qC}
  have hqC : q ≠ qC := by
    simpa only [qC] using xiZeroCopy_ne_conj q
  have hle := hsum.sum_le_tsum s (fun r _ => hnonneg r)
  have hC : f qC = f q := by
    simpa only [qC] using hCinv q
  have hfinite : ∑ r ∈ s, f r = 2 * f q := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqC]), Finset.sum_singleton, hC]
    ring
  rw [hfinite] at hle
  exact hle

/-- Both members of every Schwarz pair charge at most the full endpoint curvature. -/
theorem two_mul_xiEndpointCrossCharge_le_curvature (q : XiZeroCopy) :
    2 * xiEndpointCrossCharge q ≤ xiEndpointCompletedCurvature := by
  have hle := two_mul_le_tsum_of_conj_invariant
    (fun r => by
      simpa only [xiEndpointCrossCharge] using endpoint_cross_term_re_nonneg r)
    summable_xiEndpointCrossCharge xiEndpointCrossCharge_conj q
  rwa [tsum_xiEndpointCrossCharge_eq_curvature] at hle

/-- Exact Schwarz-pair height law: endpoint curvature pays two units for every Xi zero copy. -/
theorem two_le_curvature_mul_one_add_im_sq (q : XiZeroCopy) :
    2 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ 2 + 1) := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have horbit := two_mul_xiEndpointCrossCharge_le_curvature q
  have hden : 0 < (q.1 : ℂ).im ^ 2 + 1 := by positivity
  have hcharge : 2 / ((q.1 : ℂ).im ^ 2 + 1) ≤
      2 * xiEndpointCrossCharge q := by
    calc
      2 / ((q.1 : ℂ).im ^ 2 + 1) =
          2 * (1 / ((q.1 : ℂ).im ^ 2 + 1)) := by ring
      _ ≤ 2 * xiEndpointCrossCharge q :=
        mul_le_mul_of_nonneg_left hlower (by norm_num)
  have hbudget : 2 / ((q.1 : ℂ).im ^ 2 + 1) ≤
      xiEndpointCompletedCurvature := hcharge.trans horbit
  rwa [div_le_iff₀ hden] at hbudget

/-- Corrected endpoint curvature plus Schwarz-pair amplification forces every Xi multiplicity copy
above squared height `9769 / 231`. -/
theorem xiZeroCopy_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq
    (q : XiZeroCopy) :
    (9769 / 231 : ℝ) < (q.1 : ℂ).im ^ 2 := by
  have hbudget := two_le_curvature_mul_one_add_im_sq q
  have hC := xiEndpointCompletedCurvature_lt_twoHundredThirtyOne_over_fiveThousand
  have hden : 0 < (q.1 : ℂ).im ^ 2 + 1 := by positivity
  have hstrict :
      xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ 2 + 1) <
        (231 / 5000 : ℝ) * ((q.1 : ℂ).im ^ 2 + 1) :=
    mul_lt_mul_of_pos_right hC hden
  nlinarith

/-- Same Schwarz-pair squared-height gap on the Xi divisor support. -/
theorem xiDivisorSupport_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq
    (rho : XiDivisorSupport) :
    (9769 / 231 : ℝ) < (rho : ℂ).im ^ 2 := by
  let q : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    exact ⟨rho, ⟨0, hn⟩⟩
  simpa only [q] using
    xiZeroCopy_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq q

/-- Every Xi zero obeys the Schwarz-pair squared-height gap. -/
theorem nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq_of_xi_eq_zero
    {rho : ℂ} (hzero : xi rho = 0) :
    (9769 / 231 : ℝ) < rho.im ^ 2 :=
  xiDivisorSupport_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩

/-- Source-only zero-free horizontal band improved from radius `9 / 2` to `13 / 2`. -/
theorem xi_ne_zero_of_abs_im_le_thirteen_halves {rho : ℂ}
    (hrho : |rho.im| ≤ 13 / 2) :
    xi rho ≠ 0 := by
  intro hzero
  have hheight :=
    nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq_of_xi_eq_zero hzero
  nlinarith [sq_abs rho.im, abs_nonneg rho.im]

/-- In centered coordinates, Xi is zero-free on the closed slab `|Re z| ≤ 13 / 2`. -/
theorem XiC_ne_zero_of_abs_re_le_thirteen_halves {z : ℂ}
    (hz : |z.re| ≤ 13 / 2) :
    XiC z ≠ 0 := by
  intro hzero
  have hheight : (9769 / 231 : ℝ) < (1 / 2 + z * I).im ^ 2 :=
    nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq_of_xi_eq_zero hzero
  have him : (1 / 2 + z * I).im = z.re := by simp [mul_im]
  rw [him] at hheight
  nlinarith [sq_abs z.re, abs_nonneg z.re]

end

end RHTower
