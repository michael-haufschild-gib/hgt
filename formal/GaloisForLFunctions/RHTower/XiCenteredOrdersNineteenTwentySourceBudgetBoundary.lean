import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaloisForLFunctions.HTGeometry.SectorPowerPositivity

/-!
# Centered orders nineteen and twenty source-budget boundaries

The extended fourth reciprocal-trace source band and the universal off-line height floor
force positivity of the twentieth centered reciprocal power outside one explicit
finite annulus. Consequently, emptiness of precisely that annulus discharges
positivity of normalized prime-archimedean moment nineteen.
-/

open Complex

namespace RHTower

noncomputable section

/-- **A sector failure is confined to the residual annulus.**  The residual window differs from the
edge corner only in its height floor: here the lower bound `2365/16 ≤ im²` comes from the centering
criterion rather than from the off-line height gap.  The certificate `P < A` is abstract, so one
law serves both residual orders. -/
private theorem sectorFailure_mem_residualAnnulus_aux {P A c K : ℝ} (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ c → P < A)
    (hhigh : K ≤ (q.1 : ℂ).im ^ (2 : ℕ) → P < A) (hfail : A ≤ P) :
    (q.1 : ℂ).re ≠ 1 / 2 ∧ c < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) ∧ (q.1 : ℂ).im ^ (2 : ℕ) < K := by
  refine ⟨hoff, ?_, xi_divisor_support_centered_re_sq_lt_quarter q.1, ?_, ?_⟩
  · by_contra h
    exact absurd (hinner (not_lt.mp h)) (not_lt.mpr hfail)
  · by_contra h
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (not_le.mp h))
  · by_contra h
    exact absurd (hhigh (not_lt.mp h)) (not_lt.mpr hfail)

theorem orderTwentyReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 163 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (20 : ℕ)).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 784 / 10000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

theorem xiCenteredOrderTwentySectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (2365 / 10464 : ℝ)) :
    163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hv : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ (2 : ℕ) :=
    le_of_not_gt fun hvlt => hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hvlt)
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 163) (u₀ := 2365 / 10464)
      (v₀ := 2365 / 16) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner hv
      (by norm_num) (by norm_num)

theorem xiCenteredOrderTwentySectorRatio_of_threeHundredTwentySevenHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 327 / 2 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 163) (u₀ := 1 / 4)
      (v₀ := 327 / 2) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

def XiCenteredOrderTwentyResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 10464 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) ∧
          (q.1 : ℂ).im ^ (2 : ℕ) < 327 / 2

theorem xiCenteredOrderTwentySectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        163 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    XiCenteredOrderTwentyResidualAnnulus q :=
  sectorFailure_mem_residualAnnulus_aux q hoff
    (fun h => xiCenteredOrderTwentySectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderTwentySectorRatio_of_threeHundredTwentySevenHalves_le_im_sq q h)
    hfail

theorem xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ (20 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderTwentyReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderTwentySectorFailure_mem_residualAnnulus q hoff hfail)
    hnot

def XiCenteredOrderTwentyResidualAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyResidualAnnulus q

/-- RH excludes the order-twenty residual annulus because every Xi divisor point is centered. -/
theorem xiCenteredOrderTwentyResidualAnnulusEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCenteredOrderTwentyResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  exact hq.1 (xi_divisor_support_re_eq_half_of_rh hRH q.1)

theorem xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_residualAnnulusEmpty
    (h : XiCenteredOrderTwentyResidualAnnulusEmpty) (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (20 : ℕ)).re := by
  apply xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_not_mem_residualAnnulus
  intro hq
  exact h ⟨q, hq⟩

theorem normalizedPrimeArchMoment_nineteen_pos_of_centeredOrderTwentyResidualAnnulusEmpty
    (h : XiCenteredOrderTwentyResidualAnnulusEmpty) :
    0 < normalizedPrimeArchMoment 19 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 19
  simpa using
    xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_residualAnnulusEmpty h

theorem orderTwentyOneReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 180 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (21 : ℕ)).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt (t := 747 / 10000) hA
    (by norm_num) (by norm_num) hsector (by norm_num; nlinarith [Real.pi_gt_d20])

theorem xiCenteredOrderTwentyOneSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (2365 / 11552 : ℝ)) :
    180 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hv : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ (2 : ℕ) :=
    le_of_not_gt fun hvlt => hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hvlt)
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 180) (u₀ := 2365 / 11552)
      (v₀ := 2365 / 16) (y₀ := 0) (y := 0) (by norm_num) le_rfl hinner hv
      (by norm_num) (by norm_num)

theorem xiCenteredOrderTwentyOneSectorRatio_of_threeHundredSixtyOneHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 361 / 2 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    180 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 180) (u₀ := 1 / 4)
      (v₀ := 361 / 2) (y₀ := 0) (y := 0) (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh (by norm_num) (by norm_num)

def XiCenteredOrderTwentyOneResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 11552 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) ∧
          (q.1 : ℂ).im ^ (2 : ℕ) < 361 / 2

theorem xiCenteredOrderTwentyOneSectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        180 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    XiCenteredOrderTwentyOneResidualAnnulus q :=
  sectorFailure_mem_residualAnnulus_aux q hoff
    (fun h => xiCenteredOrderTwentyOneSectorRatio_of_offLine_inner q hoff h)
    (fun h => xiCenteredOrderTwentyOneSectorRatio_of_threeHundredSixtyOneHalves_le_im_sq q h)
    hfail

theorem xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyOneResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ (21 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderTwentyOneReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderTwentyOneSectorFailure_mem_residualAnnulus q hoff hfail)
    hnot

def XiCenteredOrderTwentyOneResidualAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyOneResidualAnnulus q

/-- RH excludes the order-twenty-one residual annulus for the same centered-divisor reason. -/
theorem xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCenteredOrderTwentyOneResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  exact hq.1 (xi_divisor_support_re_eq_half_of_rh hRH q.1)

theorem xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_residualAnnulusEmpty
    (h : XiCenteredOrderTwentyOneResidualAnnulusEmpty) (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (21 : ℕ)).re := by
  apply xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_not_mem_residualAnnulus
  intro hq
  exact h ⟨q, hq⟩

theorem normalizedPrimeArchMoment_twenty_pos_of_centeredOrderTwentyOneResidualAnnulusEmpty
    (h : XiCenteredOrderTwentyOneResidualAnnulusEmpty) :
    0 < normalizedPrimeArchMoment 20 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 20
  simpa using
    xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_residualAnnulusEmpty h

def XiCenteredDegreeTenResidualAnnuliEmpty : Prop :=
  XiCenteredOrderTwentyResidualAnnulusEmpty ∧
    XiCenteredOrderTwentyOneResidualAnnulusEmpty

/-- RH simultaneously discharges both residual-annulus interfaces at degree ten. -/
theorem xiCenteredDegreeTenResidualAnnuliEmpty_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiCenteredDegreeTenResidualAnnuliEmpty :=
  ⟨xiCenteredOrderTwentyResidualAnnulusEmpty_of_riemannHypothesis hRH,
    xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_riemannHypothesis hRH⟩

theorem normalizedPrimeArchMoment_nineteen_pos_of_degreeTenResidualAnnuliEmpty
    (h : XiCenteredDegreeTenResidualAnnuliEmpty) :
    0 < normalizedPrimeArchMoment 19 :=
  normalizedPrimeArchMoment_nineteen_pos_of_centeredOrderTwentyResidualAnnulusEmpty h.1

theorem normalizedPrimeArchMoment_twenty_pos_of_degreeTenResidualAnnuliEmpty
    (h : XiCenteredDegreeTenResidualAnnuliEmpty) :
    0 < normalizedPrimeArchMoment 20 :=
  normalizedPrimeArchMoment_twenty_pos_of_centeredOrderTwentyOneResidualAnnulusEmpty h.2

/-- Degree-nineteen source-moment positivity no longer needs a residual-annulus premise once RH
is in scope. -/
theorem normalizedPrimeArchMoment_nineteen_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    0 < normalizedPrimeArchMoment 19 :=
  normalizedPrimeArchMoment_nineteen_pos_of_degreeTenResidualAnnuliEmpty
    (xiCenteredDegreeTenResidualAnnuliEmpty_of_riemannHypothesis hRH)

/-- Degree-twenty source-moment positivity no longer needs a residual-annulus premise once RH is
in scope. -/
theorem normalizedPrimeArchMoment_twenty_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    0 < normalizedPrimeArchMoment 20 :=
  normalizedPrimeArchMoment_twenty_pos_of_degreeTenResidualAnnuliEmpty
    (xiCenteredDegreeTenResidualAnnuliEmpty_of_riemannHypothesis hRH)

end

end RHTower
