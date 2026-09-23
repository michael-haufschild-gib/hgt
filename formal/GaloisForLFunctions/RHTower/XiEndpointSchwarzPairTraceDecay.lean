import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.XiEndpointFourthTraceDefectContraction
import GaloisForLFunctions.RHTower.XiEndpointReflectionNeumannCarrier

/-!
# Schwarz-pair decay of endpoint reciprocal traces

The two-copy endpoint height gap places every raw reciprocal Xi coordinate in the disk of radius
`4 / 25`, far inside the previously used uniform radius `9 / 10`.  Consequently the complete raw
reciprocal-power trace tower decays geometrically:

`‖T_(n+2)‖ < (4 / 25)^n * 47 / 1000`.

This gives a quantitative all-order convergence reserve for the endpoint Neumann reconstruction.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every raw reciprocal Xi coordinate lies in the disk of radius `4 / 25`. -/
theorem xiRawReciprocalCoordinate_norm_lt_four_twentyFifths (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q‖ < 4 / 25 := by
  have hheight :=
    xiZeroCopy_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq q
  have hsq : ‖(q.1 : ℂ)‖ ^ (2 : ℕ) =
      (q.1 : ℂ).re ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hlarge : (25 / 4 : ℝ) < ‖(q.1 : ℂ)‖ := by
    nlinarith [sq_nonneg (q.1 : ℂ).re, norm_nonneg (q.1 : ℂ)]
  have hnormpos : 0 < ‖(q.1 : ℂ)‖ := by
    linarith
  rw [xiRawReciprocalCoordinate, norm_inv]
  apply (inv_lt_comm₀ hnormpos (by norm_num)).2
  norm_num
  exact hlarge

/-- The strengthened fourth-trace endpoint norm budget is below `47 / 1000`. -/
theorem xiRawReciprocalHermitianMass_lt_fortySeven_thousandths :
    xiRawReciprocalHermitianMass < 47 / 1000 := by
  calc
    xiRawReciprocalHermitianMass ≤
        (2373 / 2365 : ℝ) * xiEndpointCompletedCurvature :=
      xiRawReciprocalHermitianMass_le_twoThousandThreeHundredSeventyThree_over_twoThousandThreeHundredSixtyFive_mul_curvature
    _ < (2373 / 2365 : ℝ) * (231 / 5000) :=
      mul_lt_mul_of_pos_left
        xiEndpointCompletedCurvature_lt_twoHundredThirtyOne_over_fiveThousand
        (by norm_num)
    _ < 47 / 1000 := by norm_num

/-- Every reciprocal trace above order two is controlled by the pair-height geometric radius and
the exact raw Hermitian mass. -/
theorem norm_xiRawReciprocalPowerTrace_add_two_le_four_twentyFifths_pow_mul_mass
    (n : ℕ) :
    ‖xiRawReciprocalPowerTrace (n + 2)‖ ≤
      (4 / 25 : ℝ) ^ n * xiRawReciprocalHermitianMass := by
  have hsum := summable_xiRawReciprocalCoordinate_pow_add_two n
  have hmajor := summable_norm_xiRawReciprocalCoordinate_sq.mul_left ((4 / 25 : ℝ) ^ n)
  rw [xiRawReciprocalPowerTrace]
  calc
    ‖∑' q : XiZeroCopy, xiRawReciprocalCoordinate q ^ (n + 2)‖ ≤
        ∑' q : XiZeroCopy, ‖xiRawReciprocalCoordinate q ^ (n + 2)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' q : XiZeroCopy,
        (4 / 25 : ℝ) ^ n * ‖xiRawReciprocalCoordinate q‖ ^ (2 : ℕ) := by
      exact hsum.norm.tsum_mono hmajor (fun q => by
        change ‖xiRawReciprocalCoordinate q ^ (n + 2)‖ ≤
          (4 / 25 : ℝ) ^ n * ‖xiRawReciprocalCoordinate q‖ ^ (2 : ℕ)
        rw [norm_pow, pow_add]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _)
            (xiRawReciprocalCoordinate_norm_lt_four_twentyFifths q).le n)
          (sq_nonneg _))
    _ = (4 / 25 : ℝ) ^ n * xiRawReciprocalHermitianMass := by
      rw [xiRawReciprocalHermitianMass, tsum_mul_left]

/-- Explicit exponential decay of the complete raw reciprocal-power trace tower. -/
theorem norm_xiRawReciprocalPowerTrace_add_two_lt_four_twentyFifths_pow_mul_fortySeven_thousandths
    (n : ℕ) :
    ‖xiRawReciprocalPowerTrace (n + 2)‖ <
      (4 / 25 : ℝ) ^ n * (47 / 1000) := by
  exact (norm_xiRawReciprocalPowerTrace_add_two_le_four_twentyFifths_pow_mul_mass n).trans_lt
    (mul_lt_mul_of_pos_left xiRawReciprocalHermitianMass_lt_fortySeven_thousandths
      (pow_pos (by norm_num) n))

end

end RHTower
