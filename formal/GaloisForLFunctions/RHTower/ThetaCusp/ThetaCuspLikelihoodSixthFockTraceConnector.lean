import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthSourceUpperOrientation

/-!
# Sixth Fock supertrace lands in the literal theta source jet

The positive odd Fock weight is not merely an auxiliary orientation scalar.  Its complete
negative-parity budget lies strictly below the sixth logarithmic derivative of the actual
higher-theta likelihood partition.  Thus the graded completion carries a coefficient-faithful
piece of the literal sixth source trace, before any Xi determinant or divisor is introduced.
-/

namespace RHTower

noncomputable section

/-- The completed odd Fock-sector weight is a strict lower source trace for the literal sixth
logarithmic likelihood jet. -/
theorem thetaCuspLikelihoodSixthFockOddWeight_lt_sourceLogPartitionJetSix
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSixthFockOddWeight x <
      thetaCuspLikelihoodSourceLogPartitionJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let M := thetaCuspHigherLikelihoodSpectralMoment B
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let P := thetaCuspLikelihoodPartition B
  let evenTail := ∑' m : ℕ, (((2 * (m + 2) : ℕ) : ℝ) ^ (5 : ℕ)) *
    r ^ (2 * (m + 2) - 1)
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hM1 : 0 < M 1 := by
    simpa only [M] using thetaCuspHigherLikelihoodSpectralMoment_one_pos hB
  have h12 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 1
  have h23 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 2
  have h34 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 3
  have h45 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 4
  have h56 := three_mul_thetaCuspHigherLikelihoodSpectralMoment_le_succ hB 5
  have hM6 : 0 < M 6 := by
    dsimp only [M] at hM1 h12 h23 h34 h45 h56 ⊢
    nlinarith
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 399 * r < 1 := by
    simpa only [B, r, M] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have hP : 0 < P := by
    simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPeq : P = 1 + r := by
    dsimp only [P, r]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hPtwo : P < 2 := by
    rw [hPeq]
    nlinarith
  have htail0 : 0 ≤ evenTail := by
    dsimp only [evenTail]
    exact tsum_nonneg fun m => by positivity
  have hfactor : 1 - (384 * r + 30 * evenTail) ≤ 1 := by
    nlinarith
  have hlead0 : 0 ≤ (1 / 30 : ℝ) * A ^ (6 : ℕ) * M 6 := by positivity
  have hfockUpper : thetaCuspLikelihoodSixthFockOddWeight x ≤
      (1 / 30 : ℝ) * A ^ (6 : ℕ) * M 6 := by
    rw [thetaCuspLikelihoodSixthFockOddWeight]
    dsimp only [A, B, r, M, evenTail]
    exact mul_le_of_le_one_right hlead0 hfactor
  have hAM : 0 < A ^ (6 : ℕ) * M 6 := mul_pos (pow_pos hA 6) hM6
  have hrawNormalized :
      (1 / 30 : ℝ) * A ^ (6 : ℕ) * M 6 <
        (2 / 25 : ℝ) * A ^ (6 : ℕ) * (M 6 / P) := by
    rw [show (2 / 25 : ℝ) * A ^ (6 : ℕ) * (M 6 / P) =
        ((2 / 25 : ℝ) * A ^ (6 : ℕ) * M 6) / P by ring]
    apply (lt_div_iff₀ hP).2
    have hprod : 0 < (2 - P) * (A ^ (6 : ℕ) * M 6) :=
      mul_pos (sub_pos.mpr hPtwo) hAM
    nlinarith
  have hsource :=
    two_twentyFifths_mul_likelihoodSixthMoment_lt_sourceLogPartitionJetSix hx
  have hsource' :
      (2 / 25 : ℝ) * A ^ (6 : ℕ) * (M 6 / P) <
        thetaCuspLikelihoodSourceLogPartitionJetSix x := by
    simpa only [A, B, M, P, thetaCuspLikelihoodNormalizedMoment] using hsource
  exact lt_of_le_of_lt hfockUpper (hrawNormalized.trans hsource')

/-- Closed coefficient-faithful sixth-grade source landing: the Fock weight is positive and is
strictly dominated by the actual sixth logarithmic source jet. -/
theorem thetaCuspLikelihoodSixthFockSourceLanding
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSixthFockOddWeight x ∧
      thetaCuspLikelihoodSixthFockOddWeight x <
        thetaCuspLikelihoodSourceLogPartitionJetSix x := by
  exact ⟨thetaCuspLikelihoodSixthFockOddWeight_pos hx,
    thetaCuspLikelihoodSixthFockOddWeight_lt_sourceLogPartitionJetSix hx⟩

/-- Two-sided coefficient-faithful sixth-grade landing.  The signed Fock trace survives inside
the literal logarithmic source jet, and the latter remains within four percent of the ordinary
one-particle source trace. -/
theorem thetaCuspLikelihoodSixthFockSourceSandwich
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSixthFockOddWeight x <
        thetaCuspLikelihoodSourceLogPartitionJetSix x ∧
      thetaCuspLikelihoodSourceLogPartitionJetSix x <
        (26 / 25 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  exact ⟨thetaCuspLikelihoodSixthFockOddWeight_lt_sourceLogPartitionJetSix hx,
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twentySixTwentyFifths_ordinary hx⟩

end

end RHTower
