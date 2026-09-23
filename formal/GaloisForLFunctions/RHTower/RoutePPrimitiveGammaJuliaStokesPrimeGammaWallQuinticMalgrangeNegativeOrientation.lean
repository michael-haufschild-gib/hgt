import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallQuarticMalgrangePositiveOrientation

/-!
# Negative orientation of the fifth prime/Gamma wall Malgrange jet

The order-nine theta/Xi recurrence exposes the fifth cold residual.  Its numerator factors into
two independently negative pieces controlled by strict factorial-normalized theta-moment
contraction.  This determines the fifth irregular-RH Stokes/Malgrange orientation without a fitted
wall clock, Xi-zero selection, or numerical computation.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The fifth normalized prime--archimedean moment as the exact order-nine theta cumulant. -/
theorem normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 4 =
      thetaCuspNormalizedEvenMoment 5 / 362880 -
        thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 / 8064 +
        thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) * thetaCuspNormalizedEvenMoment 3 / 288 -
        thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3 / 1728 +
        5 * thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) / 576 -
        5 * thetaCuspNormalizedEvenMoment 1 ^ (3 : ℕ) * thetaCuspNormalizedEvenMoment 2 / 96 +
        thetaCuspNormalizedEvenMoment 1 ^ (5 : ℕ) / 16 := by
  have h := normalizedPrimeArchMoment_recursive 4
  norm_num [Finset.sum_range_succ, thetaCuspXiJet,
    thetaCuspPrimeArchProductJet, Nat.choose] at h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hr :
      -thetaCuspRawEvenMoment 5 +
        9 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 4 -
        504 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 3 +
        15120 * normalizedPrimeArchMoment 2 * thetaCuspRawEvenMoment 2 -
        181440 * normalizedPrimeArchMoment 3 * thetaCuspRawEvenMoment 1 +
        362880 * normalizedPrimeArchMoment 4 * thetaCuspRawEvenMoment 0 = 0 := by
    linear_combination hre
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment] at hr
  simp only [thetaCuspNormalizedEvenMoment] at hr ⊢
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne'] at hr ⊢
  ring_nf at hr ⊢
  nlinarith

/-- The fifth cold residual after forced first-jet scaling is strictly negative. -/
theorem normalizedPrimeArchMoment_four_sub_zero_pow_five_div_sixteen_neg :
    normalizedPrimeArchMoment 4 - normalizedPrimeArchMoment 0 ^ (5 : ℕ) / 16 < 0 := by
  let A := thetaCuspNormalizedEvenMoment 1
  let B := thetaCuspNormalizedEvenMoment 2
  let C := thetaCuspNormalizedEvenMoment 3
  let D := thetaCuspNormalizedEvenMoment 4
  let E := thetaCuspNormalizedEvenMoment 5
  have h0 := thetaCuspRawEvenMoment_zero_pos
  have hrawBA := thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq
  have hBA : B < 6 * A ^ (2 : ℕ) := by
    dsimp only [A, B, thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith
  have hrawC := thetaCuspRawEvenMoment_three_mul_zero_lt_fifteen_mul_one_mul_two
  have hC : C < 15 * A * B := by
    dsimp only [A, B, C, thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith
  have hrawE :=
    thetaCuspRawEvenMoment_five_mul_zero_lt_fortyFive_mul_one_mul_four
  have hE : E < 45 * A * D := by
    dsimp only [A, D, E, thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith
  have hleft : 0 < 6 * A ^ (2 : ℕ) - B := by linarith
  have hright : C - 15 * A * B < 0 := by linarith
  have hproduct : (6 * A ^ (2 : ℕ) - B) * (C - 15 * A * B) < 0 :=
    mul_neg_of_pos_of_neg hleft hright
  have hQ :
      E - 45 * A * D + 1260 * A ^ (2 : ℕ) * C - 210 * B * C +
          3150 * A * B ^ (2 : ℕ) - 18900 * A ^ (3 : ℕ) * B < 0 := by
    nlinarith
  rw [normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  dsimp only [A, B, C, D, E] at hQ
  nlinarith

/-- Exact negative scalar orientation of the canonical cold fifth Malgrange target. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFifthMalgrangeTarget_neg :
    12 * (normalizedPrimeArchMoment 4 -
      normalizedPrimeArchMoment 0 ^ (5 : ℕ) / 16) < 0 := by
  nlinarith [normalizedPrimeArchMoment_four_sub_zero_pow_five_div_sixteen_neg]

end

end RHTower
