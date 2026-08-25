import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicResidualNegativeOrientation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex

/-!
# Positive orientation of the fourth prime/Gamma wall Malgrange jet

The existing all-order cold irregular-RH law identifies the fourth Malgrange correction with

`-3 * (normalizedPrimeArchMoment 3 - normalizedPrimeArchMoment 0 ^ 4 / 8)`.

This module determines that previously open datum without fitting a wall clock or selecting Xi
zeros.  The order-seven theta/Xi recurrence first exposes the exact eighth-cumulant polynomial.
Strict factorial-normalized moment contraction and ordinary Stieltjes log-convexity then force its
sign.  Therefore the canonical cold fourth Stokes/Malgrange target is strictly positive.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The fourth normalized prime--archimedean moment as the exact order-seven theta cumulant. -/
theorem normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 3 =
      -thetaCuspNormalizedEvenMoment 4 / 5040 +
        thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 / 180 +
        thetaCuspNormalizedEvenMoment 2 ^ 2 / 144 -
        thetaCuspNormalizedEvenMoment 1 ^ 2 * thetaCuspNormalizedEvenMoment 2 / 12 +
        thetaCuspNormalizedEvenMoment 1 ^ 4 / 8 := by
  apply Complex.ofReal_injective
  push_cast
  have h := normalizedPrimeArchMoment_recursive 3
  norm_num [Finset.sum_range_succ, thetaCuspXiJet,
    thetaCuspPrimeArchProductJet, Nat.choose] at h
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment] at h
  simp only [thetaCuspNormalizedEvenMoment] at h ⊢
  push_cast at h ⊢
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne'] at h ⊢
  ring_nf at h ⊢
  linear_combination 38880 * h

/-- The fourth cold residual after forced first-jet scaling is strictly negative before the
Malgrange parity factor is applied. -/
theorem normalizedPrimeArchMoment_three_sub_zero_pow_four_div_eight_neg :
    normalizedPrimeArchMoment 3 - normalizedPrimeArchMoment 0 ^ 4 / 8 < 0 := by
  let A := thetaCuspNormalizedEvenMoment 1
  let B := thetaCuspNormalizedEvenMoment 2
  let C := thetaCuspNormalizedEvenMoment 3
  let D := thetaCuspNormalizedEvenMoment 4
  have h0 := thetaCuspRawEvenMoment_zero_pos
  have hB : 0 < B := by
    dsimp only [B, thetaCuspNormalizedEvenMoment]
    exact div_pos (thetaCuspRawEvenMoment_pos 2) h0
  have hstrict := thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq
  have hBA : B < 6 * A ^ 2 := by
    dsimp only [A, B, thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith
  have hrawLog := thetaCuspRawEvenMoment_sq_le_adjacent 3 (by omega)
  have hCD : C ^ 2 ≤ B * D := by
    dsimp only [B, C, D, thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne']
    nlinarith
  let P := -D + 28 * A * C + 35 * B ^ 2 - 420 * A ^ 2 * B
  have hscaled : 35 * B ^ 2 * B < 35 * B ^ 2 * (6 * A ^ 2) := by
    exact mul_lt_mul_of_pos_left hBA (by positivity)
  have hmul : B * P < 0 := by
    dsimp only [P]
    nlinarith [sq_nonneg (C - 14 * A * B)]
  have hneg : P < 0 := by
    have hquot : P < 0 / B :=
      (lt_div_iff₀ hB).2 (by simpa [mul_comm] using hmul)
    simpa using hquot
  rw [normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  dsimp only [A, B, C, D, P] at hneg
  nlinarith

/-- Exact positive scalar orientation of the canonical cold fourth Malgrange target. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFourthMalgrangeTarget_pos :
    0 < -3 *
      (normalizedPrimeArchMoment 3 - normalizedPrimeArchMoment 0 ^ 4 / 8) := by
  nlinarith [normalizedPrimeArchMoment_three_sub_zero_pow_four_div_eight_neg]

end

end RHTower
