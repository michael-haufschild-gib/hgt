import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCassiniCalibratedReciprocalMomentNoGo

/-!
# Theta-cusp fourth-moment concentration no-go

The legacy fourth-moment concentration premise is incompatible with the
unconditional normalized-moment bounds already proved from the theta source.
Indeed, it would imply
`normalizedPrimeArchMoment 0 ^ (2 : ℕ) ≤ 7 * normalizedPrimeArchMoment 1`, whereas
the source bounds put the left side above `1 / 625` and the right side below
`63 / 50000`.

The viable interface for the sixth-moment Hankel problem is the adjacent-ratio
split in `PrimeArchThetaCumulantRatioSplit`.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- The theta-cusp source cannot satisfy the legacy fourth-moment concentration
premise. This removes its conditional consumers as possible routes to the
sixth-moment Hankel inequality. -/
theorem not_thetaCuspFourthMomentConcentration :
    ¬ ThetaCuspFourthMomentConcentration := by
  intro hconc
  rw [ThetaCuspFourthMomentConcentration] at hconc
  have h0 := thetaCuspRawEvenMoment_zero_pos
  have hM0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hM1 := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  have hnormalized :
      normalizedPrimeArchMoment 0 ^ (2 : ℕ) ≤ 7 * normalizedPrimeArchMoment 1 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment]
    simp only [thetaCuspNormalizedEvenMoment]
    field_simp [h0.ne'] at hconc ⊢
    nlinarith
  have hM0sq :
      (1 / 25 : ℝ) ^ (2 : ℕ) < normalizedPrimeArchMoment 0 ^ (2 : ℕ) := by
    nlinarith [normalizedPrimeArchMoment_zero_pos]
  nlinarith

end

end RHTower
