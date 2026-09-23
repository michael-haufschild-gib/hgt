import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# The third prime--archimedean source moment in theta-cusp moments

The all-order cumulant recurrence at index seven expresses the third normalized source moment in
the theta-cusp raw even moments.  Substituting the settled expressions for the first three source
moments gives the closed normalized form, the next entry needed by the size-three leading Hankel
determinant.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Raw form of the index-seven cumulant recurrence. -/
theorem normalizedPrimeArch_recurrence_seven_raw :
    thetaCuspRawEvenMoment 4 -
        7 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 3 +
        210 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 2 -
        2520 * normalizedPrimeArchMoment 2 * thetaCuspRawEvenMoment 1 +
        5040 * normalizedPrimeArchMoment 3 * thetaCuspRawEvenMoment 0 = 0 := by
  have h := normalizedPrimeArchMoment_recursive 3
  norm_num [thetaCuspXiJet, thetaCuspPrimeArchProductJet, Finset.sum_range_succ,
    Nat.factorial, Nat.choose] at h
  have hr : (thetaCuspRawEvenMoment 4 -
      7 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 3 +
      210 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 2 -
      2520 * normalizedPrimeArchMoment 2 * thetaCuspRawEvenMoment 1 +
      5040 * normalizedPrimeArchMoment 3 * thetaCuspRawEvenMoment 0 : ℂ) = 0 := by
    linear_combination h
  exact_mod_cast hr

/-- Closed form of the third source moment in normalized theta-cusp even moments. -/
theorem normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 3 =
      -thetaCuspNormalizedEvenMoment 4 / 5040 +
        thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 / 180 +
        thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ) / 144 -
        thetaCuspNormalizedEvenMoment 1 ^ (2 : ℕ) * thetaCuspNormalizedEvenMoment 2 / 12 +
        thetaCuspNormalizedEvenMoment 1 ^ (4 : ℕ) / 8 := by
  have hr := normalizedPrimeArch_recurrence_seven_raw
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment] at hr
  simp only [thetaCuspNormalizedEvenMoment] at hr ⊢
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne'] at hr ⊢
  nlinarith [hr]

/-- Raw form of the index-nine cumulant recurrence: the fourth source moment against the fifth
theta-cusp raw even moment and the settled lower source moments. -/
theorem normalizedPrimeArch_recurrence_nine_raw :
    -thetaCuspRawEvenMoment 5 +
        9 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 4 -
        504 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 3 +
        15120 * normalizedPrimeArchMoment 2 * thetaCuspRawEvenMoment 2 -
        181440 * normalizedPrimeArchMoment 3 * thetaCuspRawEvenMoment 1 +
        362880 * normalizedPrimeArchMoment 4 * thetaCuspRawEvenMoment 0 = 0 := by
  have h := normalizedPrimeArchMoment_recursive 4
  norm_num [thetaCuspXiJet, thetaCuspPrimeArchProductJet, Finset.sum_range_succ,
    Nat.factorial, Nat.choose] at h
  have hr : (-thetaCuspRawEvenMoment 5 +
      9 * normalizedPrimeArchMoment 0 * thetaCuspRawEvenMoment 4 -
      504 * normalizedPrimeArchMoment 1 * thetaCuspRawEvenMoment 3 +
      15120 * normalizedPrimeArchMoment 2 * thetaCuspRawEvenMoment 2 -
      181440 * normalizedPrimeArchMoment 3 * thetaCuspRawEvenMoment 1 +
      362880 * normalizedPrimeArchMoment 4 * thetaCuspRawEvenMoment 0 : ℂ) = 0 := by
    linear_combination h
  exact_mod_cast hr

/-- The fourth source moment in terms of the fifth theta-cusp normalized even moment and the
settled lower source moments.  This is the entry the size-three leading Hankel determinant needs. -/
theorem normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment :
    normalizedPrimeArchMoment 4 =
      (thetaCuspNormalizedEvenMoment 5 -
          9 * normalizedPrimeArchMoment 0 * thetaCuspNormalizedEvenMoment 4 +
          504 * normalizedPrimeArchMoment 1 * thetaCuspNormalizedEvenMoment 3 -
          15120 * normalizedPrimeArchMoment 2 * thetaCuspNormalizedEvenMoment 2 +
          181440 * normalizedPrimeArchMoment 3 * thetaCuspNormalizedEvenMoment 1) / 362880 := by
  have hr := normalizedPrimeArch_recurrence_nine_raw
  simp only [thetaCuspNormalizedEvenMoment]
  field_simp [thetaCuspRawEvenMoment_zero_pos.ne']
  linarith [hr]

end

end RHTower
