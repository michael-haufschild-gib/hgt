import GaloisForLFunctions.RHTower.EulerDeletionCanonicalClockResolvent

/-!
# Exact clock refinement for Euler deletion

Adjacent EDQ history clocks refine by one exact integral factor. At a genuine
terminal cutoff this factor splits the lower canonical beta resolvent into
blocks indexed by the upper clock quotient.
-/

noncomputable section

namespace RHTower.DeletionResidueMartingale

/-- Adding the next modulus replaces the history clock by its literal lcm with that modulus. -/
theorem clock_succ_eq_lcm (n : ℕ) :
    clock (n + 1) = Nat.lcm (clock n) (n + 1) := by
  apply Nat.dvd_antisymm
  · unfold clock
    apply Finset.lcm_dvd
    intro k hk
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) with hkn | hkn
    · subst k
      exact Nat.dvd_lcm_right _ _
    · exact (dvd_clock (by omega) (by omega)).trans (Nat.dvd_lcm_left _ _)
  · apply Nat.lcm_dvd
    · exact clock_dvd (Nat.le_succ n)
    · exact dvd_clock (by omega) le_rfl

/-- The number of lower-clock source samples factors into upper-clock samples and one exact
clock-refinement block. -/
theorem clock_quotient_factorization (l N : ℕ) (hlN : l < N) :
    clock N / clock l =
      (clock N / clock (l + 1)) * (clock (l + 1) / clock l) := by
  apply Nat.eq_of_mul_eq_mul_right (clock_pos l)
  rw [Nat.div_mul_cancel (clock_dvd (Nat.le_of_lt hlN)),
    Nat.mul_assoc, Nat.div_mul_cancel (clock_dvd (Nat.le_succ l)),
    Nat.div_mul_cancel (clock_dvd (Nat.succ_le_of_lt hlN))]

/-- The canonical lower resolvent has exactly the upper quotient times the new history-block
size. This is a count identity, leaving all source signs in place for the later block reindexing. -/
theorem canonicalClockRatio_eq_refinement_mul (l N : ℕ) (hlN : l < N) :
    canonicalClockRatio N l = canonicalClockRatio N (l + 1) *
      (clock (l + 1) / clock l) := by
  rw [canonicalClockRatio_eq_div_of_le N l (Nat.le_of_lt hlN),
    canonicalClockRatio_eq_div_of_le N (l + 1) (Nat.succ_le_of_lt hlN),
    clock_quotient_factorization l N hlN]

end RHTower.DeletionResidueMartingale
