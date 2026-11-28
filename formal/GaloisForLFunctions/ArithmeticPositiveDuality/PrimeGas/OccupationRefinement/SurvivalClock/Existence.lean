import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock.Calibration

/-! # Existence and uniqueness of the probability clock at every prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock

open scoped NNReal
open ModeCapacities

/-- The elementary probability curve fixed by the count of surviving residues. -/
def residueClock (p : Nat.Primes) : Curve := fun t =>
  ⟨survive t p.val, (survive_pos t p).le,
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.property)
      (Real.log_nonneg (Nat.one_lt_cast.mpr p.property.one_lt : (1:ℝ)<p.val).le))⟩

theorem residueClock_calibrated (p : Nat.Primes) : calibrated p (residueClock p) :=
  (calibrated_iff p _).mpr fun _ => rfl

/-- Unit-time counting specifies a unique family of real-time probability
curves simultaneously on all prime modes. -/
theorem unique_family : ∃! q : Nat.Primes → Curve, ∀ p, calibrated p (q p) := by
  refine ⟨residueClock,residueClock_calibrated,?_⟩
  intro q h
  funext p t
  exact Subtype.ext ((calibrated_iff p (q p)).mp (h p) t)

#print axioms residueClock_calibrated
#print axioms unique_family

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock
