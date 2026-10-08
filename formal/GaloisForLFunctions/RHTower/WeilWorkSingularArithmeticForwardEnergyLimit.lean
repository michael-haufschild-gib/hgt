import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticLogMomentLimit
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardCoefficients

/-!
# Convergence of the actual forward coefficient energy

Full Weil positivity supplies the exact logarithmic moment ceiling. The
monotone primitive argument turns it into a limit, without an additional
regularity, coefficient sign, or convergence premise.
-/

open Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- The critical weighted energy has an actual finite limit. -/
theorem exists_forwardCoeff_energy_limit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 ≤ K ∧ Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 K) := by
  obtain ⟨C, _, hC⟩ := exists_forwardCoeff_log_moment_le hW
  apply LogMoment.exists_mass_limit (w := fun n => ‖forwardCoeff lam n‖ ^ 2 / n)
    (C := C) (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
  intro N hN
  simpa only [LogMoment.moment, LogMoment.mass, ← mul_div_assoc] using hC N hN

end RHTower.WeilSingularArithmetic
