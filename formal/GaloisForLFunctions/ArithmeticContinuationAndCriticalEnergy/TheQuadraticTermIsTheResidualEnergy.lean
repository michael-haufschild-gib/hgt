import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCoreDominanceCriterion
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.RenormalizationPreservesDampingContinuation

/-!
# The quadratic term is the residual energy

The deviation row of the accounting is exactly the source minus the constant one, so its pronic
energy *is* the dual residual of the corpus:

`‖dev_ε‖_T² = D_T(ε)`  (`pronicNorm_deviationRow_sq`).

Hence the only unpaid piece of the signed work is bounded by the prime-dilation series times the
residual energy (`abs_workQuadratic_le_residual`), and since the residual and the critical energy are
uniformly comparable — the corpus's renormalisation neutrality — it is bounded by the same series
times `3(1 + E_T(ε))` (`abs_workQuadratic_le_energy`).

So the accounting closes in the corpus's own units: core, two explicit linear functionals, and a
quadratic term that is at most `Θ_ε(T) · (residual energy)`, with
`Θ_ε(T) = Σ_{j ≤ T} Λ(j) j^{-(ε+1/2)}` the explicit prime-dilation series whose convergence
threshold is exactly half damping.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- **The deviation's energy is the dual residual.** -/
theorem pronicNorm_deviationRow_sq (ε : ℝ) (T : ℕ) :
    pronicNorm T (deviationRow ε) ^ 2 = pmPowerDampedDualResidual ε T := by
  rw [pronicNorm_sq, pmPowerDampedDualResidual]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [deviationRow_eq n hn]

/-- The unpaid quadratic term, in the units of the residual energy. -/
theorem abs_workQuadratic_le_residual (ε : ℝ) (T : ℕ) :
    |workQuadratic ε T| ≤
      (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
        pmPowerDampedDualResidual ε T := by
  have h := abs_workQuadratic_le ε T
  rw [pronicNorm_deviationRow_sq] at h
  exact h

/-- The unpaid quadratic term, in the units of the critical energy. -/
theorem abs_workQuadratic_le_energy (ε : ℝ) (T : ℕ) :
    |workQuadratic ε T| ≤
      (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
        (3 * (1 + dampedMobiusEnergy ε T)) := by
  have hcomp := (one_add_damped_energy_comparison ε T).1
  have hS : 0 ≤ ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have h1 : 0 ≤ ArithmeticFunction.vonMangoldt j := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0 : ℝ) ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg j) _
    have h3 : (0 : ℝ) ≤ 1 / Real.sqrt (j : ℝ) := by positivity
    rw [dampedPrimeWeight]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hres : pmPowerDampedDualResidual ε T ≤ 3 * (1 + dampedMobiusEnergy ε T) := by linarith
  exact (abs_workQuadratic_le_residual ε T).trans (mul_le_mul_of_nonneg_left hres hS)

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
