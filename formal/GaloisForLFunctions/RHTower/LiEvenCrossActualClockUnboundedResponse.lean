import GaloisForLFunctions.RHTower.LiClockVolterraBoundedResponseGrowth
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSpatialGrowth
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra

/-!
# Literal complete-source clock response has arbitrarily high positive values on every tail

Unbounded positive theta-source support forces the Borel kernel to outgrow every fixed
square-root exponential.  The exact complete-source Volterra law therefore precludes any
eventual upper bound on its literal response.
-/

open Set Filter Topology MeasureTheory
namespace RHTower
noncomputable section


/-- The complete-source clock response exceeds every bound at arbitrarily late times,
without an RH premise or a zero-location hypothesis. -/
theorem liEvenCrossActualClockResponse_unboundedAbove_cofinally :
    ∀ M T₀ : ℝ, ∃ t > T₀, M < liEvenCrossActualClockResponse t := by
  exact liClockVolterra_response_unboundedAbove_cofinally_of_fastGrowth
    continuous_liEvenCrossActualClockResponse continuous_liEvenCrossActualClockBorelKernel
    (fun t => (hasDerivAt_liEvenCrossActualClockBorelKernel t).differentiableAt)
    (fun t _ => (liEvenCrossActualClockBorelKernel_pos t).le)
    (fun _ ht => liEvenCrossActualClockResponse_volterra_eq_mul_deriv ht)
    liEvenCrossActualClockBorelKernel_div_exp_sqrt_tendsto_atTop

end
end RHTower
