import GaloisForLFunctions.RHTower.ThetaFixedPointMomentProductFiberUniversalityLaw
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCenteredSeamNoGo

/-!
# Theta product-fibre fixed-point centre-escape universality

At the reflection fixed point, sending the common tail centre to infinity does not erase the
corrected seam.  It converges to the explicit positive endpoint Gibbs current on every positive
product fibre.
-/

open Complex Real Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Escaping every common tail centre sends the complete corrected seam to the explicit fixed-point
Gibbs current, not to zero. -/
theorem tendsto_thetaProductFiberCenteredCorrectedPhaseSeamCurrent_atTop_endpointGibbsSum
    (k : ℕ) :
    Tendsto (fun c : ℝ =>
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c 0)
      atTop
      (nhds (∑ q ∈ thetaPositiveFactorPairs k,
        (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) *
          ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
            Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ))))) := by
  rw [← thetaProductFiberActualPhaseCurrent_zero_eq_endpointGibbsSum]
  exact tendsto_thetaProductFiberCenteredCorrectedPhaseSeamCurrent_atTop_actual k (by simp)

/-- **Fixed-point centre-escape law.**  Every positive product fibre has a strictly positive
explicit Gibbs current, and the corrected common-centre seam converges to that current. -/
theorem thetaProductFiber_fixedPoint_centerEscape_positiveGibbsUniversality
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun c : ℝ =>
      thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c 0)
      atTop
      (nhds (∑ q ∈ thetaPositiveFactorPairs k,
        (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) *
          ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
            Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ))))) ∧
      0 < ∑ q ∈ thetaPositiveFactorPairs k,
        (4 * Real.exp (-Real.pi * ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) *
          ((8 * Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) - 2) *
            Real.exp (-Real.pi * ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  refine ⟨tendsto_thetaProductFiberCenteredCorrectedPhaseSeamCurrent_atTop_endpointGibbsSum k, ?_⟩
  rw [← thetaProductFiberActualPhaseCurrent_zero_eq_endpointGibbsSum]
  exact thetaProductFiberActualPhaseCurrent_zero_pos hk

end

end RHTower
