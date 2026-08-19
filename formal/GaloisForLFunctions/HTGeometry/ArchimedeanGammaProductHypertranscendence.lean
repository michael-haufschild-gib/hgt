import GaloisForLFunctions.HTGeometry.GammaSameSignProductBoundary
import GaloisForLFunctions.HTGeometry.MeroExponentialGauge
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# The finite archimedean Gamma product is hypertranscendental

`G(s) = e^{α s}·∏_j Γ(λ_j s + μ_j)` with positive commensurable scales is hypertranscendental over
`ℂ(s)`.  The exponential is a differentially algebraic gauge and cancels out; the Gamma part is the
positive commensurable-family theorem, which needs no separation hypothesis at all — the Gauss
refinement is allowed to collide arbitrarily.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

open scoped UnivMeroFieldInstances

set_option maxHeartbeats 1000000 in
/-- **The archimedean product of the finite Gamma-product boundary law is hypertranscendental.**
Positive integer scales, arbitrary complex shifts, positive charges, and an arbitrary linear
exponential gauge. -/
theorem hypertranscendentalOver_archimedeanGammaProductMero {d : ℕ} (hd : 0 < d)
    (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 < m i)
    (α : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaNatScaleFamilyMero n a m
        * HTGeometry.analyticMeroElement (fun z : ℂ => Complex.exp (α * z))
            (HTGeometry.analyticOnNhd_expLinear α)) := by
  rw [HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (HTGeometry.differentialAlgebraicOver_analyticMeroElement_expLinear α)
    (HTGeometry.analyticMeroElement_exp_ne_zero (fun z : ℂ => α * z)
      (analyticOnNhd_const.mul analyticOnNhd_id))]
  exact hypertranscendentalOver_gammaNatScaleFamilyMero_of_pos hd n a m hn hm

end

end GaloisForLFunctions
