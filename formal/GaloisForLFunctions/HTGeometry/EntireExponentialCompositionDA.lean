import GaloisForLFunctions.HTGeometry.MeroExponentialGauge
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge

/-!
# The exponential of a differentially algebraic entire function

If `P` is entire and satisfies an algebraic differential equation, then so does `exp ∘ P`: in the
meromorphic differential field of the plane the realization of `exp ∘ P` obeys the homogeneous
first-order relation `y′ = P′·y`, and differential algebraicity is transitive.  Transporting the
conclusion back through the jet bridge gives a statement about functions.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential UnivMeroFieldInstances

noncomputable section

/-- **The exponential of a differentially algebraic entire function is differentially
algebraic.** -/
theorem differentiallyAlgebraic_cexp_comp {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (Set.univ : Set ℂ)) (hDA : DifferentiallyAlgebraic P) :
    DifferentiallyAlgebraic (fun z => Complex.exp (P z)) := by
  refine differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hP.cexp ?_
  exact differentialAlgebraicOver_analyticMeroElement_exp P hP
    (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hP hDA)

end

end GaloisForLFunctions.HTGeometry
