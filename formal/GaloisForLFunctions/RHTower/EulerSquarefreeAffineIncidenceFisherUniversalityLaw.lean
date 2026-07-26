import GaloisForLFunctions.RHTower.EulerSquarefreeAffineFisherCutoffWard
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

/-!
# Euler squarefree-affine incidence--Fisher universality

The full affine Euler source and the squarefree divisor-incidence clock use different
descriptions of the critical geometry.  The former differs negligibly from squarefree
projective Fisher energy, while the latter is asymptotically the same squarefree Fisher energy.
Cancelling that intermediate coordinate gives a direct source-completion invariance law.
-/

open Filter Set

namespace RHTower

noncomputable section

/-- **Euler incidence--Fisher universality law.**  Adding every Euler square channel is
asymptotically invisible even after direct comparison with the squarefree relative-clock
incidence energy. -/
theorem
    tendsto_eulerSquarefreeAffineCriticalProjectiveFisherEnergy_sub_incidenceEnergy :
    Tendsto
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalRelativeClockEnergy sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have h :=
    tendsto_eulerSquarefreeAffineFisherEnergy_sub_squarefree.add
      tendsto_squarefreeMobiusCriticalFisher_sub_incidenceEnergy
  have heq :
      (fun sigma : ℝ =>
        (eulerSquarefreeAffineCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalProjectiveFisherEnergy sigma) +
        (squarefreeMobiusCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalRelativeClockEnergy sigma)) =ᶠ[
        nhdsWithin 1 (Ioi 1)]
      (fun sigma : ℝ =>
        eulerSquarefreeAffineCriticalProjectiveFisherEnergy sigma -
          squarefreeMobiusCriticalRelativeClockEnergy sigma) :=
    Filter.Eventually.of_forall fun sigma => by ring
  simpa only [zero_add] using h.congr' heq

end

end RHTower
