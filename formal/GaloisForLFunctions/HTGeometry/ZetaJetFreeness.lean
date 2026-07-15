import GaloisForLFunctions.HTGeometry.HypertranscendentalFunctionJetFreeness
import GaloisForLFunctions.RHTower.ZetaHypertranscendental

/-!
# The Riemann zeta derivative jets are algebraically independent

This leaf instantiates the generic free-jet consequence of function hypertranscendence with the
repository's unconditional theorem for the Riemann zeta function. It is the exact formal bridge
from the analytic zeta theorem to free-jet HT geometry. No horizon fixed-field claim is added.
-/

namespace GaloisForLFunctions

/-- Every finite initial family of Riemann-zeta derivative functions is algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_riemannZeta_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) riemannZeta) :=
  hypertranscendental_riemannZeta.algebraicIndependent_initialJets n

/-- **Riemann-zeta free jets.** All derivative functions of `ζ` are algebraically independent
over `ℂ`. -/
theorem algebraicIndependent_riemannZeta_iteratedDeriv :
    AlgebraicIndependent ℂ (fun j : ℕ => iteratedDeriv j riemannZeta) :=
  hypertranscendental_riemannZeta.algebraicIndependent_iteratedDeriv

end GaloisForLFunctions
