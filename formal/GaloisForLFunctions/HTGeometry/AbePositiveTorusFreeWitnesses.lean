import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedFactorExtension

/-!
# Abe positivity is exactly having a presentation

The torusless positivity interface asks for a nonempty tower of damped extensions over an Abe
positive presentation.  The base constructor supplies one from a presentation alone, and one more
damped extension step carries positivity up the tower — so the interface is literally "reachable
from an Abe presentation", and the analytic content sits entirely in the presentation's
polynomial-Gaussian majorant.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An Abe positive presentation makes its own factor positive torusless.** -/
theorem isAbePositiveTorusless_of_presentation {d : ℕ}
    (P : AbePositiveFactorPresentation.{u} d) :
    AutomorphicFactor.IsAbePositiveTorusless.{u} P.factor :=
  ⟨AbePositiveFactorTower.base P⟩

/-- Positivity is carried up every damped extension step. -/
theorem isAbePositiveTorusless_extension {d : ℕ}
    {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (hlower : AutomorphicFactor.IsAbePositiveTorusless.{u} lower)
    (step : AbeDampedFactorExtension.{u} lower upper) :
    AutomorphicFactor.IsAbePositiveTorusless.{u} upper :=
  ⟨AbePositiveFactorTower.extension hlower.some step⟩

end GaloisForLFunctions.HTGeometry
