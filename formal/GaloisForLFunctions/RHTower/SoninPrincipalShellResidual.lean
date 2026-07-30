/-
The canonical positive Sonin principal-shell subtraction.

The one-scale Sonin Gram `L_p^* L_p` has the explicit physical-plus-Fourier shell
`Sigma(a, p*a)` as its Calkin principal part.  Their difference is a canonical compact
self-adjoint residual.  Its adjoint square is therefore a positive compact source operator.
-/
import GaloisForLFunctions.RHTower.SoninEulerEssentialNorm
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal

noncomputable section

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- The canonical principal shell of the one-scale even Sonin Gram operator. -/
def evenSoninPrincipalShell (a p : ℝ) :
    evenSubspace →L[Complex] evenSubspace :=
  evenTwoPolarizationShell a (p * a)

/-- The compact arithmetic residual left after subtracting the universal two-polarization shell
from the one-scale Sonin Gram operator. -/
def evenSoninPrincipalShellResidual
    (a p : ℝ) (hp : 1 < p) : evenSubspace →L[Complex] evenSubspace :=
  evenCentralSoninQuadraticCorner a p p hp hp - evenSoninPrincipalShell a p

/-- The principal-shell residual is compact on the actual even Sonin carrier. -/
theorem evenSoninPrincipalShellResidual_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    IsCompactOperator (evenSoninPrincipalShellResidual a p hp) := by
  have h := evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell a p ha hp
  change IsCompactOperator
    (evenCentralSoninQuadraticCorner a p p hp hp -
      evenTwoPolarizationShell a (p * a))
  simpa only [CompactOperatorEq] using! h

/-- The principal-shell residual is self-adjoint. -/
theorem adjoint_evenSoninPrincipalShellResidual
    (a p : ℝ) (hp : 1 < p) :
    (evenSoninPrincipalShellResidual a p hp)† =
      evenSoninPrincipalShellResidual a p hp := by
  rw [evenSoninPrincipalShellResidual, adjoint_sub_clm,
    adjoint_evenCentralSoninQuadraticCorner,
    evenSoninPrincipalShell, adjoint_evenTwoPolarizationShell]

/-- The positive compact operator canonically associated to the principal-shell residual. -/
def evenSoninPrincipalShellEnergy
    (a p : ℝ) (hp : 1 < p) : evenSubspace →L[Complex] evenSubspace :=
  (evenSoninPrincipalShellResidual a p hp)† *
    evenSoninPrincipalShellResidual a p hp

/-- The residual energy is compact. -/
theorem evenSoninPrincipalShellEnergy_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    IsCompactOperator (evenSoninPrincipalShellEnergy a p hp) := by
  rw [evenSoninPrincipalShellEnergy,
    adjoint_evenSoninPrincipalShellResidual]
  exact (evenSoninPrincipalShellResidual_isCompactOperator a p ha hp).comp_clm _

/-- The residual energy has a nonnegative quadratic form. -/
theorem evenSoninPrincipalShellEnergy_re_inner_nonneg
    (a p : ℝ) (hp : 1 < p) (x : evenSubspace) :
    0 ≤ Complex.re (inner Complex x (evenSoninPrincipalShellEnergy a p hp x)) := by
  change 0 ≤ Complex.re
    (inner Complex x
      (ContinuousLinearMap.adjoint (evenSoninPrincipalShellResidual a p hp)
        (evenSoninPrincipalShellResidual a p hp x)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := Complex) (E := evenSubspace)

/-- Because the residual is self-adjoint, its positive energy is its ordinary square. -/
theorem evenSoninPrincipalShellEnergy_eq_sq
    (a p : ℝ) (hp : 1 < p) :
    evenSoninPrincipalShellEnergy a p hp =
      evenSoninPrincipalShellResidual a p hp *
        evenSoninPrincipalShellResidual a p hp := by
  rw [evenSoninPrincipalShellEnergy,
    adjoint_evenSoninPrincipalShellResidual]

end RHTower
