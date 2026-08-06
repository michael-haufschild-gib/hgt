import GaloisForLFunctions.HTGeometry.CommonPeriodIterate
import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeHorizon

/-!
# The horizon becomes a union of fixed divisors under an iterate

On a quasi-compact integral Noetherian scheme the divisorial support of a rational function is
finite, so the components of the horizon are permuted by a finite permutation and a single iterate
fixes them all.  This is the passage to an iterate that lets the horizon be treated as a set of
fixed components.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

/-- **After replacing the morphism by an iterate, every component of the horizon is fixed.** -/
theorem exists_iterate_fixing_horizon (F : CodimOnePoint X → CodimOnePoint X)
    (e : CodimOnePoint X → ℕ) (g : X.functionField)
    (hF : Function.Surjective F)
    (hlaw : ∀ z : CodimOnePoint X, ordAt g z + 1 = (e z : ℤ) * (ordAt g (F z) + 1)) :
    ∃ N, 0 < N ∧ ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → F^[N] z = z :=
  exists_iterate_fixing_support hF hlaw (finite_ordAt_support g)

end GaloisForLFunctions.HTGeometry
