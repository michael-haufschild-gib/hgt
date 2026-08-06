import GaloisForLFunctions.HTGeometry.RamificationExpansionCriterion
import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeHorizon

/-!
# The scheme horizon under pointwise expansion

On a scheme the cycle hypothesis of the horizon theorem is discharged by expansion at each place of
the horizon: a component fixed by an iterate already carries ramification at the zeroth step.  So
the reduced-divisor conclusion needs only that the morphism is ramified along every component of
the horizon, with no condition on the cycle structure.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

/-- **The horizon of a scheme eigenvolume is reduced under pointwise expansion.** -/
theorem schemeEigenvolume_ordAt_eq_neg_one_of_expansion
    (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
    {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
    (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
    (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
    (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1)
    (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
    (hexp : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → 1 < e z)
    {z : CodimOnePoint X} (hz : ordAt g z ≠ 0) :
    ordAt g z = -1 :=
  eigenvolumeOrder_eq_neg_one_of_forall_one_lt hF hone
    (schemeEigenvolume_shiftLaw F e hPg hJ0 hpull hjac heig)
    (finite_ordAt_support g) hexp hz

/-- **The horizon of a scheme eigenvolume is totally invariant under pointwise expansion.** -/
theorem schemeEigenvolume_ordAt_ne_zero_iff_of_expansion
    (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
    {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
    (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
    (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
    (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1)
    (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
    (hexp : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → 1 < e z)
    (z : CodimOnePoint X) :
    ordAt g z ≠ 0 ↔ ordAt g (F z) ≠ 0 :=
  schemeEigenvolume_ordAt_ne_zero_iff F e hPg hJ0 hpull hjac heig hF hone
    (ramified_cycle_of_forall_one_lt hexp) z

end GaloisForLFunctions.HTGeometry
