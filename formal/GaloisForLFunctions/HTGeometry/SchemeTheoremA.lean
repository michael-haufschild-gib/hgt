import GaloisForLFunctions.HTGeometry.SchemeHorizonExpansion
import GaloisForLFunctions.HTGeometry.SchemeEigenvolumeBoundary

/-!
# The eigenvolume horizon theorem on a scheme, assembled

All conclusions of the horizon theorem are collected here in one statement about an integral
Noetherian scheme with a self-morphism, an eigenvolume, and ramification along its horizon.  The
horizon is a reduced divisor, it is totally invariant, the morphism is unramified off it, and the
ramification coefficient is the pullback difference of the boundary at every place.

The hypotheses are the local order law's ingredients -- the pullback law, the order of the Jacobian
factor and the eigenvolume condition -- together with surjectivity of the divisor map and
ramification along the horizon.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

/-- **The eigenvolume horizon theorem on a scheme.**  Each conjunct is one conclusion of Theorem A:
the order of the eigenvolume takes only the values `0` and `-1`, so the horizon is a reduced
divisor; it is `-1` exactly on the horizon; the horizon is totally invariant; the morphism is
unramified off it; and ramification is the pullback difference of the boundary. -/
theorem scheme_eigenvolume_horizon_theorem
    (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
    {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
    (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
    (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
    (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1)
    (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
    (hexp : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → 1 < e z) :
    (∀ z : CodimOnePoint X, ordAt g z = 0 ∨ ordAt g z = -1) ∧
      (∀ z : CodimOnePoint X, ordAt g z ≠ 0 → ordAt g z = -1) ∧
      (∀ z : CodimOnePoint X, ordAt g z ≠ 0 ↔ ordAt g (F z) ≠ 0) ∧
      (∀ z : CodimOnePoint X, ordAt g z = 0 → e z = 1) ∧
      (∀ z : CodimOnePoint X, (e z : ℤ) - 1 =
        (e z : ℤ) * boundaryCoeff (ordAt g) (F z) - boundaryCoeff (ordAt g) z) := by
  have hram := ramified_cycle_of_forall_one_lt (F := F) hexp
  refine ⟨fun z => schemeEigenvolume_ordAt_eq_zero_or_neg_one F e hPg hJ0 hpull hjac heig hF hone
      hram z,
    fun z hz => schemeEigenvolume_ordAt_eq_neg_one_of_expansion F e hPg hJ0 hpull hjac heig hF hone
      hexp hz,
    fun z => schemeEigenvolume_ordAt_ne_zero_iff_of_expansion F e hPg hJ0 hpull hjac heig hF hone
      hexp z,
    fun z hz => schemeEigenvolume_ramificationIndex_eq_one_off_horizon F e hPg hJ0 hpull hjac heig
      hz,
    fun z => schemeEigenvolume_ramification_eq_pullback_sub F e hPg hJ0 hpull hjac heig hF hone
      hram z⟩

end GaloisForLFunctions.HTGeometry
