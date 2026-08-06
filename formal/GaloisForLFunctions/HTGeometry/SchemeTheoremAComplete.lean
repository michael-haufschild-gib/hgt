import GaloisForLFunctions.HTGeometry.NumericalClassExpansion
import GaloisForLFunctions.HTGeometry.SchemeTheoremA

/-!
# The eigenvolume horizon theorem with expansion from the numerical class

The horizon theorem is stated here with its expansion step in the form the argument uses: the
components of the horizon have nonzero numerical classes, those classes are eigenvectors of the
pullback with eigenvalue the ramification index, and every eigenvalue of the pullback exceeds one
in modulus.

All conclusions follow: the horizon is a reduced divisor, it is exactly where the order is `-1`,
it is totally invariant, the morphism is unramified off it, and ramification is the pullback
difference of the boundary.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

/-- **The eigenvolume horizon theorem, with expansion supplied by the numerical class.** -/
theorem scheme_eigenvolume_horizon_theorem_of_numerical_class
    (F : CodimOnePoint X → CodimOnePoint X) (e : CodimOnePoint X → ℕ)
    {g J Pg : X.functionField} (hPg : Pg ≠ 0) (hJ0 : J ≠ 0)
    (hpull : ∀ z : CodimOnePoint X, Scheme.ord Pg z.1 = (e z : ℤ) * Scheme.ord g (F z).1)
    (hjac : ∀ z : CodimOnePoint X, Scheme.ord J z.1 = (e z : ℤ) - 1)
    (heig : ∀ z : CodimOnePoint X, Scheme.ord (Pg * J) z.1 = Scheme.ord g z.1)
    (hF : Function.Surjective F) (hone : ∀ z : CodimOnePoint X, 1 ≤ e z)
    {N : Type*} [AddCommGroup N] [Module ℝ N] (T : N →ₗ[ℝ] N)
    (hspec : ∀ (μ : ℝ) (w : N), w ≠ 0 → T w = μ • w → 1 < |μ|)
    (cls : CodimOnePoint X → N)
    (hnz : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → cls z ≠ 0)
    (hact : ∀ z : CodimOnePoint X, ordAt g z ≠ 0 → T (cls z) = (e z : ℝ) • cls z) :
    (∀ z : CodimOnePoint X, ordAt g z = 0 ∨ ordAt g z = -1) ∧
      (∀ z : CodimOnePoint X, ordAt g z ≠ 0 → ordAt g z = -1) ∧
      (∀ z : CodimOnePoint X, ordAt g z ≠ 0 ↔ ordAt g (F z) ≠ 0) ∧
      (∀ z : CodimOnePoint X, ordAt g z = 0 → e z = 1) ∧
      (∀ z : CodimOnePoint X, (e z : ℤ) - 1 =
        (e z : ℤ) * boundaryCoeff (ordAt g) (F z) - boundaryCoeff (ordAt g) z) :=
  scheme_eigenvolume_horizon_theorem F e hPg hJ0 hpull hjac heig hF hone
    (forall_one_lt_of_numerical_class T hspec e g cls hnz hact)

end GaloisForLFunctions.HTGeometry
