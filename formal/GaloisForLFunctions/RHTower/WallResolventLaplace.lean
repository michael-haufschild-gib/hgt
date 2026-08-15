import GaloisForLFunctions.RHTower.WallGeneratorEquation
import GaloisForLFunctions.HTGeometry.ResolventLaplaceRepresentation

/-!
# The Laplace representation of the shifted Gamma-wall resolvent

Wherever the frequency logarithm and the position together open the numerical floor, the shifted
generator `C(x,L) = B(x+iσ) + L·I` is a unit, and its inverse is the orbit integral of the accretive
semigroup against `e^{-Ls}`:

`C(x,L)^{-1}u = ∫₀^∞ e^{-Ls} e^{-sB(x+iσ)} u ds`.

The abstract representation is available for any generator with a numerical floor; what is needed
here is its instantiation at the literal Gamma-wall generator, whose floor is the logarithmic one.
Uniqueness of the inverse then identifies the orbit integral with the ring inverse, which is the form
the integration by parts produces.

This is the card's `(21)`, and it is what turns the non-decaying first boundary term into a
superposition of semigroup slices, each of which is controlled by Plancherel.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

/-- **`(21)`: the shifted Gamma-wall resolvent is the Laplace transform of its semigroup.**
Wherever the frequency logarithm and the position together open the floor, the inverse of
`C(x,L) = B(x+iσ) + L·I` is the orbit integral of the accretive semigroup against `e^{-Ls}`. -/
theorem invFamily_wallGeneratorShift_eq_laplace {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {x L : ℝ} (hgap : 0 < wallFloor T σ x + L) (u : X) :
    invFamily (wallGeneratorShift T σ L) x u
      = ∫ s in Ioi (0 : ℝ), resolventOrbit (wallGenerator T σ x) L u s := by
  have hB : ∀ v : X, wallFloor T σ x * ‖v‖ ^ 2 ≤ (inner ℂ (wallGenerator T σ x v) v).re :=
    fun v => re_inner_wallGenerator_ge hσ0 hσ1 x v
  have hrep := resolvent_integral_apply hB hgap u
  have hunit : IsUnit (wallGeneratorShift T σ L x) := isUnit_wallGeneratorShift hσ0 hσ1 hgap
  have hcancel : wallGeneratorShift T σ L x * invFamily (wallGeneratorShift T σ L) x = 1 :=
    Ring.mul_inverse_cancel _ hunit
  have hleft : wallGeneratorShift T σ L x (invFamily (wallGeneratorShift T σ L) x u) = u := by
    have := congrArg (fun A : X →L[ℂ] X => A u) hcancel
    simpa using this
  have hinj : Function.Injective (wallGeneratorShift T σ L x) := by
    have hcancel' : invFamily (wallGeneratorShift T σ L) x * wallGeneratorShift T σ L x = 1 :=
      Ring.inverse_mul_cancel _ hunit
    intro a b hab
    have h1 : invFamily (wallGeneratorShift T σ L) x (wallGeneratorShift T σ L x a) = a := by
      have := congrArg (fun A : X →L[ℂ] X => A a) hcancel'
      simpa using this
    have h2 : invFamily (wallGeneratorShift T σ L) x (wallGeneratorShift T σ L x b) = b := by
      have := congrArg (fun A : X →L[ℂ] X => A b) hcancel'
      simpa using this
    rw [← h1, ← h2, hab]
  refine hinj ?_
  rw [hleft]
  exact hrep.symm

end GaloisForLFunctions.RHTower
