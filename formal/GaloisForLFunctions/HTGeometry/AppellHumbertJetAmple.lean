import GaloisForLFunctions.HTGeometry.AppellHumbertLatticeGrowth
import GaloisForLFunctions.HTGeometry.QuasiAbelianPositiveFactorJetAmple

/-!
# A positive Appell--Humbert factor is jet ample of every finite order

`AbePositiveFactorPresentation` carries the polynomial-Gaussian majorant as an analytic field, and
`AbePositiveFactorPresentation.jetAmpleEveryFiniteOrder` turns such a presentation into arbitrary
finite mixed-jet interpolation with one fixed factor.  For the Appell--Humbert factor of a positive
semidefinite Hermitian form the field is a theorem: the reciprocal factor is bounded on compacta,
which is Abe's lattice growth condition with rate zero, and
`gaussianMajorant_of_hasLatticeExponentialGrowth` supplies the majorant from it.

So the presentation exists unconditionally for this class, and with it the interpolation.

* `abePositiveFactorPresentationAppellHumbert`;
* `jetAmpleEveryFiniteOrder_appellHumbert` — **one fixed positive factor interpolates every finite
  jet packet**.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {d : ℕ} {H : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} {χ : (Fin d → ℂ) → ℂ}

/-- **The positive-factor presentation of an Appell--Humbert factor.** -/
def abePositiveFactorPresentationAppellHumbert (hH : IsHermitianForm H)
    (hpos : ∀ y : Fin d → ℂ, 0 ≤ (H y y).re) (hχ : ∀ γ, ‖χ γ‖ = 1)
    (hsemi : IsSemicharacterOn H χ (standardIntegerLattice d)) :
    AbePositiveFactorPresentation.{u} d where
  factor := appellHumbertAutomorphicFactor hH hχ hsemi
  gaussianMajorant :=
    gaussianMajorant_of_hasLatticeExponentialGrowth.{u} _
      (hasLatticeExponentialGrowth_appellHumbert hH hpos hχ hsemi)

/-- **One fixed positive Appell--Humbert factor interpolates every finite jet packet.** -/
theorem jetAmpleEveryFiniteOrder_appellHumbert (hH : IsHermitianForm H)
    (hpos : ∀ y : Fin d → ℂ, 0 ≤ (H y y).re) (hχ : ∀ γ, ‖χ γ‖ = 1)
    (hsemi : IsSemicharacterOn H χ (standardIntegerLattice d)) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u}
      (appellHumbertAutomorphicFactor hH hχ hsemi) :=
  (abePositiveFactorPresentationAppellHumbert.{u} hH hpos hχ hsemi).jetAmpleEveryFiniteOrder

end

end GaloisForLFunctions.HTGeometry
