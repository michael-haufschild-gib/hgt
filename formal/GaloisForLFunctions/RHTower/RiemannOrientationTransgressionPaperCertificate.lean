import GaloisForLFunctions.RHTower.DeningerCalderonWittOrientationTransgressionCompleteness
import GaloisForLFunctions.RHTower.RiemannDenseSourceClosedAdmissionLaw

/-!
# Paper certificate: orientation--transgression and completed admission

This module packages the two load-bearing statements of the paper:

* the all-prime source has one regular orientation factor, while every
  relative class is canonical Green-primitive escape from an admitted
  incidence sector;
* for the completed Xi incidence realization, closed dense-source
  admission with one exact finite trace exists exactly at zero modular
  displacement.

The theorem below is only a dependency-closed conjunction of the two
independently proved laws.  It introduces no additional hypothesis.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/--
The complete paper core: universal source observation/relative
transgression, together with the completed-incidence admission
classification.
-/
theorem riemannOrientationTransgressionPaperCore
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W)
    (hregular :
      ∀ v, F (deningerCalderonWittGlobalOrientedBoundary v) = 0)
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle :
      deningerCalderonWittAlgebraicGlobalExteriorCup w = 0)
    (p q : Nat.Primes) (hpq : p ≠ q)
    (r : XiZeroCopy) (a : ℝ) :
    ((deningerCalderonWittGlobalOrientationConsumerPrimary F +
          deningerCalderonWittGlobalOrientationConsumerSecondary F = F) ∧
      ((∃! phi : ℂ →ₗ[ℂ] W,
          F = phi.comp deningerCalderonWittGlobalOrientedTrace) ∧
        (deningerCalderonWittGlobalRelativeBoundaryClass S w = 0 ↔
          deningerCalderonWittGlobalMilnorGreenRetraction w ∈ S))) ∧
      (Nonempty
          (DeningerCompletedXiClosedHodgeAdmission p q hpq r a) ↔
        a = 0) := by
  exact
    ⟨⟨deningerCalderonWittGlobalOrientationConsumer_primary_add_secondary F,
        deningerCalderonWittGlobalOrientationTransgressionCompleteness
          F hregular S w hcocycle⟩,
      exists_deningerCompletedXiClosedHodgeAdmission_iff p q hpq r a⟩

end

end RHTower
