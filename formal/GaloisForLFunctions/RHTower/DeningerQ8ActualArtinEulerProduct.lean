import GaloisForLFunctions.RHTower.DeningerQ8ArtinGaloisRealization
import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneGaloisIdentification

/-!
# Finite-place Artin Euler product of the source-authenticated quaternionic field

The literal field
`ℚ(√5, √41, √((5 + √5) * (41 + 6 * √41)))` is the quaternionic field
selected in Example 1.3(ii) of Shankar--Södergren--Templier.  This module
joins its already-formal degree-eight, Galois, and `Q₈`-identification facts
to the canonical finite-place Artin Euler product.

The source asserts that the associated two-dimensional Artin representation
has root number `-1`; this file does not turn that citation into a theorem.
It proves only the unconditional finite-place source object and its
absolute-half-plane properties.  A literal global epsilon-factor calculation
remains a separate arithmetic obligation.
-/

open scoped NumberField

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

noncomputable local instance deningerQ8ActualEulerFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance deningerQ8ActualEulerFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance deningerQ8ActualEulerFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2

noncomputable local instance deningerQ8ActualEulerFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

local instance deningerQ8ActualEulerCharZero : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance deningerQ8ActualEulerNumberField : NumberField K3 := NumberField.mk

noncomputable local instance deningerQ8ActualEulerIsGalois : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

/-- The canonical finite-place Artin Euler product attached to the literal
quaternionic field selected by the source and its literal symplectic
representation. -/
noncomputable def deningerQ8ActualArtinEulerProduct : ℂ → ℂ :=
  deningerQ8ArtinEulerProduct (K := ℚ) (L := K3) (G := Gal(K3/ℚ))
    deningerQ8RootNumberNegOne_galoisEquivQ8

/-- The source-authenticated field's finite-place Artin Euler product is
holomorphic in the absolute-convergence half-plane. -/
theorem differentiableOn_deningerQ8ActualArtinEulerProduct :
    DifferentiableOn ℂ deningerQ8ActualArtinEulerProduct
      GaloisForLFunctions.artinEulerAbsoluteHalfPlane := by
  exact differentiableOn_deningerQ8ArtinEulerProduct
    (K := ℚ) (L := K3) (G := Gal(K3/ℚ)) deningerQ8RootNumberNegOne_galoisEquivQ8

/-- The source-authenticated field's finite-place Artin Euler product has no
zero in the absolute-convergence half-plane. -/
theorem deningerQ8ActualArtinEulerProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    {s : ℂ} (hs : s ∈ GaloisForLFunctions.artinEulerAbsoluteHalfPlane) :
    deningerQ8ActualArtinEulerProduct s ≠ 0 := by
  exact deningerQ8ArtinEulerProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    (K := ℚ) (L := K3) (G := Gal(K3/ℚ)) deningerQ8RootNumberNegOne_galoisEquivQ8 hs

end

end RHTower
