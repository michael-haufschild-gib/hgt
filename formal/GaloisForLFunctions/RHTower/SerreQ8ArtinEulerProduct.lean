import GaloisForLFunctions.RHTower.SerreQ8ArtinGaloisRealization

/-!
# Finite-place Artin Euler product of Serre's literal quaternionic field

The literal radical field constructed in the Serre `Q₈` chain is a number
field, is Galois over `ℚ`, and has its exact two-dimensional symplectic Artin
representation.  This module joins those three already proved facts to the
canonical finite-place Artin Euler product.

The resulting product is an unconditional source object: it is holomorphic
and nonvanishing on its absolute-convergence half-plane.  It is deliberately
not called a completed Artin `L`-function and no root-number assertion is
made: a continuation together with the genuine global epsilon-factor product
remains a separate arithmetic theorem.
-/

open scoped NumberField

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => SerreQ8TopField

noncomputable local instance serreQ8EulerFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance serreQ8EulerFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis serreQ8_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance serreQ8EulerFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2

noncomputable local instance serreQ8EulerFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

local instance serreQ8CharZero : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance serreQ8NumberField : NumberField K3 := NumberField.mk

noncomputable local instance serreQ8IsGalois : IsGalois ℚ K3 := serreQ8_isGalois

/-- The canonical finite-place Artin Euler product of the literal Serre
quaternionic number field and its literal symplectic representation. -/
noncomputable def serreQ8ArtinEulerProduct : ℂ → ℂ :=
  deningerQ8ArtinEulerProduct (K := ℚ) (L := K3) (G := Gal(K3/ℚ))
    serreQ8_galoisEquivQ8

/-- The literal Serre `Q₈` Artin Euler product is holomorphic throughout its
absolute-convergence half-plane. -/
theorem differentiableOn_serreQ8ArtinEulerProduct :
    DifferentiableOn ℂ serreQ8ArtinEulerProduct
      GaloisForLFunctions.artinEulerAbsoluteHalfPlane := by
  exact differentiableOn_deningerQ8ArtinEulerProduct
    (K := ℚ) (L := K3) (G := Gal(K3/ℚ)) serreQ8_galoisEquivQ8

/-- The literal Serre `Q₈` Artin Euler product has no zero in its
absolute-convergence half-plane. -/
theorem serreQ8ArtinEulerProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    {s : ℂ} (hs : s ∈ GaloisForLFunctions.artinEulerAbsoluteHalfPlane) :
    serreQ8ArtinEulerProduct s ≠ 0 := by
  exact deningerQ8ArtinEulerProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    (K := ℚ) (L := K3) (G := Gal(K3/ℚ)) serreQ8_galoisEquivQ8 hs

end

end RHTower
