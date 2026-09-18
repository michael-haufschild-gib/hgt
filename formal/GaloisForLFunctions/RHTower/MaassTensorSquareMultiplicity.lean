import GaloisForLFunctions.RHTower.RealSphericalHarishChandra
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensor-square compact-weight multiplicity for the Maass model

The completed Maass model is unitary, so its tensor powers are a natural candidate for supplying
the local positivity required by the symmetric-power route.  This module tests that candidate at
the algebraic `K`-finite level.  The exact tensor-square coordinate model has an independent
zero-weight vector for every pair of opposite original weights.  Thus its diagonal compact
zero-weight space has arbitrarily large finite independent families.

The finite symmetric-power exponent packet used by the generic-unitary argument therefore cannot
be obtained from tensor unitarity alone without an additional selection or functorial-lift map.
The theorem here is the local multiplicity obstruction; it makes no global-lift assertion.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section

/-- Finitely supported coordinates for the algebraic tensor square of the spherical model. -/
abbrev SphericalTensorSquareCoordinates := (ℤ × ℤ) →₀ ℂ

/-- Exact algebraic coordinates of the tensor square of the spherical `K`-finite model. -/
def sphericalTensorSquareCoordinateEquiv :
    TensorProduct ℂ SphericalKFiniteModel SphericalKFiniteModel ≃ₗ[ℂ]
      SphericalTensorSquareCoordinates :=
  finsuppTensorFinsupp' ℂ ℤ ℤ

@[simp] theorem sphericalTensorSquareCoordinateEquiv_pure (m n : ℤ) :
    sphericalTensorSquareCoordinateEquiv
      (Finsupp.single m (1 : ℂ) ⊗ₜ[ℂ] Finsupp.single n (1 : ℂ)) =
      Finsupp.single (m, n) 1 := by
  simp [sphericalTensorSquareCoordinateEquiv]

/-- A one-dimensional weighted insertion into tensor-square coordinates. -/
def pairWeightedSingle (p : ℤ × ℤ) (a : ℂ) : ℂ →ₗ[ℂ] SphericalTensorSquareCoordinates where
  toFun z := Finsupp.single p (a * z)
  map_add' x y := by
    ext q
    by_cases hpq : p = q <;> simp [hpq, mul_add]
  map_smul' c z := by
    ext q
    by_cases hpq : p = q
    · simp [hpq]
      ring
    · simp [hpq]

/-- The diagonal compact-weight generator in exact tensor-square coordinates. -/
def tensorDiagonalHCoordinates :
    SphericalTensorSquareCoordinates →ₗ[ℂ] SphericalTensorSquareCoordinates :=
  Finsupp.lsum ℂ (fun p ↦ pairWeightedSingle p (2 * ((p.1 + p.2 : ℤ) : ℂ)))

@[simp] theorem tensorDiagonalHCoordinates_single (p : ℤ × ℤ) (z : ℂ) :
    tensorDiagonalHCoordinates (Finsupp.single p z) =
      Finsupp.single p (2 * ((p.1 + p.2 : ℤ) : ℂ) * z) := by
  simp [tensorDiagonalHCoordinates, pairWeightedSingle]

/-- The diagonal compact-weight operator on the tensor square, transported through its exact
finitely-supported coordinate equivalence. -/
def sphericalTensorSquareDiagonalH :
    TensorProduct ℂ SphericalKFiniteModel SphericalKFiniteModel →ₗ[ℂ]
      TensorProduct ℂ SphericalKFiniteModel SphericalKFiniteModel :=
  sphericalTensorSquareCoordinateEquiv.symm.toLinearMap.comp
    (tensorDiagonalHCoordinates.comp sphericalTensorSquareCoordinateEquiv.toLinearMap)

/-- Tensor basis weights add under the diagonal compact generator. -/
theorem sphericalTensorSquareDiagonalH_pure (m n : ℤ) :
    sphericalTensorSquareDiagonalH
      (Finsupp.single m (1 : ℂ) ⊗ₜ[ℂ] Finsupp.single n (1 : ℂ)) =
      (2 * ((m + n : ℤ) : ℂ)) •
        (Finsupp.single m (1 : ℂ) ⊗ₜ[ℂ] Finsupp.single n (1 : ℂ)) := by
  apply sphericalTensorSquareCoordinateEquiv.injective
  simp only [sphericalTensorSquareDiagonalH, LinearMap.comp_apply, map_smul]
  simp [sphericalTensorSquareCoordinateEquiv, tensorDiagonalHCoordinates, pairWeightedSingle]

/-- Every pair of opposite original compact weights is zero-weight for the diagonal tensor action. -/
theorem sphericalTensorSquareDiagonalH_opposite_pure (m : ℤ) :
    sphericalTensorSquareDiagonalH
      (Finsupp.single m (1 : ℂ) ⊗ₜ[ℂ] Finsupp.single (-m) (1 : ℂ)) = 0 := by
  rw [sphericalTensorSquareDiagonalH_pure]
  simp

/-- A coordinate basis for the diagonal zero-weight sector. -/
def tensorZeroWeightBasis (m : ℤ) : SphericalTensorSquareCoordinates :=
  Finsupp.single (m, -m) 1

/-- The coordinate zero-weight basis lies in the diagonal compact kernel. -/
theorem tensorDiagonalHCoordinates_zeroWeightBasis (m : ℤ) :
    tensorDiagonalHCoordinates (tensorZeroWeightBasis m) = 0 := by
  simp [tensorZeroWeightBasis]

/-- Opposite-weight coordinates are linearly independent. -/
theorem tensorZeroWeightBasis_linearIndependent :
    LinearIndependent ℂ tensorZeroWeightBasis := by
  exact (Finsupp.linearIndependent_single_one ℂ (ℤ × ℤ)).comp
    (fun m : ℤ => (m, -m)) (by
      intro m n h
      exact congrArg Prod.fst h)

/-- The tensor-square diagonal compact kernel contains independent families of every finite size. -/
theorem tensorDiagonalHCoordinates_kernel_has_independent_family (r : ℕ) :
    ∃ v : Fin r → SphericalTensorSquareCoordinates,
      LinearIndependent ℂ v ∧ ∀ j, tensorDiagonalHCoordinates (v j) = 0 := by
  refine ⟨fun j => tensorZeroWeightBasis (j : ℤ), ?_, ?_⟩
  · exact tensorZeroWeightBasis_linearIndependent.comp (fun j : Fin r => (j : ℤ))
      (by intro i j h; exact Fin.ext (Int.ofNat_inj.mp h))
  · intro j
    exact tensorDiagonalHCoordinates_zeroWeightBasis (j : ℤ)

end
end GaloisForLFunctions.RHTower
