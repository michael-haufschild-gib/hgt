import GaloisForLFunctions.HTGeometry.CompoundExponential

/-!
# Transporting the matrix exponential to the operator algebra

The star algebra equivalence that sends a matrix to the operator it defines on
`EuclideanSpace ℂ κ` is an isometry for the operator norm, hence continuous, hence commutes with
the exponential.  This is what carries the compound identities — which are proved with matrices —
into the C⋆-algebra where the operator order and the functional calculus live.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Matrix.Norms.L2Operator

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem isometry_toEuclideanCLM :
    Isometry (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ)) :=
  AddMonoidHomClass.isometry_of_norm _ fun A => Matrix.l2_opNorm_toEuclideanCLM A

/-- **The operator of an exponential is the exponential of the operator.** -/
theorem toEuclideanCLM_exp (M : Matrix κ κ ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (NormedSpace.exp M)
      = NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  letI : NormedAlgebra ℝ (Matrix κ κ ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
  letI : NormedAlgebra ℚ (Matrix κ κ ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℝ (EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ) :=
    NormedAlgebra.restrictScalars ℝ ℂ _
  letI : NormedAlgebra ℚ (EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp _ (isometry_toEuclideanCLM (κ := κ)).continuous M

end GaloisForLFunctions.HTGeometry
