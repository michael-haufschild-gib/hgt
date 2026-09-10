import GaloisForLFunctions.HTGeometry.GomesPolynomialReflectionJointCommutant
import GaloisForLFunctions.HTGeometry.SuperPoincarePolynomialReflection
import GaloisForLFunctions.HTGeometry.ComplexExponentialPolynomial
import GaloisForLFunctions.RHTower.LiEvenSquareReflectionBlindnessNoGo

/-!
# Formal matrix reconstruction of the corpus's three actual reflections

The same closed theorem applies to functional-equation reflection P(1-X),
exponential-polynomial negation P(-X), and hard-edge reflection P(4-X). The full
joint commutant classification also applies to the actual supertranslation
reflection endomorphism.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Every affine reflection is reconstructed exactly from its formal matrix on residue chains. -/
theorem gomesPolynomialReflectionEnd_matrix_reconstruction (c : K) (P : K[X]) :
    gomesPolynomialReflectionEnd K c P =
      (gomesPolynomialResidueChainEquiv K 2).symm
        (fun i => ∑ j, gomesFormalSeriesPolynomialOperator K (gomesPolynomialReflectionMatrix K c i j)
          (gomesPolynomialResidueChainEquiv K 2 P j)) := by
  have h := congrArg (fun E : GomesPolynomialDerivativePowerCommutant K 2 => E.val P)
    ((gomesPolynomialDerivativePowerCommutantEquiv K 2).symm_apply_apply
      (gomesPolynomialReflectionSymmetry K c))
  rw [gomesPolynomialDerivativePowerCommutantEquiv_symm_apply] at h
  exact h.symm

/-- Actual functional-equation reflection has the exact center-one formal matrix reconstruction. -/
theorem gomesReflectPolyEnd_matrix_reconstruction (P : ℂ[X]) :
    reflectPolyEnd P =
      (gomesPolynomialResidueChainEquiv ℂ 2).symm
        (fun i => ∑ j, gomesFormalSeriesPolynomialOperator ℂ (gomesPolynomialReflectionMatrix ℂ 1 i j)
          (gomesPolynomialResidueChainEquiv ℂ 2 P j)) := by
  have h := gomesPolynomialReflectionEnd_matrix_reconstruction ℂ 1 P
  rw [gomesPolynomialReflectionEnd_apply] at h
  change P.comp (1 - X) = _
  simpa only [map_one] using h

/-- Existing exponential-polynomial negation has the exact diagonal parity reconstruction. -/
theorem gomesCExpPolyNegComp_matrix_reconstruction (P : ℂ[X]) :
    CExpPoly.negComp P =
      (gomesPolynomialResidueChainEquiv ℂ 2).symm
        (fun i => ∑ j, gomesFormalSeriesPolynomialOperator ℂ
          ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) i j)
          (gomesPolynomialResidueChainEquiv ℂ 2 P j)) := by
  have h := gomesPolynomialReflectionEnd_matrix_reconstruction ℂ 0 P
  rw [gomesPolynomialReflectionEnd_apply, gomesPolynomialReflectionMatrix_zero] at h
  simpa only [map_zero, zero_sub, CExpPoly.negComp] using h

/-- Existing hard-edge reflection has the exact center-four formal matrix reconstruction. -/
theorem gomesLiHardEdgeReflection_matrix_reconstruction (P : ℂ[X]) :
    RHTower.liHardEdgeReflection P =
      (gomesPolynomialResidueChainEquiv ℂ 2).symm
        (fun i => ∑ j, gomesFormalSeriesPolynomialOperator ℂ (gomesPolynomialReflectionMatrix ℂ 4 i j)
          (gomesPolynomialResidueChainEquiv ℂ 2 P j)) :=
  gomesPolynomialReflectionEnd_matrix_reconstruction ℂ 4 P

/-- The full shared commutant of the corpus's actual derivative and functional-equation reflection. -/
theorem gomesActualDerivativeReflectPolyEnd_joint_commutant (E : Module.End ℂ ℂ[X]) :
    (Commute E polynomialDerivativeEnd ∧ Commute E reflectPolyEnd) ↔
      ∃ F : PowerSeries ℂ, E = gomesEvenFormalPolynomialOperator ℂ F := by
  have hr : gomesPolynomialReflectionEnd ℂ 1 = reflectPolyEnd := by
    apply LinearMap.ext
    intro P
    rw [gomesPolynomialReflectionEnd_apply]
    change P.comp (C 1 - X) = P.comp (1 - X)
    rw [map_one]
  have hD : polynomialDerivativeEnd = (Polynomial.derivative : Module.End ℂ ℂ[X]) := by
    apply LinearMap.ext
    intro P
    rfl
  rw [hD]
  simpa only [hr] using gomesPolynomialDerivativeReflection_joint_commutant ℂ 1 E

end GaloisForLFunctions.HTGeometry
