import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanRationalCuspAction
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanDeterminantProfile

/-!
# Rational invariance of the archimedean determinant profile

Determinant-one number-field congruences preserve each real and complex local determinant.  In
particular, passage to any rational rank-two cusp chart leaves the determinant profile unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

omit [NumberField K] in
/-- Local determinant is invariant under rational special-linear congruence. -/
theorem numberFieldArchimedeanDet_rational_smul
    (A : numberFieldArchimedeanPositiveForms K n)
    (g : Matrix.SpecialLinearGroup (Fin n) K)
    (w : InfinitePlace K) :
    numberFieldArchimedeanDet (g • A) w =
      numberFieldArchimedeanDet A w := by
  classical
  rw [numberFieldArchimedeanDet, numberFieldArchimedeanDet]
  split_ifs with hw
  · let G := numberFieldRealMatrixAt ⟨w, hw⟩
      (g : Matrix (Fin n) (Fin n) K)
    have hG : G.det = 1 := by
      rw [numberFieldRealMatrixAt_det, Matrix.SpecialLinearGroup.det_coe, map_one]
    change (G * (A.1.1 ⟨w, hw⟩ : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.conjTranspose G).det = _
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hG]
    simp
  · let wc : {w : InfinitePlace K // w.IsComplex} :=
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
    let G := numberFieldComplexMatrixAt wc
      (g : Matrix (Fin n) (Fin n) K)
    have hG : G.det = 1 := by
      rw [numberFieldComplexMatrixAt_det, Matrix.SpecialLinearGroup.det_coe, map_one]
    change (G * (A.1.2 wc : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.conjTranspose G).det.re = _
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hG]
    simp [wc]

/-- A rank-two rational cusp chart preserves every local determinant. -/
theorem numberFieldArchimedeanDet_cuspChart
    (v : Fin 2 → K) (hv : v ≠ 0)
    (A : numberFieldArchimedeanPositiveForms K 2)
    (w : InfinitePlace K) :
    numberFieldArchimedeanDet (numberFieldRankTwoCuspChart v hv A) w =
      numberFieldArchimedeanDet A w := by
  rw [← numberFieldRankTwoCuspSpecialLinear_smul]
  exact numberFieldArchimedeanDet_rational_smul A
    (numberFieldRankTwoCuspSpecialLinear v hv) w

end

end GaloisForLFunctions.HTGeometry
