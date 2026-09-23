import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicOrientationLedger

/-!
# Four-moment factorization of the literal parabolic cross kernel

The complete matched--quantile cross-cell source factors through four source-moment directions.
No prime--polar displacement debt is dropped.  Therefore this parabolic carrier alone cannot be
the growing-rank coercive Gram required by the CCM-FU/RH chain.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open Matrix

/-- Literal all-pair matched--quantile parabolic cross kernel on a finite physical head. -/
def ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix (K : ℕ) :
    Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ :=
  fun m n => ccmActualHeadMatchedQuantileParabolicCrossKernelValue (m.val + 2) (n.val + 2)

def ccmActualHeadMatchedQuantileParabolicCrossWeight (K : ℕ) : Fin (K + 1) → ℝ :=
  fun m => criticalMellinAtomWeight (m.val + 2)

def ccmActualHeadMatchedQuantileParabolicCrossCentroid (K : ℕ) : Fin (K + 1) → ℝ :=
  fun m => criticalMellinAtomWeight (m.val + 2) *
    ccmActualHeadMatchedPolarCentroid (m.val + 2)

def ccmActualHeadMatchedQuantileParabolicCrossDisplacement (K : ℕ) : Fin (K + 1) → ℝ :=
  fun m => criticalMellinAtomWeight (m.val + 2) *
    ccmActualHeadMatchedQuantilePolarDisplacement (m.val + 2)

def ccmActualHeadMatchedQuantileParabolicCrossEnergy (K : ℕ) : Fin (K + 1) → ℝ :=
  fun m => criticalMellinAtomWeight (m.val + 2) *
    (ccmActualHeadMatchedQuantilePolarDisplacement (m.val + 2) *
        ccmActualHeadMatchedPolarCentroid (m.val + 2) +
      ccmActualHeadMatchedQuantilePolarDisplacement (m.val + 2) ^ (2 : ℕ) / 2)

def ccmActualHeadMatchedQuantileParabolicCrossRightEnergy (K : ℕ) : Fin (K + 1) → ℝ :=
  fun n => -criticalMellinAtomWeight (n.val + 2) *
    (ccmActualHeadMatchedQuantilePolarDisplacement (n.val + 2) *
        ccmActualHeadMatchedPolarCentroid (n.val + 2) +
      ccmActualHeadMatchedQuantilePolarDisplacement (n.val + 2) ^ (2 : ℕ) / 2)

def ccmActualHeadMatchedQuantileParabolicCrossRightDisplacement (K : ℕ) : Fin (K + 1) → ℝ :=
  fun n => criticalMellinAtomWeight (n.val + 2) *
    ccmActualHeadMatchedQuantilePolarDisplacement (n.val + 2)

def ccmActualHeadMatchedQuantileParabolicCrossRightCentroidDisplacement
    (K : ℕ) : Fin (K + 1) → ℝ :=
  fun n => criticalMellinAtomWeight (n.val + 2) *
    (ccmActualHeadMatchedPolarCentroid (n.val + 2) +
      ccmActualHeadMatchedQuantilePolarDisplacement (n.val + 2))

def ccmActualHeadMatchedQuantileParabolicCrossRightWeight (K : ℕ) : Fin (K + 1) → ℝ :=
  fun n => -criticalMellinAtomWeight (n.val + 2)

/-- Exact four-outer-product realization of the complete parabolic cross-cell source. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix_eq_fourOuterProducts
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix K =
      Matrix.vecMulVec (ccmActualHeadMatchedQuantileParabolicCrossWeight K)
          (ccmActualHeadMatchedQuantileParabolicCrossRightEnergy K) +
        Matrix.vecMulVec (ccmActualHeadMatchedQuantileParabolicCrossCentroid K)
          (ccmActualHeadMatchedQuantileParabolicCrossRightDisplacement K) +
        Matrix.vecMulVec (ccmActualHeadMatchedQuantileParabolicCrossDisplacement K)
          (ccmActualHeadMatchedQuantileParabolicCrossRightCentroidDisplacement K) +
        Matrix.vecMulVec (ccmActualHeadMatchedQuantileParabolicCrossEnergy K)
          (ccmActualHeadMatchedQuantileParabolicCrossRightWeight K) := by
  ext m n
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix,
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_orientation_sub_debt]
  simp only [ccmActualHeadMatchedQuantileParabolicOrientationLedger,
    ccmActualHeadMatchedQuantileParabolicOrientationCoefficient,
    ccmActualHeadMatchedQuantileParabolicDisplacementDebt,
    ccmActualHeadMatchedQuantileParabolicCrossWeight,
    ccmActualHeadMatchedQuantileParabolicCrossCentroid,
    ccmActualHeadMatchedQuantileParabolicCrossDisplacement,
    ccmActualHeadMatchedQuantileParabolicCrossEnergy,
    ccmActualHeadMatchedQuantileParabolicCrossRightEnergy,
    ccmActualHeadMatchedQuantileParabolicCrossRightDisplacement,
    ccmActualHeadMatchedQuantileParabolicCrossRightCentroidDisplacement,
    ccmActualHeadMatchedQuantileParabolicCrossRightWeight,
    Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

/-- The complete finite parabolic carrier has only four source-moment image directions. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix_range_fourMoment
    (K : ℕ) (v : Fin (K + 1) → ℝ) :
    ∃ a b c d : ℝ,
      Matrix.mulVec (ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix K) v =
        a • ccmActualHeadMatchedQuantileParabolicCrossWeight K +
          b • ccmActualHeadMatchedQuantileParabolicCrossCentroid K +
          c • ccmActualHeadMatchedQuantileParabolicCrossDisplacement K +
          d • ccmActualHeadMatchedQuantileParabolicCrossEnergy K := by
  refine ⟨ccmActualHeadMatchedQuantileParabolicCrossRightEnergy K ⬝ᵥ v,
    ccmActualHeadMatchedQuantileParabolicCrossRightDisplacement K ⬝ᵥ v,
    ccmActualHeadMatchedQuantileParabolicCrossRightCentroidDisplacement K ⬝ᵥ v,
    ccmActualHeadMatchedQuantileParabolicCrossRightWeight K ⬝ᵥ v, ?_⟩
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelMatrix_eq_fourOuterProducts]
  simp only [Matrix.add_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp
  ring

end

end RHTower
