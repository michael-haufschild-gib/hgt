import GaloisForLFunctions.HTGeometry.DifferentialVariationalCartanTranslationNorm
import GaloisForLFunctions.HTGeometry.FreeDifferentialOrderCartan
import GaloisForLFunctions.HTGeometry.DifferentialOperatorCompletedCartanBalance

/-!
# Free differential order as intrinsic Cartan translation speed

The matrix-degree orientation of free differential order points from the orbit lattice back to the
base lattice.  This file identifies that orientation on the actual projective Euclidean vertex
carrier, constructs its dominant balanced vector limit, and proves that the existing free-order
Fekete speed is exactly the top coordinate of that vector.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C] {r : ℕ}

/-- Standard projective completed-lattice point in arbitrary free differential rank. -/
def freeDifferentialProjectiveBasePoint (r : ℕ) :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier
      (JetField C (Fin r)) (Fin r) :=
  Quotient.mk
    (DiffOp.completedPseudoDiffOpLatticeLeftHomothetySetoid
      (K := JetField C (Fin r)) (ι := Fin r))
    (DiffOp.standardCompletedPseudoDiffOpLattice
      (K := JetField C (Fin r)) (ι := Fin r))

/-- The canonical free action sends the standard projective point to the projective class of its
literal completed variational-operator-matrix orbit lattice. -/
theorem projectiveBuildingAction_free_basePoint
    (σ : FreeAut (C := C) (ι := Fin r)) :
    σ.projectiveBuildingAction
        (freeVariationalOreBasis (C := C) (r := r))
        (freeDifferentialProjectiveBasePoint (C := C) r) =
      Quotient.mk
        (DiffOp.completedPseudoDiffOpLatticeLeftHomothetySetoid
          (K := JetField C (Fin r)) (ι := Fin r))
        (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
          (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
            (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm
              (freeVariationalOreBasis (C := C) (r := r))))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin r)) (ι := Fin r))) := by
  unfold projectiveBuildingAction variationalOreProjectiveBuildingAction
    DiffOp.differentialVariationalProjectiveSemilinearAction
    freeDifferentialProjectiveBasePoint
  change Quotient.mk _
      (DiffOp.mapCompletedPseudoDiffOpLatticeLinear _
        (DiffOp.mapCompletedPseudoDiffOpLattice σ.toRingEquiv σ.deriv_comm
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin r)) (ι := Fin r)))) = _
  rw [DiffOp.map_standardCompletedPseudoDiffOpLattice]

/-- Equation `(19)` on the literal projective Euclidean carrier: free differential order is the
top centered Cartan coordinate from the orbit point back to the standard point. -/
theorem freeDifferentialOrder_eq_reverseProjectiveEuclideanRelativePosition_zero
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    (freeDifferentialOrder σ : ℝ) =
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
        (σ.projectiveBuildingAction
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (freeDifferentialProjectiveBasePoint (C := C) (r + 1)))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) :
        Fin (r + 1) → ℝ) 0 := by
  rw [projectiveBuildingAction_free_basePoint]
  change (freeDifferentialOrder σ : ℝ) =
    DiffOp.centeredCoweight
      (DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
          (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
            (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm
              (freeVariationalOreBasis (C := C) (r := r + 1))))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))))
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) ) 0
  let L := DiffOp.standardCompletedPseudoDiffOpLattice
    (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))
  let M := DiffOp.mapCompletedPseudoDiffOpLatticeLinear
    (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
      (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm
        (freeVariationalOreBasis (C := C) (r := r + 1)))) L
  have hforward : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L M i = 0 := by
    exact DiffOp.differentialOperatorMatrixCartanBalance
      (variationalOreOperatorMatrixUnit σ.fixes σ.deriv_comm
        (freeVariationalOreBasis (C := C) (r := r + 1)))
  have hreverse : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition M L i = 0 := by
    have hadd := DiffOp.completedPseudoDiffOpCartanIndex_add M L M
    rw [DiffOp.completedPseudoDiffOpCartanIndex_self] at hadd
    have hadd' : DiffOp.completedPseudoDiffOpCartanIndex M L +
        DiffOp.completedPseudoDiffOpCartanIndex L M = 0 := hadd.symm
    unfold DiffOp.completedPseudoDiffOpCartanIndex at hadd'
    rw [hforward, add_zero] at hadd'
    exact hadd'
  have hreverse' :
      ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
          (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
            (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm
              (freeVariationalOreBasis (C := C) (r := r + 1))))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))))
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) i = 0 := by
    simpa only [M, L] using hreverse
  have hreverseReal :
      ∑ i, ((DiffOp.completedPseudoDiffOpDominantRelativePosition
        (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
          (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
            (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm
              (freeVariationalOreBasis (C := C) (r := r + 1))))
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))))
        (DiffOp.standardCompletedPseudoDiffOpLattice
          (K := JetField C (Fin (r + 1))) (ι := Fin (r + 1))) i : ℤ) : ℝ) = 0 := by
    exact_mod_cast hreverse'
  rw [DiffOp.centeredCoweight]
  rw [hreverseReal, zero_div, sub_zero]
  exact_mod_cast (freeDifferentialOrder_eq_topCartan σ).symm

/-- Dominant Cartan translation vector in differential-order orientation, from orbit point back to
base point. -/
noncomputable def freeDifferentialReverseCartanTranslationVector
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) : Fin (r + 1) → ℝ :=
  fun i => -differentialVariationalCartanTranslationVector
    (freeVariationalOreBasis (C := C) (r := r + 1))
    (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ i.rev

/-- Normalized reverse Cartan displacement converges coordinatewise to the order-oriented vector. -/
theorem tendsto_freeDifferential_reverseCartanTranslationVector
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    Filter.Tendsto (fun n : ℕ => fun i : Fin (r + 1) =>
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
        ((σ ^ n).projectiveBuildingAction
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (freeDifferentialProjectiveBasePoint (C := C) (r + 1)))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) :
        Fin (r + 1) → ℝ) i / n)
      Filter.atTop (nhds (freeDifferentialReverseCartanTranslationVector σ)) := by
  rw [tendsto_pi_nhds]
  intro i
  have hforward := tendsto_differentialVariationalCartanTranslationVector
    (freeVariationalOreBasis (C := C) (r := r + 1))
    (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ
  rw [tendsto_pi_nhds] at hforward
  have hneg := (hforward i.rev).neg
  unfold freeDifferentialReverseCartanTranslationVector
  convert hneg using 1
  funext n
  rw [DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_reverse_apply]
  ring

/-- The order-oriented Cartan translation vector lies in the dominant Weyl chamber. -/
theorem freeDifferentialReverseCartanTranslationVector_antitone
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    Antitone (freeDifferentialReverseCartanTranslationVector σ) := by
  intro i j hij
  unfold freeDifferentialReverseCartanTranslationVector
  apply neg_le_neg
  exact differentialVariationalCartanTranslationVector_antitone
    (freeVariationalOreBasis (C := C) (r := r + 1))
    (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ
    (Fin.rev_le_rev.mpr hij)

/-- The order-oriented Cartan translation vector is exactly balanced. -/
theorem freeDifferentialReverseCartanTranslationVector_sum_eq_zero
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    ∑ i, freeDifferentialReverseCartanTranslationVector σ i = 0 := by
  unfold freeDifferentialReverseCartanTranslationVector
  rw [Finset.sum_neg_distrib]
  have hperm :
      (∑ i : Fin (r + 1), differentialVariationalCartanTranslationVector
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ i.rev) =
      ∑ i : Fin (r + 1), differentialVariationalCartanTranslationVector
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ i := by
    simpa [DiffOp.completedPseudoDiffOpFinRevPerm] using
      (Equiv.sum_comp (DiffOp.completedPseudoDiffOpFinRevPerm (r + 1))
        (differentialVariationalCartanTranslationVector
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ))
  rw [hperm, differentialVariationalCartanTranslationVector_sum_eq_zero, neg_zero]

/-- Intrinsic free differential-order speed is exactly the largest order-oriented Cartan
translation coordinate. -/
theorem freeDifferentialOrderTranslationLength_eq_reverseCartan_zero
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    freeOrderGauge.translationLength σ =
      freeDifferentialReverseCartanTranslationVector σ 0 := by
  have horder := tendsto_normalized_freeDifferentialOrder σ
  have hreverse := tendsto_freeDifferential_reverseCartanTranslationVector σ
  rw [tendsto_pi_nhds] at hreverse
  have hreverse0 := hreverse 0
  have hsame : Filter.Tendsto
      (fun n : ℕ => (freeDifferentialOrder (σ ^ n) : ℝ) / n)
      Filter.atTop
      (nhds (freeDifferentialReverseCartanTranslationVector σ 0)) := by
    convert hreverse0 using 1
    funext n
    have hexact := freeDifferentialOrder_eq_reverseProjectiveEuclideanRelativePosition_zero
      (σ ^ n)
    exact congrArg (fun z : ℝ => z / n) hexact
  exact tendsto_nhds_unique horder hsame

/-- In the forward base-to-orbit convention, free differential-order speed is the negative bottom
Cartan translation coordinate. -/
theorem freeDifferentialOrderTranslationLength_eq_neg_cartan_last
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    freeOrderGauge.translationLength σ =
      -differentialVariationalCartanTranslationVector
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) σ (Fin.last r) := by
  rw [freeDifferentialOrderTranslationLength_eq_reverseCartan_zero]
  rfl

omit [CharZero C] in
/-- Free differential-order translation speed is nonnegative. -/
theorem freeDifferentialOrderTranslationLength_nonneg
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    0 ≤ freeOrderGauge.translationLength σ := by
  have horder := tendsto_normalized_freeDifferentialOrder σ
  rw [← neg_nonpos]
  apply le_of_tendsto' horder.neg
  intro n
  exact neg_nonpos.mpr (by positivity)

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
