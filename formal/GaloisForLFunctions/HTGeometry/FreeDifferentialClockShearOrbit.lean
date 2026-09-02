import GaloisForLFunctions.HTGeometry.FreeDifferentialClockShear
import GaloisForLFunctions.HTGeometry.DifferentialVariationalOperatorMatrixInterleaving

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C]

/-- Explicit inverse of the rank-two clock-shear Fréchet matrix. -/
def freeClockShearFrechetInverseMatrix :
    Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))) :=
  !![-DiffOp.mono 1 1, 1; 1, 0]

omit [CharZero C] in
theorem freeClockShearFrechetMatrix_mul_inverse :
    freeClockShearFrechetMatrix (C := C) * freeClockShearFrechetInverseMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [freeClockShearFrechetMatrix, freeClockShearFrechetInverseMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

omit [CharZero C] in
theorem freeClockShearFrechetInverseMatrix_mul :
    freeClockShearFrechetInverseMatrix (C := C) * freeClockShearFrechetMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [freeClockShearFrechetMatrix, freeClockShearFrechetInverseMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The literal clock-shear matrix as a unit over the Ore ring. -/
def freeClockShearFrechetMatrixUnit :
    (Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))))ˣ where
  val := freeClockShearFrechetMatrix
  inv := freeClockShearFrechetInverseMatrix
  val_inv := freeClockShearFrechetMatrix_mul_inverse
  inv_val := freeClockShearFrechetInverseMatrix_mul

omit [CharZero C] in
@[simp] theorem freeClockShearFrechetMatrixUnit_val :
    (freeClockShearFrechetMatrixUnit (C := C) :
      Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2)))) =
        freeClockShearFrechetMatrix := rfl

omit [CharZero C] in
@[simp] theorem freeClockShearFrechetMatrixUnit_inv_val :
    ((freeClockShearFrechetMatrixUnit (C := C))⁻¹ :
      (Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))))ˣ).1 =
        freeClockShearFrechetInverseMatrix := rfl

omit [CharZero C] in
theorem matDeg_freeClockShearFrechetInverseMatrix :
    DiffOp.matDeg (freeClockShearFrechetInverseMatrix (C := C)) = 1 := by
  refine le_antisymm (DiffOp.matDeg_le fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;>
      simp [freeClockShearFrechetInverseMatrix, DiffOp.degree_zero,
        DiffOp.degree_one, DiffOp.degree_neg, DiffOp.degree_mono]
  · have h : DiffOp.degree
        (freeClockShearFrechetInverseMatrix (C := C) 0 0) = 1 := by
      simp [freeClockShearFrechetInverseMatrix, DiffOp.degree_neg,
        DiffOp.degree_mono]
    calc
      1 = DiffOp.degree (freeClockShearFrechetInverseMatrix (C := C) 0 0) := h.symm
      _ ≤ DiffOp.matDeg (freeClockShearFrechetInverseMatrix (C := C)) :=
        DiffOp.degree_le_matDeg _ 0 0

omit [CharZero C] in
theorem topCoeffMatrix_freeClockShearFrechetInverseMatrix :
    DiffOp.topCoeffMatrix (freeClockShearFrechetInverseMatrix (C := C)) 1 =
      !![-1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [freeClockShearFrechetInverseMatrix, DiffOp.topCoeffMatrix,
      DiffOp.one_def, DiffOp.coeff_mono_of_ne]

omit [CharZero C] in
private theorem freeClockShear_inverse_leading_chain_entry (n : ℕ) :
    DiffOp.chainProdK (fun _ : ℕ =>
      DiffOp.topCoeffMatrix (freeClockShearFrechetInverseMatrix (C := C)) 1) n 0 0 =
        (-1 : JetField C (Fin 2)) ^ n := by
  rw [show (fun _ : ℕ =>
      DiffOp.topCoeffMatrix (freeClockShearFrechetInverseMatrix (C := C)) 1) =
      (fun _ : ℕ => (!![-1, 0; 0, 0] :
        Matrix (Fin 2) (Fin 2) (JetField C (Fin 2)))) by
    funext _
    exact topCoeffMatrix_freeClockShearFrechetInverseMatrix]
  induction n with
  | zero => simp [DiffOp.chainProdK]
  | succ n ih =>
      rw [DiffOp.chainProdK_succ, Matrix.mul_apply]
      simp [Fin.sum_univ_two, ih, pow_succ]

omit [CharZero C] in
private theorem freeClockShear_inverse_leading_chain_ne_zero (n : ℕ) :
    DiffOp.chainProdK (fun _ : ℕ =>
      DiffOp.topCoeffMatrix (freeClockShearFrechetInverseMatrix (C := C)) 1) n ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (JetField C (Fin 2)) => M 0 0) hzero
  rw [freeClockShear_inverse_leading_chain_entry, Matrix.zero_apply] at hentry
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hentry

omit [CharZero C] in
private theorem clockOrbit_chainProd_const_eq_pow
    (A : Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2)))) (n : ℕ) :
    DiffOp.chainProd (K := JetField C (Fin 2)) (fun _ => A) n = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [DiffOp.chainProd_succ, ih, pow_succ]

omit [CharZero C] in
theorem matDeg_freeClockShearFrechetInverseMatrix_pow (n : ℕ) :
    DiffOp.matDeg (freeClockShearFrechetInverseMatrix (C := C) ^ n) = n := by
  rw [← clockOrbit_chainProd_const_eq_pow]
  simpa using DiffOp.matDeg_chainProd_eq
    (fun _ : ℕ => freeClockShearFrechetInverseMatrix (C := C)) 1
    (fun _ i j => by
      have h := DiffOp.degree_le_matDeg
        (freeClockShearFrechetInverseMatrix (C := C)) i j
      rwa [matDeg_freeClockShearFrechetInverseMatrix] at h)
    freeClockShear_inverse_leading_chain_ne_zero n

omit [CharZero C] in
private theorem exists_entry_degree_eq_matDeg_finTwo
    (P : Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2)))) (n : ℕ)
    (hP : DiffOp.matDeg P = n) :
    ∃ i j, DiffOp.degree (P i j) = n := by
  by_cases hn : n = 0
  · refine ⟨0, 0, ?_⟩
    rw [hn]
    apply Nat.eq_zero_of_le_zero
    have hle := DiffOp.degree_le_matDeg P 0 0
    rw [hP, hn] at hle
    exact hle
  · by_contra hnone
    push Not at hnone
    have hle : ∀ i j, DiffOp.degree (P i j) ≤ n - 1 := by
      intro i j
      have hij := DiffOp.degree_le_matDeg P i j
      rw [hP] at hij
      have hlt : DiffOp.degree (P i j) < n :=
        lt_of_le_of_ne hij (hnone i j)
      omega
    have hmat := DiffOp.matDeg_le hle
    rw [hP] at hmat
    omega

theorem exists_degree_freeClockShearFrechetMatrix_pow (n : ℕ) :
    ∃ i j, DiffOp.degree ((freeClockShearFrechetMatrix (C := C) ^ n) i j) = n := by
  exact exists_entry_degree_eq_matDeg_finTwo _ n
    (matDeg_freeClockShearFrechetMatrix_pow n)

omit [CharZero C] in
theorem exists_degree_freeClockShearFrechetInverseMatrix_pow (n : ℕ) :
    ∃ i j, DiffOp.degree
      ((freeClockShearFrechetInverseMatrix (C := C) ^ n) i j) = n := by
  exact exists_entry_degree_eq_matDeg_finTwo _ n
    (matDeg_freeClockShearFrechetInverseMatrix_pow n)

/-- Actual completed-lattice orbit of the standard point under the `n`-th clock-shear matrix. -/
def freeClockShearCompletedOrbitLattice (n : ℕ) :
    DiffOp.CompletedPseudoDiffOpLattice (JetField C (Fin 2)) (Fin 2) :=
  DiffOp.mapCompletedPseudoDiffOpLatticeLinear
    (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
      (DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
        (freeClockShearFrechetMatrixUnit (C := C) ^ n)))
    (DiffOp.standardCompletedPseudoDiffOpLattice
      (K := JetField C (Fin 2)) (ι := Fin 2))

omit [CharZero C] in
theorem freeClockShearFrechetMatrixUnit_pow_val (n : ℕ) :
    (freeClockShearFrechetMatrixUnit (C := C) ^ n :
      (Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))))ˣ).1 =
        freeClockShearFrechetMatrix ^ n := rfl

omit [CharZero C] in
theorem freeClockShearFrechetMatrixUnit_pow_inv_val (n : ℕ) :
    ((freeClockShearFrechetMatrixUnit (C := C) ^ n)⁻¹ :
      (Matrix (Fin 2) (Fin 2) (DiffOp (JetField C (Fin 2))))ˣ).1 =
        freeClockShearFrechetInverseMatrix ^ n := rfl

/-- Exact geometric clock law in the unconditional projective interleaving metric. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_freeClockShear (n : ℕ) :
    DiffOp.completedPseudoDiffOpLatticeOrbitInterleavingDistance
      (DiffOp.standardCompletedPseudoDiffOpLattice
        (K := JetField C (Fin 2)) (ι := Fin 2))
      (freeClockShearCompletedOrbitLattice (C := C) n) = n := by
  let U := freeClockShearFrechetMatrixUnit (C := C) ^ n
  let L := DiffOp.standardCompletedPseudoDiffOpLattice
    (K := JetField C (Fin 2)) (ι := Fin 2)
  let M := freeClockShearCompletedOrbitLattice (C := C) n
  have hupper : DiffOp.completedPseudoDiffOpLatticeOrbitInterleavingDistance L M ≤ n := by
    rw [DiffOp.completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
    apply (DiffOp.standard_leftOrbitInterleavedAt_operatorMatrix_iff n U).2
    refine ⟨0, ?_, ?_⟩
    · intro i j
      right
      rw [show (↑(U⁻¹) : Matrix (Fin 2) (Fin 2)
          (DiffOp (JetField C (Fin 2)))) i j =
          (freeClockShearFrechetInverseMatrix (C := C) ^ n) i j by
        exact congrFun (congrFun (freeClockShearFrechetMatrixUnit_pow_inv_val n) i) j]
      change (DiffOp.degree
        ((freeClockShearFrechetInverseMatrix (C := C) ^ n) i j) : ℤ) ≤ (n : ℤ)
      exact_mod_cast (by
        simpa [matDeg_freeClockShearFrechetInverseMatrix_pow n] using
          DiffOp.degree_le_matDeg
            (freeClockShearFrechetInverseMatrix (C := C) ^ n) i j)
    · intro i j
      right
      rw [show (U : Matrix (Fin 2) (Fin 2)
          (DiffOp (JetField C (Fin 2)))) i j =
          (freeClockShearFrechetMatrix (C := C) ^ n) i j by
        exact congrFun (congrFun (freeClockShearFrechetMatrixUnit_pow_val n) i) j]
      change (DiffOp.degree
        ((freeClockShearFrechetMatrix (C := C) ^ n) i j) : ℤ) ≤ (n : ℤ)
      exact_mod_cast (by
        simpa [matDeg_freeClockShearFrechetMatrix_pow n] using
          DiffOp.degree_le_matDeg (freeClockShearFrechetMatrix (C := C) ^ n) i j)
  apply le_antisymm hupper
  by_cases hn : n = 0
  · omega
  · let d := DiffOp.completedPseudoDiffOpLatticeOrbitInterleavingDistance L M
    have hspec := DiffOp.completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M
    obtain ⟨z, hInv, hMat⟩ :=
      (DiffOp.standard_leftOrbitInterleavedAt_operatorMatrix_iff d U).1 hspec
    obtain ⟨i, j, hij⟩ := exists_degree_freeClockShearFrechetMatrix_pow (C := C) n
    obtain ⟨i', j', hij'⟩ :=
      exists_degree_freeClockShearFrechetInverseMatrix_pow (C := C) n
    have hP : (n : ℤ) ≤ (d : ℤ) + z := by
      have h := hMat i j
      rw [show (U : Matrix (Fin 2) (Fin 2)
          (DiffOp (JetField C (Fin 2)))) i j =
          (freeClockShearFrechetMatrix (C := C) ^ n) i j by
        exact congrFun (congrFun (freeClockShearFrechetMatrixUnit_pow_val n) i) j] at h
      rcases h with hzero | hdeg
      · rw [hzero, DiffOp.degree_zero] at hij
        omega
      · rw [hij] at hdeg
        exact hdeg
    have hQ : (n : ℤ) ≤ (d : ℤ) - z := by
      have h := hInv i' j'
      rw [show (↑(U⁻¹) : Matrix (Fin 2) (Fin 2)
          (DiffOp (JetField C (Fin 2)))) i' j' =
          (freeClockShearFrechetInverseMatrix (C := C) ^ n) i' j' by
        exact congrFun (congrFun (freeClockShearFrechetMatrixUnit_pow_inv_val n) i') j'] at h
      rcases h with hzero | hdeg
      · rw [hzero, DiffOp.degree_zero] at hij'
        omega
      · rw [hij'] at hdeg
        exact hdeg
    omega

theorem freeFrechetMatrix_freeClockShear_pow (n : ℕ) :
    freeFrechetMatrix (freeClockShear (C := C) ^ n) =
      freeClockShearFrechetMatrix ^ n := by
  cases n with
  | zero =>
      rw [pow_zero, freeFrechetMatrix_one (C := C) (ι := Fin 2), pow_zero]
      ext i j
      by_cases h : i = j
      · subst j
        simp
      · simp [h]
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        (freeFrechetMatrix_freeClockShear_pow_succ (C := C) n)

theorem variationalOreCompletedMatrixUnit_freeClockShear_pow (n : ℕ) :
    variationalOreCompletedMatrixUnit
        (freeClockShear (C := C) ^ n).fixes
        (freeClockShear (C := C) ^ n).deriv_comm
        (freeVariationalOreBasis (C := C) (r := 2)) =
      DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
        (freeClockShearFrechetMatrixUnit (C := C) ^ n) := by
  apply Units.ext
  rw [variationalOreCompletedMatrixUnit_free_val,
    DiffOp.completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val,
    freeClockShearFrechetMatrixUnit_pow_val,
    freeFrechetMatrix_freeClockShear_pow]

/-- Standard projective completed-lattice point in free rank two. -/
def freeClockShearProjectiveBasePoint :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier
      (JetField C (Fin 2)) (Fin 2) :=
  Quotient.mk
    (DiffOp.completedPseudoDiffOpLatticeLeftHomothetySetoid
      (K := JetField C (Fin 2)) (ι := Fin 2))
    (DiffOp.standardCompletedPseudoDiffOpLattice
      (K := JetField C (Fin 2)) (ι := Fin 2))

theorem projectiveBuildingAction_freeClockShear_pow_basePoint (n : ℕ) :
    (freeClockShear (C := C) ^ n).projectiveBuildingAction
        (freeVariationalOreBasis (C := C) (r := 2))
        (freeClockShearProjectiveBasePoint (C := C)) =
      Quotient.mk
        (DiffOp.completedPseudoDiffOpLatticeLeftHomothetySetoid
          (K := JetField C (Fin 2)) (ι := Fin 2))
        (freeClockShearCompletedOrbitLattice (C := C) n) := by
  unfold projectiveBuildingAction variationalOreProjectiveBuildingAction
    DiffOp.differentialVariationalProjectiveSemilinearAction
    freeClockShearProjectiveBasePoint
  change Quotient.mk _
      (DiffOp.mapCompletedPseudoDiffOpLatticeLinear
        (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
          (variationalOreCompletedMatrixUnit
            (freeClockShear (C := C) ^ n).fixes
            (freeClockShear (C := C) ^ n).deriv_comm
            (freeVariationalOreBasis (C := C) (r := 2))))
        (DiffOp.mapCompletedPseudoDiffOpLattice
          (freeClockShear (C := C) ^ n).toRingEquiv
          (freeClockShear (C := C) ^ n).deriv_comm
          (DiffOp.standardCompletedPseudoDiffOpLattice
            (K := JetField C (Fin 2)) (ι := Fin 2)))) = _
  rw [DiffOp.map_standardCompletedPseudoDiffOpLattice,
    variationalOreCompletedMatrixUnit_freeClockShear_pow]
  rfl

/-- Exact unit-cost orbit law for the actual canonical variational projective action. -/
theorem projectiveInterleavingDistance_freeClockShear_pow_basePoint (n : ℕ) :
    DiffOp.differentialVariationalProjectiveInterleavingDistance
        (freeClockShearProjectiveBasePoint (C := C))
        ((freeClockShear (C := C) ^ n).projectiveBuildingAction
          (freeVariationalOreBasis (C := C) (r := 2))
          (freeClockShearProjectiveBasePoint (C := C))) = n := by
  rw [projectiveBuildingAction_freeClockShear_pow_basePoint]
  exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_freeClockShear n

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
