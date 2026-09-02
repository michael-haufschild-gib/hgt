import GaloisForLFunctions.HTGeometry.DifferentialVariationalSemilinearMatrixAction
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingAction
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingStandardApartment

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DiffOp

variable {K : Type u} [Field K] [Differential K]

theorem completedPseudoDiffOpAddValue_diffOpToCompletedPseudoRingHom_of_ne_zero
    (p : DiffOp K) (hp : p ≠ 0) :
    completedPseudoDiffOpAddValue (diffOpToCompletedPseudoRingHom p) =
      (-(degree p : ℤ) : WithTop ℤ) := by
  classical
  rw [diffOpToCompletedPseudoRingHom_apply, completedPseudoDiffOpAddValue]
  rw [completedPseudoDiffOpValuation_apply_coe]
  change pseudoDiffOpAddValuation (numeratorRingHom p : PseudoDiffOp K) = _
  rw [pseudoDiffOpAddValuation_apply]
  unfold pseudoDiffOpAddValuationValue
  have hnum : (numeratorRingHom p : PseudoDiffOp K) ≠ 0 :=
    fun h => hp (numeratorRingHom_injective (h.trans (map_zero _).symm))
  rw [if_neg hnum, ordQ_numeratorRingHom, if_neg hp]
  norm_cast

theorem diffOpToCompletedPseudoRingHom_mem_integer_iff
    (p : DiffOp K) :
    diffOpToCompletedPseudoRingHom p ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      p = 0 ∨ degree p = 0 := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg]
  by_cases hp : p = 0
  · subst p
    simp only [eq_self, true_or, iff_true, map_zero]
    unfold completedPseudoDiffOpAddValue
    rw [Valuation.map_zero]
    exact le_top
  · rw [completedPseudoDiffOpAddValue_diffOpToCompletedPseudoRingHom_of_ne_zero p hp]
    simp only [hp, false_or]
    norm_cast
    omega

theorem uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff
    (n : ℕ) (p : DiffOp K) :
    ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
        diffOpToCompletedPseudoRingHom p ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      degree p ≤ n := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  by_cases hp : p = 0
  · subst p
    simp only [map_zero]
    unfold completedPseudoDiffOpAddValue
    rw [Valuation.map_zero]
    exact iff_of_true le_top (Nat.zero_le _)
  · rw [completedPseudoDiffOpAddValue_diffOpToCompletedPseudoRingHom_of_ne_zero p hp]
    norm_cast
    omega

theorem uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int
    (z : ℤ) (p : DiffOp K) :
    ((completedPseudoDiffOpUniformizerUnit (K := K) ^ z :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
        diffOpToCompletedPseudoRingHom p ∈ CompletedPseudoDiffOpInteger (K := K) ↔
      p = 0 ∨ (degree p : ℤ) ≤ z := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  by_cases hp : p = 0
  · subst p
    simp only [map_zero, eq_self, true_or, iff_true]
    unfold completedPseudoDiffOpAddValue
    rw [Valuation.map_zero]
    exact le_top
  · rw [completedPseudoDiffOpAddValue_diffOpToCompletedPseudoRingHom_of_ne_zero p hp]
    simp only [hp, false_or]
    norm_cast
    omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mapMatrix_standard_carrier_le_iff
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv A)
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))).carrier ≤
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier ↔
      ∀ i j, (A : Matrix ι ι (CompletedPseudoDiffOp K)) i j ∈
        CompletedPseudoDiffOpInteger (K := K) := by
  constructor
  · intro h i j
    let e : ι → CompletedPseudoDiffOp K := Pi.basisFun (CompletedPseudoDiffOp K) ι i
    have he : e ∈ (standardCompletedPseudoDiffOpLattice
        (K := K) (ι := ι)).carrier := basisFun_mem_completedPseudoDiffOpIntegralCarrier i
    have himage : completedPseudoDiffOpMatrixLinearEquiv A e ∈
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))).carrier :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff _ _ _).2 ⟨e, he, rfl⟩
    have hj := (mem_standardCompletedPseudoDiffOpLattice_iff _).1 (h himage) j
    simpa [e, completedPseudoDiffOpMatrixLinearEquiv, Matrix.vecMul,
      Pi.basisFun_apply] using hj
  · intro h y hy
    rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hx ⊢
    intro j
    change (∑ i, x i * (A : Matrix ι ι (CompletedPseudoDiffOp K)) i j) ∈
      CompletedPseudoDiffOpInteger (K := K)
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (h i j)

theorem leftScale_mapMatrix_standard_carrier_le_iff
    (a : (CompletedPseudoDiffOp K)ˣ)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (leftScaleCompletedPseudoDiffOpLattice a
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv A)
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)))).carrier ≤
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier ↔
      ∀ i j, (a : CompletedPseudoDiffOp K) *
        (A : Matrix ι ι (CompletedPseudoDiffOp K)) i j ∈
          CompletedPseudoDiffOpInteger (K := K) := by
  constructor
  · intro h i j
    let e : ι → CompletedPseudoDiffOp K := Pi.basisFun (CompletedPseudoDiffOp K) ι i
    have he : e ∈ (standardCompletedPseudoDiffOpLattice
        (K := K) (ι := ι)).carrier := basisFun_mem_completedPseudoDiffOpIntegralCarrier i
    have himage : completedPseudoDiffOpMatrixLinearEquiv A e ∈
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))).carrier :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff _ _ _).2 ⟨e, he, rfl⟩
    have hscale : leftMulCompletedPseudoIntegerVecSemilinearMap a
        (completedPseudoDiffOpMatrixLinearEquiv A e) ∈
        (leftScaleCompletedPseudoDiffOpLattice a
          (mapCompletedPseudoDiffOpLatticeLinear
            (completedPseudoDiffOpMatrixLinearEquiv A)
            (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)))).carrier :=
      (mem_leftScaleCompletedPseudoDiffOpLattice_iff _ _ _).2
        ⟨_, himage, rfl⟩
    have hj := (mem_standardCompletedPseudoDiffOpLattice_iff _).1 (h hscale) j
    have hentry : leftMulCompletedPseudoIntegerVecSemilinearMap a
        (completedPseudoDiffOpMatrixLinearEquiv A e) j =
          (a : CompletedPseudoDiffOp K) *
            (A : Matrix ι ι (CompletedPseudoDiffOp K)) i j := by
      change (a : CompletedPseudoDiffOp K) *
        Matrix.vecMul e (A : Matrix ι ι (CompletedPseudoDiffOp K)) j = _
      simp [e, Matrix.vecMul, Pi.basisFun_apply]
    rwa [hentry] at hj
  · intro h y hy
    rw [mem_leftScaleCompletedPseudoDiffOpLattice_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hx ⊢
    intro j
    change (a : CompletedPseudoDiffOp K) *
        (∑ i, x i * (A : Matrix ι ι (CompletedPseudoDiffOp K)) i j) ∈
      CompletedPseudoDiffOpInteger (K := K)
    rw [Finset.mul_sum]
    apply Subring.sum_mem
    intro i hi
    rw [← mul_assoc, show (a : CompletedPseudoDiffOp K) * x i =
      ((a : CompletedPseudoDiffOp K) * x i * a⁻¹) * a by simp [mul_assoc],
      mul_assoc]
    exact Subring.mul_mem _
      (innerCompletedPseudoDiffOp_mem_integer a ⟨x i, hx i⟩) (h i j)

theorem standard_carrier_le_leftScale_mapMatrix_iff
    (a : (CompletedPseudoDiffOp K)ˣ)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice a
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)))).carrier ↔
      ∀ i j, (a⁻¹ : (CompletedPseudoDiffOp K)ˣ) *
        (A⁻¹ : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ).1 i j ∈
          CompletedPseudoDiffOpInteger (K := K) := by
  rw [← leftScaleCompletedPseudoDiffOpLattice_carrier_le_iff a⁻¹]
  simp only [leftScaleCompletedPseudoDiffOpLattice_mul, inv_mul_cancel,
    leftScaleCompletedPseudoDiffOpLattice_one]
  rw [← mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff
    (completedPseudoDiffOpMatrixLinearEquiv A⁻¹)]
  rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale,
    mapCompletedPseudoDiffOpLatticeLinear_trans,
    completedPseudoDiffOpMatrixLinearEquiv_mul]
  simp only [mul_inv_cancel, completedPseudoDiffOpMatrixLinearEquiv_one,
    mapCompletedPseudoDiffOpLatticeLinear_refl]
  exact leftScale_mapMatrix_standard_carrier_le_iff a⁻¹ A⁻¹

theorem standard_interleavedAt_leftScale_mapMatrix_iff
    (n : ℕ) (a : (CompletedPseudoDiffOp K)ˣ)
    (A : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ) :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).InterleavedAt n
      (leftScaleCompletedPseudoDiffOpLattice a
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv A)
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)))) ↔
      (∀ i j, ((a⁻¹ *
          completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) :
            (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
          (A⁻¹ : (Matrix ι ι (CompletedPseudoDiffOp K))ˣ).1 i j ∈
            CompletedPseudoDiffOpInteger (K := K)) ∧
      (∀ i j, ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) * a :
            (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) *
          (A : Matrix ι ι (CompletedPseudoDiffOp K)) i j ∈
            CompletedPseudoDiffOpInteger (K := K)) := by
  let piN := completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  have hunit : (piN⁻¹ * a)⁻¹ = a⁻¹ * piN := by
    simp
  constructor
  · rintro ⟨hleft, hright⟩
    have hleft' :=
      (leftScaleCompletedPseudoDiffOpLattice_carrier_le_iff piN⁻¹
        (leftScaleCompletedPseudoDiffOpLattice piN L)
        (leftScaleCompletedPseudoDiffOpLattice a M)).2 hleft
    simp only [leftScaleCompletedPseudoDiffOpLattice_mul, inv_mul_cancel,
      leftScaleCompletedPseudoDiffOpLattice_one] at hleft'
    have hInv := (standard_carrier_le_leftScale_mapMatrix_iff (piN⁻¹ * a) A).1 hleft'
    have hright' :
        (leftScaleCompletedPseudoDiffOpLattice (piN * a) M).carrier ≤ L.carrier := by
      simpa only [leftScaleCompletedPseudoDiffOpLattice_mul] using hright
    have hMat := (leftScale_mapMatrix_standard_carrier_le_iff (piN * a) A).1 hright'
    refine ⟨?_, ?_⟩
    · intro i j
      rw [hunit] at hInv
      exact hInv i j
    · intro i j
      exact hMat i j
  · rintro ⟨hInv, hMat⟩
    have hleft' : L.carrier ≤
        (leftScaleCompletedPseudoDiffOpLattice (piN⁻¹ * a) M).carrier := by
      apply (standard_carrier_le_leftScale_mapMatrix_iff (piN⁻¹ * a) A).2
      intro i j
      rw [hunit]
      exact hInv i j
    have hleft :=
      (leftScaleCompletedPseudoDiffOpLattice_carrier_le_iff piN L
        (leftScaleCompletedPseudoDiffOpLattice (piN⁻¹ * a) M)).2 hleft'
    have hright' :
        (leftScaleCompletedPseudoDiffOpLattice (piN * a) M).carrier ≤ L.carrier := by
      apply (leftScale_mapMatrix_standard_carrier_le_iff (piN * a) A).2
      exact hMat
    refine ⟨?_, ?_⟩
    · have hcancel : piN * (piN⁻¹ * a) = a := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [leftScaleCompletedPseudoDiffOpLattice_mul, hcancel] at hleft
      exact hleft
    · simpa only [leftScaleCompletedPseudoDiffOpLattice_mul] using hright'

@[simp] theorem completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val
    (U : (Matrix ι ι (DiffOp K))ˣ) :
    ((completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U)⁻¹ :
        (Matrix ι ι (CompletedPseudoDiffOp K))ˣ).1 =
      ((U⁻¹ : (Matrix ι ι (DiffOp K))ˣ).1).map
        diffOpToCompletedPseudoRingHom := by
  rfl

theorem standard_leftOrbitInterleavedAt_operatorMatrix_iff
    (n : ℕ) (U : (Matrix ι ι (DiffOp K))ˣ) :
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).LeftOrbitInterleavedAt n
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv
          (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U))
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))) ↔
      ∃ z : ℤ,
        (∀ i j, (U⁻¹ : (Matrix ι ι (DiffOp K))ˣ).1 i j = 0 ∨
          ((degree ((U⁻¹ : (Matrix ι ι (DiffOp K))ˣ).1 i j) : ℕ) : ℤ) ≤
            (n : ℤ) - z) ∧
        (∀ i j, (U : Matrix ι ι (DiffOp K)) i j = 0 ∨
          ((degree ((U : Matrix ι ι (DiffOp K)) i j) : ℕ) : ℤ) ≤
            (n : ℤ) + z) := by
  let pi := completedPseudoDiffOpUniformizerUnit (K := K)
  let A := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit U
  let L := standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)
  let M := mapCompletedPseudoDiffOpLatticeLinear
    (completedPseudoDiffOpMatrixLinearEquiv A) L
  have hminus (z : ℤ) : (pi ^ z)⁻¹ * pi ^ (n : ℤ) = pi ^ ((n : ℤ) - z) := by
    rw [← zpow_neg, ← zpow_add]
    congr 1
    omega
  have hplus (z : ℤ) : pi ^ (n : ℤ) * pi ^ z = pi ^ ((n : ℤ) + z) := by
    rw [← zpow_add]
  constructor
  · rintro ⟨a, ha⟩
    let z := completedPseudoDiffOpUnitAddValue a
    have hrep := leftScaleCompletedPseudoDiffOpLattice_eq_uniformizer_zpow_unitAddValue a M
    rw [hrep] at ha
    have h := (standard_interleavedAt_leftScale_mapMatrix_iff n (pi ^ z) A).1 ha
    refine ⟨z, ?_, ?_⟩
    · intro i j
      have hij := h.1 i j
      rw [hminus z, completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val,
        Matrix.map_apply] at hij
      exact (uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int
        ((n : ℤ) - z) ((U⁻¹ : (Matrix ι ι (DiffOp K))ˣ).1 i j)).1 hij
    · intro i j
      have hij := h.2 i j
      rw [hplus z, completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val,
        Matrix.map_apply] at hij
      exact (uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int
        ((n : ℤ) + z) ((U : Matrix ι ι (DiffOp K)) i j)).1 hij
  · rintro ⟨z, hInv, hMat⟩
    refine ⟨pi ^ z, ?_⟩
    apply (standard_interleavedAt_leftScale_mapMatrix_iff n (pi ^ z) A).2
    constructor
    · intro i j
      rw [hminus z, completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_inv_val,
        Matrix.map_apply]
      exact (uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int
        ((n : ℤ) - z) ((U⁻¹ : (Matrix ι ι (DiffOp K))ˣ).1 i j)).2 (hInv i j)
    · intro i j
      rw [hplus z, completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val,
        Matrix.map_apply]
      exact (uniformizer_zpow_mul_diffOpToCompletedPseudoRingHom_mem_integer_iff_int
        ((n : ℤ) + z) ((U : Matrix ι ι (DiffOp K)) i j)).2 (hMat i j)

end DiffOp

end

end GaloisForLFunctions.HTGeometry

