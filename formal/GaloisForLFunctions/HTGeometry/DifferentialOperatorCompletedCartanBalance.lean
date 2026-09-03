import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCartanIndex
import GaloisForLFunctions.HTGeometry.DifferentialVariationalSemilinearMatrixAction
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreDiagonal
import GaloisForLFunctions.HTGeometry.OperatorBalanceLaw
import GaloisForLFunctions.HTGeometry.DifferentialVariationalOperatorMatrixInterleaving

/-!
# Exact Cartan balance for invertible differential-operator matrices

The sum of the dominant completed-pseudodifferential Cartan coordinates defines an additive
character on completed linear frames.  Elementary differential-operator transvections have
character zero.  Ore row-column diagonalization then reduces every matrix unit to a diagonal
matrix unit, whose entries and inverse entries all have differential order zero and therefore fix
the standard completed valuation lattice.  Consequently every invertible operator matrix, and in
particular every canonical finite-basis variational Ore action, has exactly balanced Cartan vector.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {r : ℕ}

def completedPseudoDiffOpLinearCartanIndex
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) : ℤ :=
  completedPseudoDiffOpCartanIndex
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
    (mapCompletedPseudoDiffOpLatticeLinear e
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)))

theorem completedPseudoDiffOpCartanIndex_mapLinear
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpCartanIndex
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M) =
      completedPseudoDiffOpCartanIndex L M := by
  unfold completedPseudoDiffOpCartanIndex
  rw [completedPseudoDiffOpDominantRelativePosition_mapLinear]

theorem completedPseudoDiffOpCartanIndex_self (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpCartanIndex L L = 0 := by
  have h := completedPseudoDiffOpCartanIndex_add L L L
  omega

theorem completedPseudoDiffOpLinearCartanIndex_refl :
    completedPseudoDiffOpLinearCartanIndex
      (LinearEquiv.refl (CompletedPseudoDiffOp K)
        (Fin r → CompletedPseudoDiffOp K)) = 0 := by
  unfold completedPseudoDiffOpLinearCartanIndex
  rw [mapCompletedPseudoDiffOpLatticeLinear_refl]
  exact completedPseudoDiffOpCartanIndex_self _

theorem completedPseudoDiffOpLinearCartanIndex_trans
    (e f : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    completedPseudoDiffOpLinearCartanIndex (e.trans f) =
      completedPseudoDiffOpLinearCartanIndex e + completedPseudoDiffOpLinearCartanIndex f := by
  let Z := standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)
  change completedPseudoDiffOpCartanIndex Z
      (mapCompletedPseudoDiffOpLatticeLinear (e.trans f) Z) = _
  rw [← mapCompletedPseudoDiffOpLatticeLinear_trans]
  rw [completedPseudoDiffOpCartanIndex_add Z
    (mapCompletedPseudoDiffOpLatticeLinear f Z)
    (mapCompletedPseudoDiffOpLatticeLinear f
      (mapCompletedPseudoDiffOpLatticeLinear e Z))]
  rw [completedPseudoDiffOpCartanIndex_mapLinear f Z (mapCompletedPseudoDiffOpLatticeLinear e Z)]
  simp only [completedPseudoDiffOpLinearCartanIndex, Z]
  omega

theorem completedPseudoDiffOpLinearCartanIndex_symm
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    completedPseudoDiffOpLinearCartanIndex e.symm = -completedPseudoDiffOpLinearCartanIndex e := by
  have h := completedPseudoDiffOpLinearCartanIndex_trans e e.symm
  rw [e.self_trans_symm, completedPseudoDiffOpLinearCartanIndex_refl] at h
  omega

theorem completedPseudoDiffOpLinearCartanIndex_conj
    (e s : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) :
    completedPseudoDiffOpLinearCartanIndex (s.symm.trans (e.trans s)) =
      completedPseudoDiffOpLinearCartanIndex e := by
  rw [completedPseudoDiffOpLinearCartanIndex_trans, completedPseudoDiffOpLinearCartanIndex_trans,
    completedPseudoDiffOpLinearCartanIndex_symm]
  omega

theorem completedPseudoDiffOpLinearCartanIndex_eq_zero_of_map_standard
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (h : mapCompletedPseudoDiffOpLatticeLinear e
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
        standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) :
    completedPseudoDiffOpLinearCartanIndex e = 0 := by
  unfold completedPseudoDiffOpLinearCartanIndex
  rw [h]
  exact completedPseudoDiffOpCartanIndex_self _

def completedPseudoDiffOpCoordinateShear (i j : Fin r) (hij : i ≠ j)
    (q : CompletedPseudoDiffOp K) :
    (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K) where
  toFun x k := if k = j then x j + x i * q else x k
  invFun x k := if k = j then x j + x i * (-q) else x k
  left_inv x := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [hij]
    · simp [hk]
  right_inv x := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [hij]
    · simp [hk]
  map_add' x y := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
      noncomm_ring
    · simp [hk]
  map_smul' a x := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
      noncomm_ring
    · simp [hk]

@[simp] theorem completedPseudoDiffOpCoordinateShear_apply (i j : Fin r) (hij : i ≠ j)
    (q : CompletedPseudoDiffOp K) (x : Fin r → CompletedPseudoDiffOp K) (k : Fin r) :
    completedPseudoDiffOpCoordinateShear i j hij q x k =
      if k = j then x j + x i * q else x k := rfl

@[simp] theorem completedPseudoDiffOpCoordinateShear_symm_apply (i j : Fin r) (hij : i ≠ j)
    (q : CompletedPseudoDiffOp K) (x : Fin r → CompletedPseudoDiffOp K) (k : Fin r) :
    (completedPseudoDiffOpCoordinateShear i j hij q).symm x k =
      if k = j then x j + x i * (-q) else x k := rfl

theorem completedPseudoDiffOpCoordinateShear_symm (i j : Fin r) (hij : i ≠ j)
    (q : CompletedPseudoDiffOp K) :
    (completedPseudoDiffOpCoordinateShear i j hij q).symm = completedPseudoDiffOpCoordinateShear i j hij (-q) := by
  ext x k
  by_cases hk : k = j <;> simp [hk]

def completedPseudoDiffOpCoordinateSign (i : Fin r) :
    (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K) where
  toFun x k := if k = i then -x k else x k
  invFun x k := if k = i then -x k else x k
  left_inv x := by
    funext k
    by_cases hk : k = i <;> simp [hk]
  right_inv x := by
    funext k
    by_cases hk : k = i <;> simp [hk]
  map_add' x y := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [Pi.add_apply, if_pos, neg_add_rev]
      abel
    · simp [hk]
  map_smul' a x := by
    funext k
    by_cases hk : k = i <;> simp [hk]

@[simp] theorem completedPseudoDiffOpCoordinateSign_apply (i : Fin r)
    (x : Fin r → CompletedPseudoDiffOp K) (k : Fin r) :
    completedPseudoDiffOpCoordinateSign i x k = if k = i then -x k else x k := rfl

@[simp] theorem completedPseudoDiffOpCoordinateSign_symm_apply (i : Fin r)
    (x : Fin r → CompletedPseudoDiffOp K) (k : Fin r) :
    (completedPseudoDiffOpCoordinateSign i).symm x k = if k = i then -x k else x k := rfl

theorem completedPseudoDiffOpCoordinateSign_map_standard (i : Fin r) :
    mapCompletedPseudoDiffOpLatticeLinear (completedPseudoDiffOpCoordinateSign (K := K) i)
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
        standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext x
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hy ⊢
    intro k
    by_cases hk : k = i
    · simpa [hk] using neg_mem (hy k)
    · simpa [hk] using hy k
  · intro hx
    refine ⟨completedPseudoDiffOpCoordinateSign i x, ?_, ?_⟩
    · rw [mem_standardCompletedPseudoDiffOpLattice_iff] at hx ⊢
      intro k
      by_cases hk : k = i
      · simpa [hk] using neg_mem (hx k)
      · simpa [hk] using hx k
    · ext k
      by_cases hk : k = i <;> simp [hk]

theorem completedPseudoDiffOpCoordinateSign_conj_shear (i j : Fin r) (hij : i ≠ j)
    (q : CompletedPseudoDiffOp K) :
    (completedPseudoDiffOpCoordinateSign i).symm.trans
        ((completedPseudoDiffOpCoordinateShear i j hij q).trans (completedPseudoDiffOpCoordinateSign i)) =
      completedPseudoDiffOpCoordinateShear i j hij (-q) := by
  ext x k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki, hkj]

theorem completedPseudoDiffOpLinearCartanIndex_coordinateShear (i j : Fin r) (hij : i ≠ j)
    (q : CompletedPseudoDiffOp K) :
    completedPseudoDiffOpLinearCartanIndex (completedPseudoDiffOpCoordinateShear i j hij q) = 0 := by
  have hsign : completedPseudoDiffOpLinearCartanIndex (completedPseudoDiffOpCoordinateSign (K := K) i) = 0 :=
    completedPseudoDiffOpLinearCartanIndex_eq_zero_of_map_standard _ (completedPseudoDiffOpCoordinateSign_map_standard i)
  have hconj := congrArg completedPseudoDiffOpLinearCartanIndex
    (completedPseudoDiffOpCoordinateSign_conj_shear i j hij q)
  rw [completedPseudoDiffOpLinearCartanIndex_conj] at hconj
  have hinv := completedPseudoDiffOpLinearCartanIndex_trans
    (completedPseudoDiffOpCoordinateShear i j hij q) (completedPseudoDiffOpCoordinateShear i j hij q).symm
  rw [(completedPseudoDiffOpCoordinateShear i j hij q).self_trans_symm,
    completedPseudoDiffOpLinearCartanIndex_refl, completedPseudoDiffOpCoordinateShear_symm] at hinv
  omega

def completedPseudoDiffOpMatrixCartanIndex
    (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) : ℤ :=
  completedPseudoDiffOpLinearCartanIndex (completedPseudoDiffOpMatrixLinearEquiv A)

theorem completedPseudoDiffOpMatrixCartanIndex_mul
    (A B : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ) :
    completedPseudoDiffOpMatrixCartanIndex (A * B) =
      completedPseudoDiffOpMatrixCartanIndex A + completedPseudoDiffOpMatrixCartanIndex B := by
  unfold completedPseudoDiffOpMatrixCartanIndex
  rw [← completedPseudoDiffOpMatrixLinearEquiv_mul,
    completedPseudoDiffOpLinearCartanIndex_trans]

def differentialOperatorMatrixCartanIndex
    (A : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ) : ℤ :=
  completedPseudoDiffOpMatrixCartanIndex (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit A)

theorem differentialOperatorMatrixCartanIndex_mul
    (A B : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ) :
    differentialOperatorMatrixCartanIndex (A * B) =
      differentialOperatorMatrixCartanIndex A + differentialOperatorMatrixCartanIndex B := by
  unfold differentialOperatorMatrixCartanIndex
  rw [completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_mul,
    completedPseudoDiffOpMatrixCartanIndex_mul]

def differentialOperatorMatrixTransvection (i j : Fin r) (q : DiffOp K) :
    Matrix (Fin r) (Fin r) (DiffOp K) :=
  1 + Matrix.single i j q

def differentialOperatorMatrixTransvectionUnit (i j : Fin r) (hij : i ≠ j) (q : DiffOp K) :
    (Matrix (Fin r) (Fin r) (DiffOp K))ˣ where
  val := differentialOperatorMatrixTransvection i j q
  inv := differentialOperatorMatrixTransvection i j (-q)
  val_inv := by
    have hs : (Matrix.single i j q : Matrix (Fin r) (Fin r) (DiffOp K)) *
        Matrix.single i j (-q) = 0 := by
      funext a b
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      simp only [Matrix.single_apply]
      split_ifs <;> simp_all
    simp only [differentialOperatorMatrixTransvection, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hs, add_zero]
    rw [show 1 + Matrix.single i j q + Matrix.single i j (-q) =
        1 + (Matrix.single i j q + Matrix.single i j (-q)) by abel,
      ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]
  inv_val := by
    have hs : (Matrix.single i j (-q) : Matrix (Fin r) (Fin r) (DiffOp K)) *
        Matrix.single i j q = 0 := by
      funext a b
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      simp only [Matrix.single_apply]
      split_ifs <;> simp_all
    simp only [differentialOperatorMatrixTransvection, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hs, add_zero]
    rw [show 1 + Matrix.single i j (-q) + Matrix.single i j q =
        1 + (Matrix.single i j (-q) + Matrix.single i j q) by abel,
      ← Matrix.single_add, neg_add_cancel, Matrix.single_zero, add_zero]

@[simp] theorem differentialOperatorMatrixTransvectionUnit_val
    (i j : Fin r) (hij : i ≠ j) (q : DiffOp K) :
    (differentialOperatorMatrixTransvectionUnit i j hij q : Matrix (Fin r) (Fin r) (DiffOp K)) =
      differentialOperatorMatrixTransvection i j q := rfl

theorem completedPseudoDiffOpMatrixTransvectionLinearEquiv_eq_coordinateShear
    (i j : Fin r) (hij : i ≠ j) (q : DiffOp K) :
    completedPseudoDiffOpMatrixLinearEquiv
        (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
          (differentialOperatorMatrixTransvectionUnit i j hij q)) =
      completedPseudoDiffOpCoordinateShear i j hij (diffOpToCompletedPseudoRingHom q) := by
  have hval :
      (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
          (differentialOperatorMatrixTransvectionUnit i j hij q) :
        Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K)) =
      1 + Matrix.single i j (diffOpToCompletedPseudoRingHom q) := by
    change (diffOpToCompletedPseudoRingHom (K := K)).mapMatrix
        (1 + Matrix.single i j q) = _
    rw [(diffOpToCompletedPseudoRingHom (K := K)).mapMatrix.map_add,
      (diffOpToCompletedPseudoRingHom (K := K)).mapMatrix.map_one]
    congr 1
    exact Matrix.map_single i j q diffOpToCompletedPseudoRingHom
  ext x k
  change Matrix.vecMul x
      (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
          (differentialOperatorMatrixTransvectionUnit i j hij q) :
        Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K)) k = _
  rw [hval]
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  have hsingle : Matrix.vecMul x
      (Matrix.single i j (diffOpToCompletedPseudoRingHom q)) k =
      if k = j then x i * diffOpToCompletedPseudoRingHom q else 0 := by
    change (∑ a, x a * Matrix.single i j
      (diffOpToCompletedPseudoRingHom q) a k) = _
    by_cases hkj : k = j
    · subst k
      rw [if_pos rfl]
      rw [Finset.sum_eq_single i]
      · rw [Matrix.single_apply_same]
      · intro a _ hai
        rw [Matrix.single_apply_of_ne]
        simp
        exact fun h => hai h.1.symm
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [if_neg hkj]
      apply Finset.sum_eq_zero
      intro a _
      rw [Matrix.single_apply_of_ne]
      simp
      exact fun h => hkj h.2.symm
  change x k + Matrix.vecMul x
    (Matrix.single i j (diffOpToCompletedPseudoRingHom q)) k = _
  rw [hsingle]
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

theorem differentialOperatorMatrixCartanIndex_transvection
    (i j : Fin r) (hij : i ≠ j) (q : DiffOp K) :
    differentialOperatorMatrixCartanIndex (differentialOperatorMatrixTransvectionUnit i j hij q) = 0 := by
  unfold differentialOperatorMatrixCartanIndex completedPseudoDiffOpMatrixCartanIndex
  rw [completedPseudoDiffOpMatrixTransvectionLinearEquiv_eq_coordinateShear]
  exact completedPseudoDiffOpLinearCartanIndex_coordinateShear i j hij _

theorem differentialOperatorMatrixTransvection_mul (i k : Fin r) (q : DiffOp K)
    (P : Matrix (Fin r) (Fin r) (DiffOp K)) :
    differentialOperatorMatrixTransvection i k q * P = rowAdd i k q P := by
  rw [differentialOperatorMatrixTransvection, Matrix.add_mul, Matrix.one_mul]
  funext a b
  have hs : (Matrix.single i k q * P) a b =
      if a = i then q * P k b else 0 := by
    rw [Matrix.mul_apply]
    by_cases hai : a = i
    · subst a
      rw [if_pos rfl, Finset.sum_eq_single k]
      · rw [Matrix.single_apply_same]
      · intro c _ hck
        rw [Matrix.single_apply_of_ne]
        simp
        exact fun h => hck h.2.symm
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · rw [if_neg hai]
      apply Finset.sum_eq_zero
      intro c _
      rw [Matrix.single_apply_of_ne]
      simp
      exact fun h => hai h.1.symm
  change P a b + (Matrix.single i k q * P) a b = _
  rw [hs]
  by_cases hai : a = i
  · subst a
    rw [if_pos rfl, rowAdd_apply_self]
  · rw [if_neg hai, add_zero, rowAdd_apply_of_ne k q P b hai]

theorem mul_differentialOperatorMatrixTransvection (j k : Fin r) (q : DiffOp K)
    (P : Matrix (Fin r) (Fin r) (DiffOp K)) :
    P * differentialOperatorMatrixTransvection k j q = colAdd j k q P := by
  rw [differentialOperatorMatrixTransvection, Matrix.mul_add, Matrix.mul_one]
  funext a b
  have hs : (P * Matrix.single k j q) a b =
      if b = j then P a k * q else 0 := by
    rw [Matrix.mul_apply]
    by_cases hbj : b = j
    · subst b
      rw [if_pos rfl, Finset.sum_eq_single k]
      · rw [Matrix.single_apply_same]
      · intro c _ hck
        rw [Matrix.single_apply_of_ne]
        simp
        exact fun h => hck h.1.symm
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · rw [if_neg hbj]
      apply Finset.sum_eq_zero
      intro c _
      rw [Matrix.single_apply_of_ne]
      simp
      exact fun h => hbj h.2.symm
  change P a b + (P * Matrix.single k j q) a b = _
  rw [hs]
  by_cases hbj : b = j
  · subst b
    rw [if_pos rfl, colAdd_apply_self]
  · rw [if_neg hbj, add_zero, colAdd_apply_of_ne k q P a hbj]

theorem exists_operatorMatrixUnit_cartanIndex_eq_of_rowColEquiv
    (A : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ)
    {P : Matrix (Fin r) (Fin r) (DiffOp K)}
    (h : RowColEquiv (A : Matrix (Fin r) (Fin r) (DiffOp K)) P) :
    ∃ B : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ,
      (B : Matrix (Fin r) (Fin r) (DiffOp K)) = P ∧
        differentialOperatorMatrixCartanIndex B = differentialOperatorMatrixCartanIndex A := by
  induction h with
  | refl => exact ⟨A, rfl, rfl⟩
  | tail hPQ hstep ih =>
      obtain ⟨B, hB, hindex⟩ := ih
      rcases hstep with ⟨i, k, q, hik, rfl⟩ | ⟨j, k, q, hjk, rfl⟩
      · let E := differentialOperatorMatrixTransvectionUnit (K := K) i k hik q
        refine ⟨E * B, ?_, ?_⟩
        · change differentialOperatorMatrixTransvection i k q *
              (B : Matrix (Fin r) (Fin r) (DiffOp K)) = rowAdd i k q _
          rw [hB, differentialOperatorMatrixTransvection_mul]
        · rw [differentialOperatorMatrixCartanIndex_mul,
            differentialOperatorMatrixCartanIndex_transvection, zero_add, hindex]
      · let E := differentialOperatorMatrixTransvectionUnit (K := K) k j (Ne.symm hjk) q
        refine ⟨B * E, ?_, ?_⟩
        · change (B : Matrix (Fin r) (Fin r) (DiffOp K)) *
              differentialOperatorMatrixTransvection k j q = colAdd j k q _
          rw [hB, mul_differentialOperatorMatrixTransvection]
        · rw [differentialOperatorMatrixCartanIndex_mul,
            differentialOperatorMatrixCartanIndex_transvection, add_zero, hindex]

theorem degree_eq_zero_of_diagonalized_operatorMatrixUnit
    (B : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ)
    (hdiag : Diagonalized (B : Matrix (Fin r) (Fin r) (DiffOp K))) :
    (∀ i j, degree ((B : Matrix (Fin r) (Fin r) (DiffOp K)) i j) = 0) ∧
      (∀ i j, degree ((↑(B⁻¹) : Matrix (Fin r) (Fin r) (DiffOp K)) i j) = 0) := by
  have degree_eq_zero_of_unit {p : DiffOp K} (hp : IsUnit p) : degree p = 0 := by
    obtain ⟨u, rfl⟩ := hp
    have hu : ((u : DiffOp K) ≠ 0) := Units.ne_zero u
    have huinv : ((↑u⁻¹ : DiffOp K) ≠ 0) := Units.ne_zero u⁻¹
    have hdeg := degree_mul hu huinv
    rw [Units.mul_inv] at hdeg
    have hone : degree (1 : DiffOp K) = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply degree_le_iff.mpr
      intro n hn
      rw [one_def, coeff_mono_of_ne 1 (Nat.ne_of_gt hn).symm]
    rw [hone] at hdeg
    exact (Nat.add_eq_zero_iff.mp hdeg.symm).1
  let P : Matrix (Fin r) (Fin r) (DiffOp K) := B
  let Q : Matrix (Fin r) (Fin r) (DiffOp K) :=
    (↑(B⁻¹) : Matrix (Fin r) (Fin r) (DiffOp K))
  have hdiagP : Diagonalized P := by
    simpa only [P] using hdiag
  have hPQ : P * Q = 1 := Units.mul_inv B
  have hQP : Q * P = 1 := Units.inv_mul B
  have hindep : RowIndep P := rowIndep_of_vecMul_inverse P Q fun v => by
    change Matrix.vecMul (Matrix.vecMul v P) Q = v
    rw [Matrix.vecMul_vecMul, hPQ, Matrix.vecMul_one]
  choose f hf using fun i => exists_ne_zero_of_rowIndep hindep i
  have hfinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hz : P b (f a) = 0 := (hdiagP a (f a) (hf a)).1 b (Ne.symm hne)
    rw [hab] at hz
    exact hf b hz
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, rfl⟩
  let e : Fin r ≃ Fin r := Equiv.ofBijective f hfbij
  have he : ∀ i, P i (e i) ≠ 0 := hf
  have hPQentry (i b : Fin r) :
      P i (e i) * Q (e i) b = (1 : Matrix (Fin r) (Fin r) (DiffOp K)) i b := by
    calc
      P i (e i) * Q (e i) b = ∑ k, P i k * Q k b := by
        symm
        refine Finset.sum_eq_single (e i) (fun k _ hki => ?_)
          (fun hi => absurd (Finset.mem_univ (e i)) hi)
        rw [(hdiagP i (e i) (he i)).2 k hki, zero_mul]
      _ = (P * Q) i b := Matrix.mul_apply.symm
      _ = _ := congrFun (congrFun hPQ i) b
  have hQPentry (i : Fin r) :
      Q (e i) i * P i (e i) = 1 := by
    calc
      Q (e i) i * P i (e i) = ∑ k, Q (e i) k * P k (e i) := by
        symm
        refine Finset.sum_eq_single i (fun k _ hki => ?_)
          (fun hi => absurd (Finset.mem_univ i) hi)
        rw [(hdiagP i (e i) (he i)).1 k hki, mul_zero]
      _ = (Q * P) (e i) (e i) := Matrix.mul_apply.symm
      _ = (1 : Matrix (Fin r) (Fin r) (DiffOp K)) (e i) (e i) :=
        congrFun (congrFun hQP (e i)) (e i)
      _ = 1 := by simp
  have hpivotUnit (i : Fin r) : IsUnit (P i (e i)) := by
    refine ⟨⟨P i (e i), Q (e i) i, ?_, ?_⟩, rfl⟩
    · simpa using hPQentry i i
    · exact hQPentry i
  have hPdeg : ∀ i j, degree (P i j) = 0 := by
    intro i j
    by_cases hij : j = e i
    · subst j
      exact degree_eq_zero_of_unit (hpivotUnit i)
    · rw [(hdiagP i (e i) (he i)).2 j hij, degree_zero]
  have hQoff (i b : Fin r) (hib : b ≠ i) : Q (e i) b = 0 := by
    have hpzero : P i (e i) * Q (e i) b = 0 := by
      rw [hPQentry]
      simp [Ne.symm hib]
    have h := congrArg (fun z => Q (e i) i * z) hpzero
    simpa only [mul_zero, ← mul_assoc, hQPentry, one_mul] using h
  have hQdeg : ∀ a b, degree (Q a b) = 0 := by
    intro a b
    obtain ⟨i, rfl⟩ := e.surjective a
    by_cases hib : b = i
    · subst b
      have hunit : IsUnit (Q (e i) i) := by
        refine ⟨⟨Q (e i) i, P i (e i), hQPentry i, ?_⟩, rfl⟩
        simpa using hPQentry i i
      exact degree_eq_zero_of_unit hunit
    · rw [hQoff i b hib, degree_zero]
  exact ⟨hPdeg, hQdeg⟩

theorem map_standard_of_diagonalized_operatorMatrixUnit
    (B : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ)
    (hdiag : Diagonalized (B : Matrix (Fin r) (Fin r) (DiffOp K))) :
    mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv
          (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit B))
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
  let A := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit B
  obtain ⟨hBdeg, hBinvdeg⟩ := degree_eq_zero_of_diagonalized_operatorMatrixUnit B hdiag
  have hforward :
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv A)
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))).carrier ≤
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier :=
    (mapMatrix_standard_carrier_le_iff A).2 fun i j => by
      have hentry :
          (A : Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K)) i j =
            diffOpToCompletedPseudoRingHom
              ((B : Matrix (Fin r) (Fin r) (DiffOp K)) i j) := rfl
      rw [hentry]
      rw [diffOpToCompletedPseudoRingHom_mem_integer_iff]
      exact Or.inr (hBdeg i j)
  have hbackward :
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier ≤
      (mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpMatrixLinearEquiv A)
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))).carrier := by
    have h := (standard_carrier_le_leftScale_mapMatrix_iff
      (1 : (CompletedPseudoDiffOp K)ˣ) A).2 (fun i j => ?_)
    · simpa only [leftScaleCompletedPseudoDiffOpLattice_one] using h
    · change (1 : CompletedPseudoDiffOp K) *
          (A⁻¹ : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ).1 i j ∈
        CompletedPseudoDiffOpInteger (K := K)
      rw [one_mul]
      have hentry :
          (A⁻¹ : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ).1 i j =
            diffOpToCompletedPseudoRingHom
              ((↑(B⁻¹) : Matrix (Fin r) (Fin r) (DiffOp K)) i j) := rfl
      rw [hentry]
      rw [diffOpToCompletedPseudoRingHom_mem_integer_iff]
      exact Or.inr (hBinvdeg i j)
  apply CompletedPseudoDiffOpLattice.ext
  exact le_antisymm hforward hbackward

theorem differentialOperatorMatrixCartanIndex_eq_zero_of_diagonalized
    (B : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ)
    (hdiag : Diagonalized (B : Matrix (Fin r) (Fin r) (DiffOp K))) :
    differentialOperatorMatrixCartanIndex B = 0 := by
  unfold differentialOperatorMatrixCartanIndex completedPseudoDiffOpMatrixCartanIndex
  exact completedPseudoDiffOpLinearCartanIndex_eq_zero_of_map_standard _
    (map_standard_of_diagonalized_operatorMatrixUnit B hdiag)

theorem differentialOperatorMatrixCartanIndex_eq_zero
    (A : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ) :
    differentialOperatorMatrixCartanIndex A = 0 := by
  obtain ⟨P, hAP, hdiag⟩ := exists_diagonalized
    (A : Matrix (Fin r) (Fin r) (DiffOp K))
  obtain ⟨B, hB, hindex⟩ := exists_operatorMatrixUnit_cartanIndex_eq_of_rowColEquiv A hAP
  have hdiagB : Diagonalized (B : Matrix (Fin r) (Fin r) (DiffOp K)) := by
    rw [hB]
    exact hdiag
  have hzero := differentialOperatorMatrixCartanIndex_eq_zero_of_diagonalized B hdiagB
  omega

theorem differentialOperatorMatrixCartanBalance
    (A : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ) :
    ∑ i, completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit A))
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i = 0 := by
  exact differentialOperatorMatrixCartanIndex_eq_zero A

theorem variationalOreCartanBalance
    {C : Type*} [Field C] [Algebra C K] [IsConstantBase C K]
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    ∑ i, completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b))
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i = 0 := by
  exact differentialOperatorMatrixCartanBalance
    (variationalOreOperatorMatrixUnit σ.fixes σ.deriv_comm b)

/-- Every finite iterate of the canonical variational Ore action has exactly balanced dominant
Cartan coordinates. -/
theorem variationalOreCartanBalance_pow
    {C : Type*} [Field C] [Algebra C K] [IsConstantBase C K]
    (σ : DifferentialFieldAut C K) (n : ℕ)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    ∑ i, completedPseudoDiffOpDominantRelativePosition
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
        (mapCompletedPseudoDiffOpLatticeLinear
          (completedPseudoDiffOpMatrixLinearEquiv
            (variationalOreCompletedMatrixUnit (σ ^ n).fixes (σ ^ n).deriv_comm b))
          (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i = 0 := by
  exact variationalOreCartanBalance (σ ^ n) b

/-- Finite differential generation supplies one actual finite Ore basis in which every iterate of
every bundled differential automorphism has exactly balanced dominant Cartan coordinates. -/
theorem exists_variationalOre_finiteBasis_cartanBalance
    {C : Type*} [Field C] [Algebra C K] [IsConstantBase C K]
    {s : ℕ} {y : Fin s → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤)
    (σ : DifferentialFieldAut C K) :
    ∃ r : ℕ, ∃ b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K),
      ∀ n : ℕ,
        ∑ i, completedPseudoDiffOpDominantRelativePosition
            (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))
            (mapCompletedPseudoDiffOpLatticeLinear
              (completedPseudoDiffOpMatrixLinearEquiv
                (variationalOreCompletedMatrixUnit
                  (σ ^ n).fixes (σ ^ n).deriv_comm b))
              (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) i = 0 := by
  obtain ⟨r, ⟨b⟩⟩ := exists_fin_basis_variationalOreModule hy
  exact ⟨r, b, fun n => variationalOreCartanBalance_pow σ n b⟩

end

end GaloisForLFunctions.HTGeometry.DiffOp
