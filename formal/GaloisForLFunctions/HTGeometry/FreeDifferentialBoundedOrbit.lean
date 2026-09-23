import GaloisForLFunctions.HTGeometry.FreeDifferentialCartanTranslationSpeed

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem antitone_sum_zero_abs_le_card_mul_top {r : ℕ}
    (v : Fin (r + 1) → ℝ) (hv : Antitone v) (hsum : ∑ i, v i = 0)
    (i : Fin (r + 1)) :
    |v i| ≤ (r + 1 : ℝ) * v 0 := by
  have htop : 0 ≤ v 0 := by
    by_contra h
    have hneg : ∀ j ∈ (Finset.univ : Finset (Fin (r + 1))), v j < 0 := by
      intro j _
      exact lt_of_le_of_lt (hv (Fin.zero_le j)) (lt_of_not_ge h)
    have hsneg := Finset.sum_neg hneg (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (r + 1))).Nonempty)
    rw [hsum] at hsneg
    exact (lt_irrefl 0) hsneg
  have hiTop : v i ≤ v 0 := hv (Fin.zero_le i)
  have hsumErase : ∑ j ∈ Finset.univ.erase i, v j = -v i := by
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := v)
      (Finset.mem_univ i)
    rw [hsum] at hsplit
    linarith
  have herase : ∑ j ∈ Finset.univ.erase i, v j ≤
      ((Finset.univ.erase i).card : ℝ) * v 0 := by
    calc
      ∑ j ∈ Finset.univ.erase i, v j ≤
          ∑ _j ∈ Finset.univ.erase i, v 0 := by
            exact Finset.sum_le_sum fun j _ => hv (Fin.zero_le j)
      _ = ((Finset.univ.erase i).card : ℝ) * v 0 := by
            simp [nsmul_eq_mul]
  have hcard : (Finset.univ.erase i).card = r := by simp
  rw [hsumErase, hcard] at herase
  rw [abs_le]
  constructor <;> nlinarith

theorem euclideanNorm_le_card_sq_mul_top_of_antitone_sum_zero {r : ℕ}
    (v : Fin (r + 1) → ℝ) (hv : Antitone v) (hsum : ∑ i, v i = 0) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (r + 1)))‖ ≤
      (r + 1 : ℝ) ^ (2 : ℕ) * v 0 := by
  have htop : 0 ≤ v 0 := by
    by_contra h
    have hneg : ∀ j ∈ (Finset.univ : Finset (Fin (r + 1))), v j < 0 := by
      intro j _
      exact lt_of_le_of_lt (hv (Fin.zero_le j)) (lt_of_not_ge h)
    have hsneg := Finset.sum_neg hneg (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (r + 1))).Nonempty)
    rw [hsum] at hsneg
    exact (lt_irrefl 0) hsneg
  rw [EuclideanSpace.norm_eq]
  have hsquares : ∑ i : Fin (r + 1), ‖v i‖ ^ (2 : ℕ) ≤
      (r + 1 : ℝ) * (((r + 1 : ℝ) * v 0) ^ (2 : ℕ)) := by
    calc
      ∑ i : Fin (r + 1), ‖v i‖ ^ (2 : ℕ) ≤
          ∑ _i : Fin (r + 1), (((r + 1 : ℝ) * v 0) ^ (2 : ℕ)) := by
            apply Finset.sum_le_sum
            intro i _
            simp only [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (antitone_sum_zero_abs_le_card_mul_top v hv hsum i) 2
      _ = (r + 1 : ℝ) * (((r + 1 : ℝ) * v 0) ^ (2 : ℕ)) := by
            simp [nsmul_eq_mul]
  have hroot := Real.sqrt_le_sqrt hsquares
  have hnonneg : 0 ≤ (r + 1 : ℝ) ^ (2 : ℕ) * v 0 := by positivity
  apply le_trans hroot
  rw [Real.sqrt_le_iff]
  constructor
  · exact hnonneg
  · have hr : (1 : ℝ) ≤ r + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
    have hdiff : 0 ≤ (r + 1 : ℝ) ^ (3 : ℕ) * ((r + 1 : ℝ) - 1) * (v 0) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (pow_nonneg (by positivity) 3) (sub_nonneg.mpr hr))
        (sq_nonneg (v 0))
    nlinarith

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C] {r : ℕ}

def FreeDifferentialOrderPowersBounded
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, freeDifferentialOrder (σ ^ n) ≤ B

def FreeDifferentialEuclideanOrbitBounded
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ,
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
      (freeDifferentialProjectiveBasePoint (C := C) (r + 1))
      ((σ ^ n).projectiveBuildingAction
        (freeVariationalOreBasis (C := C) (r := r + 1))
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1))) ≤ B

theorem freeDifferentialOrder_le_euclideanOrbitDistance
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) (n : ℕ) :
    (freeDifferentialOrder (σ ^ n) : ℝ) ≤
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1))
        ((σ ^ n).projectiveBuildingAction
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (freeDifferentialProjectiveBasePoint (C := C) (r + 1))) := by
  let x := freeDifferentialProjectiveBasePoint (C := C) (r + 1)
  let y := (σ ^ n).projectiveBuildingAction
    (freeVariationalOreBasis (C := C) (r := r + 1)) x
  let v := (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y x :
    Fin (r + 1) → ℝ)
  have hcoord := DiffOp.abs_apply_le_euclideanNorm v (0 : Fin (r + 1))
  rw [freeDifferentialOrder_eq_reverseProjectiveEuclideanRelativePosition_zero (σ ^ n)]
  change v 0 ≤ _
  calc
    v 0 ≤ |v 0| := le_abs_self _
    _ ≤ ‖WithLp.toLp 2 v‖ := hcoord
    _ = DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y := by
      rw [DiffOp.differentialVariationalProjectiveEuclideanVertexDistance]
      exact DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_norm_comm x y

theorem euclideanOrbitDistance_le_card_sq_mul_freeDifferentialOrder
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) (n : ℕ) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (freeDifferentialProjectiveBasePoint (C := C) (r + 1))
        ((σ ^ n).projectiveBuildingAction
          (freeVariationalOreBasis (C := C) (r := r + 1))
          (freeDifferentialProjectiveBasePoint (C := C) (r + 1))) ≤
      (r + 1 : ℝ) ^ (2 : ℕ) * freeDifferentialOrder (σ ^ n) := by
  let x := freeDifferentialProjectiveBasePoint (C := C) (r + 1)
  let y := (σ ^ n).projectiveBuildingAction
    (freeVariationalOreBasis (C := C) (r := r + 1)) x
  let v := (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y x :
    Fin (r + 1) → ℝ)
  have hv : Antitone v :=
    DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_antitone y x
  have hsum : ∑ i, v i = 0 :=
    DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_sum_eq_zero y x
  have hnorm := euclideanNorm_le_card_sq_mul_top_of_antitone_sum_zero v hv hsum
  have htop := freeDifferentialOrder_eq_reverseProjectiveEuclideanRelativePosition_zero (σ ^ n)
  change _ ≤ (r + 1 : ℝ) ^ (2 : ℕ) * (freeDifferentialOrder (σ ^ n) : ℝ)
  rw [DiffOp.differentialVariationalProjectiveEuclideanVertexDistance]
  rw [← DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_norm_comm x y]
  change ‖WithLp.toLp 2 v‖ ≤ _
  rw [htop]
  exact hnorm

theorem freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded
    (σ : FreeAut (C := C) (ι := Fin (r + 1))) :
    FreeDifferentialEuclideanOrbitBounded σ ↔
      FreeDifferentialOrderPowersBounded σ := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, B ≤ N := exists_nat_ge B
    refine ⟨N, fun n => ?_⟩
    exact_mod_cast le_trans (freeDifferentialOrder_le_euclideanOrbitDistance σ n)
      (le_trans (hB n) hN)
  · rintro ⟨N, hN⟩
    refine ⟨(r + 1 : ℝ) ^ (2 : ℕ) * N, fun n => ?_⟩
    exact le_trans (euclideanOrbitDistance_le_card_sq_mul_freeDifferentialOrder σ n)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hN n) (by positivity))

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
