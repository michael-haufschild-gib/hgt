import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspShearIntegralAction

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Conjugating a determinant-one unit diagonal through a cusp pseudo-basis frame. -/
def numberFieldRankTwoCuspUnitConjugate
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ) :
    Matrix (Fin 2) (Fin 2) K :=
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  numberFieldRankTwoCuspFrame K v hv *
      numberFieldRankTwoMatrixBaseChange K (numberFieldUnitDiagonal u) *
    numberFieldRankTwoCuspFrameInv K v hv

@[simp]
theorem numberFieldRankTwoCuspUnitConjugate_det
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ)
    (hu : ∏ i, u i = 1) :
    (numberFieldRankTwoCuspUnitConjugate c u).det = 1 := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  let D := numberFieldRankTwoMatrixBaseChange K (numberFieldUnitDiagonal u)
  have hD : D.det = 1 := by
    change (numberFieldMatrixBaseChange (numberFieldUnitDiagonal u)).det = 1
    rw [numberFieldMatrixBaseChange_det,
      det_numberFieldUnitDiagonal_eq_one u hu, map_one]
  have hdetInv : (numberFieldRankTwoCuspFrameInv K v hv).det = 1 := by
    have h := congrArg Matrix.det (numberFieldRankTwoCuspFrameInv_mul K v hv)
    rw [Matrix.det_mul, numberFieldRankTwoCuspFrame_det, Matrix.det_one] at h
    simpa using h
  rw [numberFieldRankTwoCuspUnitConjugate, Matrix.det_mul, Matrix.det_mul,
    numberFieldRankTwoCuspFrame_det, hD, hdetInv]
  simp

/-- A unit times one cusp coordinate and one dual coordinate is an algebraic integer. -/
theorem exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual
    (c : numberFieldRankTwoCuspType K) (e : (𝓞 K)ˣ) (i j : Fin 2) :
    ∃ z : 𝓞 K, (z : K) = (((e : 𝓞 K) : K) *
      (numberFieldRankTwoCuspRepresentative K c).1 i) *
      numberFieldRankTwoCuspDual K
        (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentative K c).2 j := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  have hvi : v i ∈ numberFieldRankTwoCoordinateIdeal K v :=
    numberFieldRankTwo_mem_coordinateIdeal K v i
  have hdj : numberFieldRankTwoCuspDual K v hv j ∈
      (↑((numberFieldRankTwoCoordinateIdealUnit K v hv)⁻¹) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
    numberFieldRankTwoCuspDual_mem_inv K v hv j
  obtain ⟨z, hz⟩ :=
    exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv hvi hdj
  refine ⟨(e : 𝓞 K) * z, ?_⟩
  change (((e : 𝓞 K) * z : 𝓞 K) : K) =
    ((((e : 𝓞 K) : K) * v i) * numberFieldRankTwoCuspDual K v hv j)
  calc
    (((e : 𝓞 K) * z : 𝓞 K) : K) =
        (((e : 𝓞 K) : K) * (z : K)) := map_mul (algebraMap (𝓞 K) K) _ _
    _ = _ := by rw [hz]; ring

/-- Every entry of a cusp-relative determinant-one unit conjugate is integral. -/
theorem exists_ringOfIntegers_eq_numberFieldRankTwoCuspUnitConjugate_entry
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ) (i j : Fin 2) :
    ∃ z : 𝓞 K, (z : K) = numberFieldRankTwoCuspUnitConjugate c u i j := by
  fin_cases i <;> fin_cases j
  · obtain ⟨z0, hz0⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 0) 0 0
    obtain ⟨z1, hz1⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 1) 1 1
    refine ⟨z0 + z1, ?_⟩
    change (z0 : K) + (z1 : K) = _
    rw [hz0, hz1]
    simp [numberFieldRankTwoCuspUnitConjugate,
      numberFieldRankTwoCuspFrame, numberFieldRankTwoCuspFrameInv,
      numberFieldRankTwoMatrixBaseChange, numberFieldUnitDiagonal,
      Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]
    ring
  · obtain ⟨z0, hz0⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 0) 0 1
    obtain ⟨z1, hz1⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 1) 0 1
    refine ⟨z0 - z1, ?_⟩
    change (z0 : K) - (z1 : K) = _
    rw [hz0, hz1]
    simp [numberFieldRankTwoCuspUnitConjugate,
      numberFieldRankTwoCuspFrame, numberFieldRankTwoCuspFrameInv,
      numberFieldRankTwoMatrixBaseChange, numberFieldUnitDiagonal,
      Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]
    ring
  · obtain ⟨z0, hz0⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 0) 1 0
    obtain ⟨z1, hz1⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 1) 1 0
    refine ⟨z0 - z1, ?_⟩
    change (z0 : K) - (z1 : K) = _
    rw [hz0, hz1]
    simp [numberFieldRankTwoCuspUnitConjugate,
      numberFieldRankTwoCuspFrame, numberFieldRankTwoCuspFrameInv,
      numberFieldRankTwoMatrixBaseChange, numberFieldUnitDiagonal,
      Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]
    ring
  · obtain ⟨z0, hz0⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 0) 1 1
    obtain ⟨z1, hz1⟩ :=
      exists_ringOfIntegers_eq_unit_mul_cuspCoordinate_mul_dual c (u 1) 0 0
    refine ⟨z0 + z1, ?_⟩
    change (z0 : K) + (z1 : K) = _
    rw [hz0, hz1]
    simp [numberFieldRankTwoCuspUnitConjugate,
      numberFieldRankTwoCuspFrame, numberFieldRankTwoCuspFrameInv,
      numberFieldRankTwoMatrixBaseChange, numberFieldUnitDiagonal,
      Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]
    ring

/-- Integral matrix underlying a cusp-relative determinant-one unit conjugate. -/
def numberFieldRankTwoCuspUnitIntegralMatrix
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ) :
    Matrix (Fin 2) (Fin 2) (𝓞 K) :=
  fun i j => Classical.choose
    (exists_ringOfIntegers_eq_numberFieldRankTwoCuspUnitConjugate_entry c u i j)

@[simp]
theorem numberFieldRankTwoCuspUnitIntegralMatrix_baseChange
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ) :
    numberFieldRankTwoMatrixBaseChange K
        (numberFieldRankTwoCuspUnitIntegralMatrix c u) =
      numberFieldRankTwoCuspUnitConjugate c u := by
  ext i j
  exact Classical.choose_spec
    (exists_ringOfIntegers_eq_numberFieldRankTwoCuspUnitConjugate_entry c u i j)

@[simp]
theorem numberFieldRankTwoCuspUnitIntegralMatrix_det
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ)
    (hu : ∏ i, u i = 1) :
    (numberFieldRankTwoCuspUnitIntegralMatrix c u).det = 1 := by
  apply NumberField.RingOfIntegers.coe_injective
  rw [map_one, ← numberFieldMatrixBaseChange_det]
  change (numberFieldRankTwoMatrixBaseChange K
    (numberFieldRankTwoCuspUnitIntegralMatrix c u)).det = 1
  rw [numberFieldRankTwoCuspUnitIntegralMatrix_baseChange,
    numberFieldRankTwoCuspUnitConjugate_det c u hu]

/-- Cusp-relative determinant-one unit conjugation as an integral special-linear matrix. -/
def numberFieldRankTwoCuspUnitSpecialLinear
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ)
    (hu : ∏ i, u i = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
  transposeSpecialLinearOfDetOne
    (numberFieldRankTwoCuspUnitIntegralMatrix c u)
    (numberFieldRankTwoCuspUnitIntegralMatrix_det c u hu)

/-- Unit balancing inside a cusp chart is exactly an integral action before entering the chart. -/
theorem numberFieldRankTwoCuspChart_unitSpecialLinear_smul
    (c : numberFieldRankTwoCuspType K) (u : Fin 2 → (𝓞 K)ˣ)
    (hu : ∏ i, u i = 1)
    (B : numberFieldArchimedeanPositiveForms K 2) :
    numberFieldRankTwoCuspChart
        (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentative K c).2
        (numberFieldRankTwoCuspUnitSpecialLinear c u hu • B) =
      numberFieldUnitSpecialLinear u hu •
        numberFieldRankTwoCuspChart
          (numberFieldRankTwoCuspRepresentative K c).1
          (numberFieldRankTwoCuspRepresentative K c).2 B := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  let F := numberFieldRankTwoCuspFrame K v hv
  let Fi := numberFieldRankTwoCuspFrameInv K v hv
  let D := numberFieldRankTwoMatrixBaseChange K (numberFieldUnitDiagonal u)
  let M := numberFieldRankTwoCuspUnitIntegralMatrix c u
  let hM := numberFieldRankTwoCuspUnitIntegralMatrix_det c u hu
  let h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    transposeSpecialLinearOfDetOne M hM
  have hbase :
      numberFieldMatrixBaseChange (h : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
        (F * D * Fi).transpose := by
    change (numberFieldRankTwoMatrixBaseChange K M).transpose =
      (F * D * Fi).transpose
    rw [numberFieldRankTwoCuspUnitIntegralMatrix_baseChange]
    rfl
  have hgroup :
      numberFieldRankTwoCuspSpecialLinear v hv * numberFieldSpecialLinearBaseChange h =
        numberFieldSpecialLinearBaseChange (numberFieldUnitSpecialLinear u hu) *
          numberFieldRankTwoCuspSpecialLinear v hv := by
    apply Subtype.ext
    change F.transpose *
        numberFieldMatrixBaseChange (h : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      D * F.transpose
    rw [hbase]
    apply Matrix.transpose_injective
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc,
      show Fi * F = 1 by exact numberFieldRankTwoCuspFrameInv_mul K v hv,
      Matrix.mul_one]
    change F * D = F * D.transpose
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp [D, numberFieldRankTwoMatrixBaseChange, numberFieldUnitDiagonal,
        Matrix.transpose_apply, hij, Ne.symm hij]
  change numberFieldRankTwoCuspSpecialLinear v hv • (h • B) =
    numberFieldUnitSpecialLinear u hu •
      (numberFieldRankTwoCuspSpecialLinear v hv • B)
  rw [← numberFieldSpecialLinearBaseChange_smul h B]
  rw [← numberFieldSpecialLinearBaseChange_smul
    (numberFieldUnitSpecialLinear u hu)
    (numberFieldRankTwoCuspSpecialLinear v hv • B)]
  rw [← mul_smul, hgroup, mul_smul]

end

end GaloisForLFunctions.HTGeometry
