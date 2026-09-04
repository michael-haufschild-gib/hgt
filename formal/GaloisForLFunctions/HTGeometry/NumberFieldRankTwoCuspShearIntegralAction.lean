import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspShearCovering

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The standard determinant-one upper shear over the number field. -/
def numberFieldRankTwoUpperShear (a : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, a; 0, 1]

omit [NumberField K] in
@[simp]
theorem numberFieldRankTwoUpperShear_det (a : K) :
    (numberFieldRankTwoUpperShear a).det = 1 := by
  simp [numberFieldRankTwoUpperShear, Matrix.det_fin_two]

/-- Conjugating a cusp-relative upper shear through its pseudo-basis frame. -/
def numberFieldRankTwoCuspShearConjugate
    (c : numberFieldRankTwoCuspType K) (a : K) :
    Matrix (Fin 2) (Fin 2) K :=
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  numberFieldRankTwoCuspFrame K v hv * numberFieldRankTwoUpperShear a *
    numberFieldRankTwoCuspFrameInv K v hv

@[simp]
theorem numberFieldRankTwoCuspShearConjugate_det
    (c : numberFieldRankTwoCuspType K) (a : K) :
    (numberFieldRankTwoCuspShearConjugate c a).det = 1 := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  rw [numberFieldRankTwoCuspShearConjugate, Matrix.det_mul, Matrix.det_mul,
    numberFieldRankTwoCuspFrame_det, numberFieldRankTwoUpperShear_det]
  have hdetInv : (numberFieldRankTwoCuspFrameInv K v hv).det = 1 := by
    have h := congrArg Matrix.det (numberFieldRankTwoCuspFrameInv_mul K v hv)
    rw [Matrix.det_mul, numberFieldRankTwoCuspFrame_det, Matrix.det_one] at h
    simpa using h
  rw [hdetInv]
  simp

/-- A shear-ideal coefficient times any product of two cusp coordinates is integral. -/
theorem exists_ringOfIntegers_eq_cuspShear_mul_coordinates
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c) (i j : Fin 2) :
    ∃ z : 𝓞 K, (z : K) = a *
      (numberFieldRankTwoCuspRepresentative K c).1 i *
      (numberFieldRankTwoCuspRepresentative K c).1 j := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  let Iu := numberFieldRankTwoCoordinateIdealUnit K v hv
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ↑Iu
  let J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ↑(Iu⁻¹ * Iu⁻¹)
  have hvi : v i ∈ I :=
    numberFieldRankTwo_mem_coordinateIdeal K v i
  have hvj : v j ∈ I :=
    numberFieldRankTwo_mem_coordinateIdeal K v j
  have hvivj : v i * v j ∈
      (↑(I * I) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.coe_mul]
    exact Submodule.mul_mem_mul hvi hvj
  have ha' : a ∈ J := by
    exact ha
  have hprod : a * (v i * v j) ∈
      (↑(J * (I * I)) : Submodule (𝓞 K) K) := by
    rw [FractionalIdeal.coe_mul]
    exact Submodule.mul_mem_mul ha' hvivj
  have hu : (Iu⁻¹ * Iu⁻¹) * (Iu * Iu) = 1 := by group
  have hideal : J * (I * I) = 1 := by
    dsimp [J, I]
    exact congrArg
      (fun L : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ =>
        (L : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) hu
  rw [hideal, FractionalIdeal.coe_one, Submodule.mem_one] at hprod
  obtain ⟨z, hz⟩ := hprod
  refine ⟨z, ?_⟩
  simpa [v, mul_assoc] using hz

/-- Every entry of a cusp-relative shear conjugate is an algebraic integer. -/
theorem exists_ringOfIntegers_eq_numberFieldRankTwoCuspShearConjugate_entry
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c) (i j : Fin 2) :
    ∃ z : 𝓞 K, (z : K) = numberFieldRankTwoCuspShearConjugate c a i j := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  fin_cases i <;> fin_cases j
  · obtain ⟨z, hz⟩ :=
      exists_ringOfIntegers_eq_cuspShear_mul_coordinates c a ha 0 1
    have hpair := numberFieldRankTwoCuspDual_pairing K v hv
    dsimp [v, hv] at hpair
    refine ⟨1 - z, ?_⟩
    change (1 : K) - (z : K) = _
    rw [hz]
    simp [numberFieldRankTwoCuspShearConjugate,
      numberFieldRankTwoUpperShear, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv]
    calc
      _ = ((numberFieldRankTwoCuspRepresentative K c).1 0 *
              numberFieldRankTwoCuspDual K
                (numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentative K c).2 0 +
            (numberFieldRankTwoCuspRepresentative K c).1 1 *
              numberFieldRankTwoCuspDual K
                (numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentative K c).2 1) -
            a * (numberFieldRankTwoCuspRepresentative K c).1 0 *
              (numberFieldRankTwoCuspRepresentative K c).1 1 := by rw [hpair]
      _ = _ := by ring
  · obtain ⟨z, hz⟩ :=
      exists_ringOfIntegers_eq_cuspShear_mul_coordinates c a ha 0 0
    refine ⟨z, ?_⟩
    rw [hz]
    simp [numberFieldRankTwoCuspShearConjugate,
      numberFieldRankTwoUpperShear, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv]
    ring
  · obtain ⟨z, hz⟩ :=
      exists_ringOfIntegers_eq_cuspShear_mul_coordinates c a ha 1 1
    refine ⟨-z, ?_⟩
    change -(z : K) = _
    rw [hz]
    simp [numberFieldRankTwoCuspShearConjugate,
      numberFieldRankTwoUpperShear, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv]
    ring
  · obtain ⟨z, hz⟩ :=
      exists_ringOfIntegers_eq_cuspShear_mul_coordinates c a ha 0 1
    have hpair := numberFieldRankTwoCuspDual_pairing K v hv
    dsimp [v, hv] at hpair
    refine ⟨1 + z, ?_⟩
    change (1 : K) + (z : K) = _
    rw [hz]
    simp [numberFieldRankTwoCuspShearConjugate,
      numberFieldRankTwoUpperShear, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv]
    calc
      _ = ((numberFieldRankTwoCuspRepresentative K c).1 0 *
              numberFieldRankTwoCuspDual K
                (numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentative K c).2 0 +
            (numberFieldRankTwoCuspRepresentative K c).1 1 *
              numberFieldRankTwoCuspDual K
                (numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentative K c).2 1) +
            a * (numberFieldRankTwoCuspRepresentative K c).1 0 *
              (numberFieldRankTwoCuspRepresentative K c).1 1 := by rw [hpair]
      _ = _ := by ring

/-- Integral matrix underlying a cusp-relative shear conjugate. -/
def numberFieldRankTwoCuspShearIntegralMatrix
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c) :
    Matrix (Fin 2) (Fin 2) (𝓞 K) :=
  fun i j => Classical.choose
    (exists_ringOfIntegers_eq_numberFieldRankTwoCuspShearConjugate_entry c a ha i j)

@[simp]
theorem numberFieldRankTwoCuspShearIntegralMatrix_baseChange
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c) :
    numberFieldRankTwoMatrixBaseChange K
        (numberFieldRankTwoCuspShearIntegralMatrix c a ha) =
      numberFieldRankTwoCuspShearConjugate c a := by
  ext i j
  exact Classical.choose_spec
    (exists_ringOfIntegers_eq_numberFieldRankTwoCuspShearConjugate_entry c a ha i j)

@[simp]
theorem numberFieldRankTwoCuspShearIntegralMatrix_det
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c) :
    (numberFieldRankTwoCuspShearIntegralMatrix c a ha).det = 1 := by
  apply NumberField.RingOfIntegers.coe_injective
  rw [map_one, ← numberFieldMatrixBaseChange_det]
  change (numberFieldRankTwoMatrixBaseChange K
    (numberFieldRankTwoCuspShearIntegralMatrix c a ha)).det = 1
  rw [numberFieldRankTwoCuspShearIntegralMatrix_baseChange,
    numberFieldRankTwoCuspShearConjugate_det]

/-- The integral special-linear transformation induced by a cusp-relative shear. -/
def numberFieldRankTwoCuspShearSpecialLinear
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c) :
    Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
  ⟨numberFieldRankTwoCuspShearIntegralMatrix c a ha,
    numberFieldRankTwoCuspShearIntegralMatrix_det c a ha⟩

/-- Transposed upper shear as a rational special-linear chart action. -/
def numberFieldRankTwoUpperShearTransposeSpecialLinear (a : K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨(numberFieldRankTwoUpperShear a).transpose, by
    rw [Matrix.det_transpose, numberFieldRankTwoUpperShear_det]⟩

/-- A cusp-relative shear performed in the chart is exactly an integral action before entering
the chart. -/
theorem numberFieldRankTwoCuspChart_shearSpecialLinear_smul
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c)
    (B : numberFieldArchimedeanPositiveForms K 2) :
    numberFieldRankTwoCuspChart
        (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentative K c).2
        ((transposeSpecialLinearOfDetOne
          (numberFieldRankTwoCuspShearIntegralMatrix c a ha)
          (numberFieldRankTwoCuspShearIntegralMatrix_det c a ha)) • B) =
      numberFieldRankTwoUpperShearTransposeSpecialLinear a •
        numberFieldRankTwoCuspChart
          (numberFieldRankTwoCuspRepresentative K c).1
          (numberFieldRankTwoCuspRepresentative K c).2 B := by
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  let F := numberFieldRankTwoCuspFrame K v hv
  let Fi := numberFieldRankTwoCuspFrameInv K v hv
  let U := numberFieldRankTwoUpperShear a
  let M := numberFieldRankTwoCuspShearIntegralMatrix c a ha
  let hM := numberFieldRankTwoCuspShearIntegralMatrix_det c a ha
  let h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    transposeSpecialLinearOfDetOne M hM
  have hbase :
      numberFieldMatrixBaseChange (h : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
        (F * U * Fi).transpose := by
    change numberFieldMatrixBaseChange M.transpose = (F * U * Fi).transpose
    change (numberFieldRankTwoMatrixBaseChange K M).transpose =
      (F * U * Fi).transpose
    rw [numberFieldRankTwoCuspShearIntegralMatrix_baseChange]
    rfl
  have hgroup :
      numberFieldRankTwoCuspSpecialLinear v hv * numberFieldSpecialLinearBaseChange h =
        numberFieldRankTwoUpperShearTransposeSpecialLinear a *
          numberFieldRankTwoCuspSpecialLinear v hv := by
    apply Subtype.ext
    change F.transpose *
        numberFieldMatrixBaseChange (h : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
      U.transpose * F.transpose
    rw [hbase]
    apply Matrix.transpose_injective
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Matrix.mul_assoc,
      show Fi * F = 1 by exact numberFieldRankTwoCuspFrameInv_mul K v hv,
      Matrix.mul_one]
  change numberFieldRankTwoCuspSpecialLinear v hv • (h • B) =
    numberFieldRankTwoUpperShearTransposeSpecialLinear a •
      (numberFieldRankTwoCuspSpecialLinear v hv • B)
  rw [← numberFieldSpecialLinearBaseChange_smul h B]
  rw [← mul_smul, hgroup, mul_smul]

end

end GaloisForLFunctions.HTGeometry
