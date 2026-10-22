import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticThirdInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem thirdInitialForm5_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm5
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow5 ((361/25)*v) := by
  simp only [thirdInitialForm5,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega)]
  simp only [thirdInitialRow5,mul_pow]

theorem thirdInitialForm6_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm6
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow6 ((361/25)*v) := by
  simp only [thirdInitialForm6,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega)]
  simp only [thirdInitialRow6,mul_pow]

theorem thirdInitialForm7_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm7
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow7 ((361/25)*v) := by
  simp only [thirdInitialForm7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega)]
  simp only [thirdInitialRow7,mul_pow]

theorem thirdInitialForm8_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm8
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow8 ((361/25)*v) := by
  simp only [thirdInitialForm8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega)]
  simp only [thirdInitialRow8,mul_pow]

theorem thirdInitialForm9_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm9
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow9 ((361/25)*v) := by
  simp only [thirdInitialForm9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega)]
  simp only [thirdInitialRow9,mul_pow]

theorem thirdInitialForm10_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm10
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow10 ((361/25)*v) := by
  simp only [thirdInitialForm10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega)]
  simp only [thirdInitialRow10,mul_pow]

theorem thirdInitialForm11_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm11
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow11 ((361/25)*v) := by
  simp only [thirdInitialForm11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega)]
  simp only [thirdInitialRow11,mul_pow]

theorem thirdInitialForm12_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm12
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow12 ((361/25)*v) := by
  simp only [thirdInitialForm12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega)]
  simp only [thirdInitialRow12,mul_pow]

theorem thirdInitialForm13_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm13
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow13 ((361/25)*v) := by
  simp only [thirdInitialForm13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega)]
  simp only [thirdInitialRow13,mul_pow]

theorem thirdInitialForm14_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm14
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow14 ((361/25)*v) := by
  simp only [thirdInitialForm14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega)]
  simp only [thirdInitialRow14,mul_pow]

theorem thirdInitialForm15_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm15
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow15 ((361/25)*v) := by
  simp only [thirdInitialForm15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega)]
  simp only [thirdInitialRow15,mul_pow]

theorem thirdInitialForm16_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm16
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow16 ((361/25)*v) := by
  simp only [thirdInitialForm16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega)]
  simp only [thirdInitialRow16,mul_pow]

theorem thirdInitialForm17_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm17
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow17 ((361/25)*v) := by
  simp only [thirdInitialForm17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega)]
  simp only [thirdInitialRow17,mul_pow]

theorem thirdInitialForm18_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm18
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow18 ((361/25)*v) := by
  simp only [thirdInitialForm18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega)]
  simp only [thirdInitialRow18,mul_pow]

theorem thirdInitialForm19_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm19
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow19 ((361/25)*v) := by
  simp only [thirdInitialForm19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega)]
  simp only [thirdInitialRow19,mul_pow]

theorem thirdInitialForm20_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm20
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow20 ((361/25)*v) := by
  simp only [thirdInitialForm20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega)]
  simp only [thirdInitialRow20,mul_pow]

theorem thirdInitialForm21_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm21
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow21 ((361/25)*v) := by
  simp only [thirdInitialForm21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow21,mul_pow]

theorem thirdInitialForm22_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm22
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow22 ((361/25)*v) := by
  simp only [thirdInitialForm22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow22,mul_pow]

theorem thirdInitialForm23_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm23
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow23 ((361/25)*v) := by
  simp only [thirdInitialForm23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow23,mul_pow]

theorem thirdInitialForm24_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm24
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow24 ((361/25)*v) := by
  simp only [thirdInitialForm24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 0 (by omega),kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow24,mul_pow]

theorem thirdInitialForm25_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm25
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow25 ((361/25)*v) := by
  simp only [thirdInitialForm25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow25,mul_pow]

theorem thirdInitialForm26_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm26
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow26 ((361/25)*v) := by
  simp only [thirdInitialForm26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 1 (by omega),kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow26,mul_pow]

theorem thirdInitialForm27_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm27
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow27 ((361/25)*v) := by
  simp only [thirdInitialForm27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow27,mul_pow]

theorem thirdInitialForm28_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm28
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow28 ((361/25)*v) := by
  simp only [thirdInitialForm28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 2 (by omega),kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow28,mul_pow]

theorem thirdInitialForm29_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm29
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow29 ((361/25)*v) := by
  simp only [thirdInitialForm29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow29,mul_pow]

theorem thirdInitialForm30_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm30
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow30 ((361/25)*v) := by
  simp only [thirdInitialForm30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 3 (by omega),kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow30,mul_pow]

theorem thirdInitialForm31_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm31
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow31 ((361/25)*v) := by
  simp only [thirdInitialForm31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow31,mul_pow]

theorem thirdInitialForm32_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm32
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow32 ((361/25)*v) := by
  simp only [thirdInitialForm32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 4 (by omega),kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow32,mul_pow]

theorem thirdInitialForm33_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm33
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow33 ((361/25)*v) := by
  simp only [thirdInitialForm33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow33,mul_pow]

theorem thirdInitialForm34_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm34
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow34 ((361/25)*v) := by
  simp only [thirdInitialForm34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 5 (by omega),kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow34,mul_pow]

theorem thirdInitialForm35_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm35
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow35 ((361/25)*v) := by
  simp only [thirdInitialForm35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow35,mul_pow]

theorem thirdInitialForm36_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm36
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow36 ((361/25)*v) := by
  simp only [thirdInitialForm36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 6 (by omega),kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow36,mul_pow]

theorem thirdInitialForm37_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm37
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow37 ((361/25)*v) := by
  simp only [thirdInitialForm37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow37,mul_pow]

theorem thirdInitialForm38_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm38
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow38 ((361/25)*v) := by
  simp only [thirdInitialForm38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 7 (by omega),kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow38,mul_pow]

theorem thirdInitialForm39_reconstruction (v : ℝ) :
    kineticBernstein 8 (fun B => thirdInitialForm39
      (fun b => (361/25)^b*degreeElevationCoefficient 8 b B)) v=
        thirdInitialRow39 ((361/25)*v) := by
  simp only [thirdInitialForm39,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 8 8 (by omega)]
  simp only [thirdInitialRow39,mul_pow]

def thirdInitialTensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 34 (fun A => kineticBernstein 8 (thirdInitialTensorCoefficient A) v) t

theorem thirdInitialTensorValue_reconstruction (t v : ℝ) :
    thirdInitialTensorValue t v=thirdInitialQuotient ((4/5)*t) ((361/25)*v) := by
  delta thirdInitialTensorValue thirdInitialTensorCoefficient thirdInitialClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    thirdInitialForm5_reconstruction,thirdInitialForm6_reconstruction,thirdInitialForm7_reconstruction,thirdInitialForm8_reconstruction,thirdInitialForm9_reconstruction,thirdInitialForm10_reconstruction,thirdInitialForm11_reconstruction,thirdInitialForm12_reconstruction,thirdInitialForm13_reconstruction,thirdInitialForm14_reconstruction,thirdInitialForm15_reconstruction,thirdInitialForm16_reconstruction,thirdInitialForm17_reconstruction,thirdInitialForm18_reconstruction,thirdInitialForm19_reconstruction,thirdInitialForm20_reconstruction,thirdInitialForm21_reconstruction,thirdInitialForm22_reconstruction,thirdInitialForm23_reconstruction,thirdInitialForm24_reconstruction,thirdInitialForm25_reconstruction,thirdInitialForm26_reconstruction,thirdInitialForm27_reconstruction,thirdInitialForm28_reconstruction,thirdInitialForm29_reconstruction,thirdInitialForm30_reconstruction,thirdInitialForm31_reconstruction,thirdInitialForm32_reconstruction,thirdInitialForm33_reconstruction,thirdInitialForm34_reconstruction,thirdInitialForm35_reconstruction,thirdInitialForm36_reconstruction,thirdInitialForm37_reconstruction,thirdInitialForm38_reconstruction,thirdInitialForm39_reconstruction]
  rw [kineticBernstein_degree 34 (5-5) (by omega),kineticBernstein_degree 34 (6-5) (by omega),kineticBernstein_degree 34 (7-5) (by omega),kineticBernstein_degree 34 (8-5) (by omega),kineticBernstein_degree 34 (9-5) (by omega),kineticBernstein_degree 34 (10-5) (by omega),kineticBernstein_degree 34 (11-5) (by omega),kineticBernstein_degree 34 (12-5) (by omega),kineticBernstein_degree 34 (13-5) (by omega),kineticBernstein_degree 34 (14-5) (by omega),kineticBernstein_degree 34 (15-5) (by omega),kineticBernstein_degree 34 (16-5) (by omega),kineticBernstein_degree 34 (17-5) (by omega),kineticBernstein_degree 34 (18-5) (by omega),kineticBernstein_degree 34 (19-5) (by omega),kineticBernstein_degree 34 (20-5) (by omega),kineticBernstein_degree 34 (21-5) (by omega),kineticBernstein_degree 34 (22-5) (by omega),kineticBernstein_degree 34 (23-5) (by omega),kineticBernstein_degree 34 (24-5) (by omega),kineticBernstein_degree 34 (25-5) (by omega),kineticBernstein_degree 34 (26-5) (by omega),kineticBernstein_degree 34 (27-5) (by omega),kineticBernstein_degree 34 (28-5) (by omega),kineticBernstein_degree 34 (29-5) (by omega),kineticBernstein_degree 34 (30-5) (by omega),kineticBernstein_degree 34 (31-5) (by omega),kineticBernstein_degree 34 (32-5) (by omega),kineticBernstein_degree 34 (33-5) (by omega),kineticBernstein_degree 34 (34-5) (by omega),kineticBernstein_degree 34 (35-5) (by omega),kineticBernstein_degree 34 (36-5) (by omega),kineticBernstein_degree 34 (37-5) (by omega),kineticBernstein_degree 34 (38-5) (by omega),kineticBernstein_degree 34 (39-5) (by omega)]
  simp only [thirdInitialQuotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

