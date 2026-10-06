import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInitialForm5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow5 ((361/25)*v) := by
  simp only [slopeInitialForm5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInitialRow5,mul_pow]

theorem slopeInitialForm6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow6 ((361/25)*v) := by
  simp only [slopeInitialForm6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInitialRow6,mul_pow]

theorem slopeInitialForm7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow7 ((361/25)*v) := by
  simp only [slopeInitialForm7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInitialRow7,mul_pow]

theorem slopeInitialForm8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow8 ((361/25)*v) := by
  simp only [slopeInitialForm8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInitialRow8,mul_pow]

theorem slopeInitialForm9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow9 ((361/25)*v) := by
  simp only [slopeInitialForm9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInitialRow9,mul_pow]

theorem slopeInitialForm10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow10 ((361/25)*v) := by
  simp only [slopeInitialForm10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInitialRow10,mul_pow]

theorem slopeInitialForm11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow11 ((361/25)*v) := by
  simp only [slopeInitialForm11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInitialRow11,mul_pow]

theorem slopeInitialForm12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow12 ((361/25)*v) := by
  simp only [slopeInitialForm12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInitialRow12,mul_pow]

theorem slopeInitialForm13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow13 ((361/25)*v) := by
  simp only [slopeInitialForm13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInitialRow13,mul_pow]

theorem slopeInitialForm14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow14 ((361/25)*v) := by
  simp only [slopeInitialForm14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInitialRow14,mul_pow]

theorem slopeInitialForm15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow15 ((361/25)*v) := by
  simp only [slopeInitialForm15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInitialRow15,mul_pow]

theorem slopeInitialForm16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow16 ((361/25)*v) := by
  simp only [slopeInitialForm16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInitialRow16,mul_pow]

theorem slopeInitialForm17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow17 ((361/25)*v) := by
  simp only [slopeInitialForm17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInitialRow17,mul_pow]

theorem slopeInitialForm18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow18 ((361/25)*v) := by
  simp only [slopeInitialForm18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInitialRow18,mul_pow]

theorem slopeInitialForm19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow19 ((361/25)*v) := by
  simp only [slopeInitialForm19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInitialRow19,mul_pow]

theorem slopeInitialForm20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow20 ((361/25)*v) := by
  simp only [slopeInitialForm20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInitialRow20,mul_pow]

theorem slopeInitialForm21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow21 ((361/25)*v) := by
  simp only [slopeInitialForm21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow21,mul_pow]

theorem slopeInitialForm22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow22 ((361/25)*v) := by
  simp only [slopeInitialForm22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow22,mul_pow]

theorem slopeInitialForm23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow23 ((361/25)*v) := by
  simp only [slopeInitialForm23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow23,mul_pow]

theorem slopeInitialForm24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow24 ((361/25)*v) := by
  simp only [slopeInitialForm24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow24,mul_pow]

theorem slopeInitialForm25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow25 ((361/25)*v) := by
  simp only [slopeInitialForm25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow25,mul_pow]

theorem slopeInitialForm26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow26 ((361/25)*v) := by
  simp only [slopeInitialForm26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow26,mul_pow]

theorem slopeInitialForm27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow27 ((361/25)*v) := by
  simp only [slopeInitialForm27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow27,mul_pow]

theorem slopeInitialForm28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow28 ((361/25)*v) := by
  simp only [slopeInitialForm28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow28,mul_pow]

theorem slopeInitialForm29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow29 ((361/25)*v) := by
  simp only [slopeInitialForm29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow29,mul_pow]

theorem slopeInitialForm30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow30 ((361/25)*v) := by
  simp only [slopeInitialForm30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow30,mul_pow]

theorem slopeInitialForm31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow31 ((361/25)*v) := by
  simp only [slopeInitialForm31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow31,mul_pow]

theorem slopeInitialForm32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow32 ((361/25)*v) := by
  simp only [slopeInitialForm32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow32,mul_pow]

theorem slopeInitialForm33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow33 ((361/25)*v) := by
  simp only [slopeInitialForm33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow33,mul_pow]

theorem slopeInitialForm34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow34 ((361/25)*v) := by
  simp only [slopeInitialForm34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow34,mul_pow]

theorem slopeInitialForm35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow35 ((361/25)*v) := by
  simp only [slopeInitialForm35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow35,mul_pow]

theorem slopeInitialForm36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow36 ((361/25)*v) := by
  simp only [slopeInitialForm36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow36,mul_pow]

theorem slopeInitialForm37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow37 ((361/25)*v) := by
  simp only [slopeInitialForm37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow37,mul_pow]

theorem slopeInitialForm38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInitialForm38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInitialRow38 ((361/25)*v) := by
  simp only [slopeInitialForm38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInitialRow38,mul_pow]

def slopeInitialTensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 33 (fun A => kineticBernstein 9 (slopeInitialTensorCoefficient A) v) t

theorem slopeInitialTensorValue_reconstruction (t v : ℝ) :
    slopeInitialTensorValue t v=slopeInitialQuotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInitialTensorValue slopeInitialTensorCoefficient slopeInitialClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInitialForm5_reconstruction,slopeInitialForm6_reconstruction,slopeInitialForm7_reconstruction,slopeInitialForm8_reconstruction,slopeInitialForm9_reconstruction,slopeInitialForm10_reconstruction,slopeInitialForm11_reconstruction,slopeInitialForm12_reconstruction,slopeInitialForm13_reconstruction,slopeInitialForm14_reconstruction,slopeInitialForm15_reconstruction,slopeInitialForm16_reconstruction,slopeInitialForm17_reconstruction,slopeInitialForm18_reconstruction,slopeInitialForm19_reconstruction,slopeInitialForm20_reconstruction,slopeInitialForm21_reconstruction,slopeInitialForm22_reconstruction,slopeInitialForm23_reconstruction,slopeInitialForm24_reconstruction,slopeInitialForm25_reconstruction,slopeInitialForm26_reconstruction,slopeInitialForm27_reconstruction,slopeInitialForm28_reconstruction,slopeInitialForm29_reconstruction,slopeInitialForm30_reconstruction,slopeInitialForm31_reconstruction,slopeInitialForm32_reconstruction,slopeInitialForm33_reconstruction,slopeInitialForm34_reconstruction,slopeInitialForm35_reconstruction,slopeInitialForm36_reconstruction,slopeInitialForm37_reconstruction,slopeInitialForm38_reconstruction]
  rw [kineticBernstein_degree 33 (5-5) (by omega),kineticBernstein_degree 33 (6-5) (by omega),kineticBernstein_degree 33 (7-5) (by omega),kineticBernstein_degree 33 (8-5) (by omega),kineticBernstein_degree 33 (9-5) (by omega),kineticBernstein_degree 33 (10-5) (by omega),kineticBernstein_degree 33 (11-5) (by omega),kineticBernstein_degree 33 (12-5) (by omega),kineticBernstein_degree 33 (13-5) (by omega),kineticBernstein_degree 33 (14-5) (by omega),kineticBernstein_degree 33 (15-5) (by omega),kineticBernstein_degree 33 (16-5) (by omega),kineticBernstein_degree 33 (17-5) (by omega),kineticBernstein_degree 33 (18-5) (by omega),kineticBernstein_degree 33 (19-5) (by omega),kineticBernstein_degree 33 (20-5) (by omega),kineticBernstein_degree 33 (21-5) (by omega),kineticBernstein_degree 33 (22-5) (by omega),kineticBernstein_degree 33 (23-5) (by omega),kineticBernstein_degree 33 (24-5) (by omega),kineticBernstein_degree 33 (25-5) (by omega),kineticBernstein_degree 33 (26-5) (by omega),kineticBernstein_degree 33 (27-5) (by omega),kineticBernstein_degree 33 (28-5) (by omega),kineticBernstein_degree 33 (29-5) (by omega),kineticBernstein_degree 33 (30-5) (by omega),kineticBernstein_degree 33 (31-5) (by omega),kineticBernstein_degree 33 (32-5) (by omega),kineticBernstein_degree 33 (33-5) (by omega),kineticBernstein_degree 33 (34-5) (by omega),kineticBernstein_degree 33 (35-5) (by omega),kineticBernstein_degree 33 (36-5) (by omega),kineticBernstein_degree 33 (37-5) (by omega),kineticBernstein_degree 33 (38-5) (by omega)]
  simp only [slopeInitialQuotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

