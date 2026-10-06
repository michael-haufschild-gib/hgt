import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeTerminalTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeTerminalForm4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow4 ((361/25)*v) := by
  simp only [slopeTerminalForm4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeTerminalRow4,mul_pow]

theorem slopeTerminalForm5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow5 ((361/25)*v) := by
  simp only [slopeTerminalForm5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeTerminalRow5,mul_pow]

theorem slopeTerminalForm6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow6 ((361/25)*v) := by
  simp only [slopeTerminalForm6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeTerminalRow6,mul_pow]

theorem slopeTerminalForm7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow7 ((361/25)*v) := by
  simp only [slopeTerminalForm7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeTerminalRow7,mul_pow]

theorem slopeTerminalForm8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow8 ((361/25)*v) := by
  simp only [slopeTerminalForm8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeTerminalRow8,mul_pow]

theorem slopeTerminalForm9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow9 ((361/25)*v) := by
  simp only [slopeTerminalForm9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeTerminalRow9,mul_pow]

theorem slopeTerminalForm10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow10 ((361/25)*v) := by
  simp only [slopeTerminalForm10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeTerminalRow10,mul_pow]

theorem slopeTerminalForm11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow11 ((361/25)*v) := by
  simp only [slopeTerminalForm11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeTerminalRow11,mul_pow]

theorem slopeTerminalForm12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow12 ((361/25)*v) := by
  simp only [slopeTerminalForm12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeTerminalRow12,mul_pow]

theorem slopeTerminalForm13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow13 ((361/25)*v) := by
  simp only [slopeTerminalForm13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeTerminalRow13,mul_pow]

theorem slopeTerminalForm14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow14 ((361/25)*v) := by
  simp only [slopeTerminalForm14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeTerminalRow14,mul_pow]

theorem slopeTerminalForm15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow15 ((361/25)*v) := by
  simp only [slopeTerminalForm15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeTerminalRow15,mul_pow]

theorem slopeTerminalForm16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow16 ((361/25)*v) := by
  simp only [slopeTerminalForm16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeTerminalRow16,mul_pow]

theorem slopeTerminalForm17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow17 ((361/25)*v) := by
  simp only [slopeTerminalForm17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeTerminalRow17,mul_pow]

theorem slopeTerminalForm18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow18 ((361/25)*v) := by
  simp only [slopeTerminalForm18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeTerminalRow18,mul_pow]

theorem slopeTerminalForm19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow19 ((361/25)*v) := by
  simp only [slopeTerminalForm19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeTerminalRow19,mul_pow]

theorem slopeTerminalForm20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow20 ((361/25)*v) := by
  simp only [slopeTerminalForm20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeTerminalRow20,mul_pow]

theorem slopeTerminalForm21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow21 ((361/25)*v) := by
  simp only [slopeTerminalForm21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow21,mul_pow]

theorem slopeTerminalForm22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow22 ((361/25)*v) := by
  simp only [slopeTerminalForm22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow22,mul_pow]

theorem slopeTerminalForm23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow23 ((361/25)*v) := by
  simp only [slopeTerminalForm23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow23,mul_pow]

theorem slopeTerminalForm24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow24 ((361/25)*v) := by
  simp only [slopeTerminalForm24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow24,mul_pow]

theorem slopeTerminalForm25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow25 ((361/25)*v) := by
  simp only [slopeTerminalForm25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow25,mul_pow]

theorem slopeTerminalForm26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow26 ((361/25)*v) := by
  simp only [slopeTerminalForm26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow26,mul_pow]

theorem slopeTerminalForm27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow27 ((361/25)*v) := by
  simp only [slopeTerminalForm27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow27,mul_pow]

theorem slopeTerminalForm28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow28 ((361/25)*v) := by
  simp only [slopeTerminalForm28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow28,mul_pow]

theorem slopeTerminalForm29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow29 ((361/25)*v) := by
  simp only [slopeTerminalForm29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow29,mul_pow]

theorem slopeTerminalForm30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow30 ((361/25)*v) := by
  simp only [slopeTerminalForm30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow30,mul_pow]

theorem slopeTerminalForm31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow31 ((361/25)*v) := by
  simp only [slopeTerminalForm31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow31,mul_pow]

theorem slopeTerminalForm32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow32 ((361/25)*v) := by
  simp only [slopeTerminalForm32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow32,mul_pow]

theorem slopeTerminalForm33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow33 ((361/25)*v) := by
  simp only [slopeTerminalForm33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow33,mul_pow]

theorem slopeTerminalForm34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow34 ((361/25)*v) := by
  simp only [slopeTerminalForm34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow34,mul_pow]

theorem slopeTerminalForm35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow35 ((361/25)*v) := by
  simp only [slopeTerminalForm35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow35,mul_pow]

theorem slopeTerminalForm36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow36 ((361/25)*v) := by
  simp only [slopeTerminalForm36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow36,mul_pow]

theorem slopeTerminalForm37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow37 ((361/25)*v) := by
  simp only [slopeTerminalForm37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow37,mul_pow]

theorem slopeTerminalForm38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow38 ((361/25)*v) := by
  simp only [slopeTerminalForm38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow38,mul_pow]

theorem slopeTerminalForm39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow39 ((361/25)*v) := by
  simp only [slopeTerminalForm39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow39,mul_pow]

theorem slopeTerminalForm40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow40 ((361/25)*v) := by
  simp only [slopeTerminalForm40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow40,mul_pow]

theorem slopeTerminalForm41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow41 ((361/25)*v) := by
  simp only [slopeTerminalForm41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow41,mul_pow]

theorem slopeTerminalForm42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeTerminalForm42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeTerminalRow42 ((361/25)*v) := by
  simp only [slopeTerminalForm42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeTerminalRow42,mul_pow]

def slopeTerminalTensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeTerminalTensorCoefficient A) v) t

theorem slopeTerminalTensorValue_reconstruction (t v : ℝ) :
    slopeTerminalTensorValue t v=slopeTerminalQuotient ((4/5)*t) ((361/25)*v) := by
  delta slopeTerminalTensorValue slopeTerminalTensorCoefficient slopeTerminalClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeTerminalForm4_reconstruction,slopeTerminalForm5_reconstruction,slopeTerminalForm6_reconstruction,slopeTerminalForm7_reconstruction,slopeTerminalForm8_reconstruction,slopeTerminalForm9_reconstruction,slopeTerminalForm10_reconstruction,slopeTerminalForm11_reconstruction,slopeTerminalForm12_reconstruction,slopeTerminalForm13_reconstruction,slopeTerminalForm14_reconstruction,slopeTerminalForm15_reconstruction,slopeTerminalForm16_reconstruction,slopeTerminalForm17_reconstruction,slopeTerminalForm18_reconstruction,slopeTerminalForm19_reconstruction,slopeTerminalForm20_reconstruction,slopeTerminalForm21_reconstruction,slopeTerminalForm22_reconstruction,slopeTerminalForm23_reconstruction,slopeTerminalForm24_reconstruction,slopeTerminalForm25_reconstruction,slopeTerminalForm26_reconstruction,slopeTerminalForm27_reconstruction,slopeTerminalForm28_reconstruction,slopeTerminalForm29_reconstruction,slopeTerminalForm30_reconstruction,slopeTerminalForm31_reconstruction,slopeTerminalForm32_reconstruction,slopeTerminalForm33_reconstruction,slopeTerminalForm34_reconstruction,slopeTerminalForm35_reconstruction,slopeTerminalForm36_reconstruction,slopeTerminalForm37_reconstruction,slopeTerminalForm38_reconstruction,slopeTerminalForm39_reconstruction,slopeTerminalForm40_reconstruction,slopeTerminalForm41_reconstruction,slopeTerminalForm42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeTerminalQuotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction
