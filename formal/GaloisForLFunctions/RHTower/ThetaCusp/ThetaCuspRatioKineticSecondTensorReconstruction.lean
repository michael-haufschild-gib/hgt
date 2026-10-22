import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

theorem secondControlDefectForm4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm4
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow4 ((361/25)*v) := by
  simp only [secondControlDefectForm4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  norm_num [secondControlDefectRow4,Nat.rawCast,Int.rawCast]

theorem secondControlDefectForm5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm5
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow5 ((361/25)*v) := by
  simp only [secondControlDefectForm5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  norm_num [secondControlDefectRow5,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm6
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow6 ((361/25)*v) := by
  simp only [secondControlDefectForm6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  norm_num [secondControlDefectRow6,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm7
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow7 ((361/25)*v) := by
  simp only [secondControlDefectForm7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  norm_num [secondControlDefectRow7,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm8
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow8 ((361/25)*v) := by
  simp only [secondControlDefectForm8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  norm_num [secondControlDefectRow8,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm9
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow9 ((361/25)*v) := by
  simp only [secondControlDefectForm9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  norm_num [secondControlDefectRow9,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm10
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow10 ((361/25)*v) := by
  simp only [secondControlDefectForm10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  norm_num [secondControlDefectRow10,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm11
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow11 ((361/25)*v) := by
  simp only [secondControlDefectForm11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  norm_num [secondControlDefectRow11,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm12
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow12 ((361/25)*v) := by
  simp only [secondControlDefectForm12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  norm_num [secondControlDefectRow12,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm13
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow13 ((361/25)*v) := by
  simp only [secondControlDefectForm13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  norm_num [secondControlDefectRow13,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm14
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow14 ((361/25)*v) := by
  simp only [secondControlDefectForm14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  norm_num [secondControlDefectRow14,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm15
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow15 ((361/25)*v) := by
  simp only [secondControlDefectForm15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  norm_num [secondControlDefectRow15,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm16
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow16 ((361/25)*v) := by
  simp only [secondControlDefectForm16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  norm_num [secondControlDefectRow16,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm17
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow17 ((361/25)*v) := by
  simp only [secondControlDefectForm17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  norm_num [secondControlDefectRow17,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm18
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow18 ((361/25)*v) := by
  simp only [secondControlDefectForm18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  norm_num [secondControlDefectRow18,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm19
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow19 ((361/25)*v) := by
  simp only [secondControlDefectForm19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  norm_num [secondControlDefectRow19,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm20
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow20 ((361/25)*v) := by
  simp only [secondControlDefectForm20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow20,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm21
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow21 ((361/25)*v) := by
  simp only [secondControlDefectForm21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow21,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm22
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow22 ((361/25)*v) := by
  simp only [secondControlDefectForm22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow22,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm23
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow23 ((361/25)*v) := by
  simp only [secondControlDefectForm23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow23,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm24
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow24 ((361/25)*v) := by
  simp only [secondControlDefectForm24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow24,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm25
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow25 ((361/25)*v) := by
  simp only [secondControlDefectForm25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow25,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm26
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow26 ((361/25)*v) := by
  simp only [secondControlDefectForm26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow26,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm27
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow27 ((361/25)*v) := by
  simp only [secondControlDefectForm27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow27,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm28
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow28 ((361/25)*v) := by
  simp only [secondControlDefectForm28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow28,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm29
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow29 ((361/25)*v) := by
  simp only [secondControlDefectForm29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow29,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm30
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow30 ((361/25)*v) := by
  simp only [secondControlDefectForm30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow30,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm31
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow31 ((361/25)*v) := by
  simp only [secondControlDefectForm31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow31,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm32
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow32 ((361/25)*v) := by
  simp only [secondControlDefectForm32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow32,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm33
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow33 ((361/25)*v) := by
  simp only [secondControlDefectForm33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow33,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm34
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow34 ((361/25)*v) := by
  simp only [secondControlDefectForm34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow34,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm35
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow35 ((361/25)*v) := by
  simp only [secondControlDefectForm35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow35,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm36
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow36 ((361/25)*v) := by
  simp only [secondControlDefectForm36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow36,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm37
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow37 ((361/25)*v) := by
  simp only [secondControlDefectForm37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow37,Nat.rawCast,Int.rawCast]
  ring

theorem secondControlDefectForm38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => secondControlDefectForm38
      (fun k => (361/25)^k*degreeElevationCoefficient 9 k B)) v=
        secondControlDefectRow38 ((361/25)*v) := by
  simp only [secondControlDefectForm38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  norm_num [secondControlDefectRow38,Nat.rawCast,Int.rawCast]
  ring

def secondControlDefectTensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 34 (fun A => kineticBernstein 9 (secondControlDefectTensorCoefficient A) v) t

theorem secondControlDefectTensorValue_reconstruction (t v : ℝ) :
    secondControlDefectTensorValue t v=secondControlDefectQuotient ((4/5)*t) ((361/25)*v) := by
  delta secondControlDefectTensorValue secondControlDefectTensorCoefficient secondControlDefectClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    secondControlDefectForm4_reconstruction,secondControlDefectForm5_reconstruction,secondControlDefectForm6_reconstruction,secondControlDefectForm7_reconstruction,secondControlDefectForm8_reconstruction,secondControlDefectForm9_reconstruction,secondControlDefectForm10_reconstruction,secondControlDefectForm11_reconstruction,secondControlDefectForm12_reconstruction,secondControlDefectForm13_reconstruction,secondControlDefectForm14_reconstruction,secondControlDefectForm15_reconstruction,secondControlDefectForm16_reconstruction,secondControlDefectForm17_reconstruction,secondControlDefectForm18_reconstruction,secondControlDefectForm19_reconstruction,secondControlDefectForm20_reconstruction,secondControlDefectForm21_reconstruction,secondControlDefectForm22_reconstruction,secondControlDefectForm23_reconstruction,secondControlDefectForm24_reconstruction,secondControlDefectForm25_reconstruction,secondControlDefectForm26_reconstruction,secondControlDefectForm27_reconstruction,secondControlDefectForm28_reconstruction,secondControlDefectForm29_reconstruction,secondControlDefectForm30_reconstruction,secondControlDefectForm31_reconstruction,secondControlDefectForm32_reconstruction,secondControlDefectForm33_reconstruction,secondControlDefectForm34_reconstruction,secondControlDefectForm35_reconstruction,secondControlDefectForm36_reconstruction,secondControlDefectForm37_reconstruction,secondControlDefectForm38_reconstruction]
  rw [kineticBernstein_degree 34 (4-4) (by omega),kineticBernstein_degree 34 (5-4) (by omega),kineticBernstein_degree 34 (6-4) (by omega),kineticBernstein_degree 34 (7-4) (by omega),kineticBernstein_degree 34 (8-4) (by omega),kineticBernstein_degree 34 (9-4) (by omega),kineticBernstein_degree 34 (10-4) (by omega),kineticBernstein_degree 34 (11-4) (by omega),kineticBernstein_degree 34 (12-4) (by omega),kineticBernstein_degree 34 (13-4) (by omega),kineticBernstein_degree 34 (14-4) (by omega),kineticBernstein_degree 34 (15-4) (by omega),kineticBernstein_degree 34 (16-4) (by omega),kineticBernstein_degree 34 (17-4) (by omega),kineticBernstein_degree 34 (18-4) (by omega),kineticBernstein_degree 34 (19-4) (by omega),kineticBernstein_degree 34 (20-4) (by omega),kineticBernstein_degree 34 (21-4) (by omega),kineticBernstein_degree 34 (22-4) (by omega),kineticBernstein_degree 34 (23-4) (by omega),kineticBernstein_degree 34 (24-4) (by omega),kineticBernstein_degree 34 (25-4) (by omega),kineticBernstein_degree 34 (26-4) (by omega),kineticBernstein_degree 34 (27-4) (by omega),kineticBernstein_degree 34 (28-4) (by omega),kineticBernstein_degree 34 (29-4) (by omega),kineticBernstein_degree 34 (30-4) (by omega),kineticBernstein_degree 34 (31-4) (by omega),kineticBernstein_degree 34 (32-4) (by omega),kineticBernstein_degree 34 (33-4) (by omega),kineticBernstein_degree 34 (34-4) (by omega),kineticBernstein_degree 34 (35-4) (by omega),kineticBernstein_degree 34 (36-4) (by omega),kineticBernstein_degree 34 (37-4) (by omega),kineticBernstein_degree 34 (38-4) (by omega)]
  simp only [secondControlDefectQuotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction
