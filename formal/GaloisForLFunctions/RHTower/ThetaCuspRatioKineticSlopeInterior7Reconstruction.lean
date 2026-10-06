import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior7TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior7Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row4 ((361/25)*v) := by
  simp only [slopeInterior7Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior7Row4,mul_pow]

theorem slopeInterior7Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row5 ((361/25)*v) := by
  simp only [slopeInterior7Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior7Row5,mul_pow]

theorem slopeInterior7Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row6 ((361/25)*v) := by
  simp only [slopeInterior7Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior7Row6,mul_pow]

theorem slopeInterior7Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row7 ((361/25)*v) := by
  simp only [slopeInterior7Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior7Row7,mul_pow]

theorem slopeInterior7Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row8 ((361/25)*v) := by
  simp only [slopeInterior7Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior7Row8,mul_pow]

theorem slopeInterior7Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row9 ((361/25)*v) := by
  simp only [slopeInterior7Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior7Row9,mul_pow]

theorem slopeInterior7Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row10 ((361/25)*v) := by
  simp only [slopeInterior7Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior7Row10,mul_pow]

theorem slopeInterior7Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row11 ((361/25)*v) := by
  simp only [slopeInterior7Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior7Row11,mul_pow]

theorem slopeInterior7Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row12 ((361/25)*v) := by
  simp only [slopeInterior7Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior7Row12,mul_pow]

theorem slopeInterior7Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row13 ((361/25)*v) := by
  simp only [slopeInterior7Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior7Row13,mul_pow]

theorem slopeInterior7Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row14 ((361/25)*v) := by
  simp only [slopeInterior7Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior7Row14,mul_pow]

theorem slopeInterior7Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row15 ((361/25)*v) := by
  simp only [slopeInterior7Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior7Row15,mul_pow]

theorem slopeInterior7Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row16 ((361/25)*v) := by
  simp only [slopeInterior7Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior7Row16,mul_pow]

theorem slopeInterior7Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row17 ((361/25)*v) := by
  simp only [slopeInterior7Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior7Row17,mul_pow]

theorem slopeInterior7Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row18 ((361/25)*v) := by
  simp only [slopeInterior7Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior7Row18,mul_pow]

theorem slopeInterior7Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row19 ((361/25)*v) := by
  simp only [slopeInterior7Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior7Row19,mul_pow]

theorem slopeInterior7Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row20 ((361/25)*v) := by
  simp only [slopeInterior7Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior7Row20,mul_pow]

theorem slopeInterior7Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row21 ((361/25)*v) := by
  simp only [slopeInterior7Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row21,mul_pow]

theorem slopeInterior7Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row22 ((361/25)*v) := by
  simp only [slopeInterior7Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row22,mul_pow]

theorem slopeInterior7Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row23 ((361/25)*v) := by
  simp only [slopeInterior7Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row23,mul_pow]

theorem slopeInterior7Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row24 ((361/25)*v) := by
  simp only [slopeInterior7Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row24,mul_pow]

theorem slopeInterior7Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row25 ((361/25)*v) := by
  simp only [slopeInterior7Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row25,mul_pow]

theorem slopeInterior7Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row26 ((361/25)*v) := by
  simp only [slopeInterior7Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row26,mul_pow]

theorem slopeInterior7Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row27 ((361/25)*v) := by
  simp only [slopeInterior7Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row27,mul_pow]

theorem slopeInterior7Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row28 ((361/25)*v) := by
  simp only [slopeInterior7Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row28,mul_pow]

theorem slopeInterior7Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row29 ((361/25)*v) := by
  simp only [slopeInterior7Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row29,mul_pow]

theorem slopeInterior7Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row30 ((361/25)*v) := by
  simp only [slopeInterior7Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row30,mul_pow]

theorem slopeInterior7Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row31 ((361/25)*v) := by
  simp only [slopeInterior7Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row31,mul_pow]

theorem slopeInterior7Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row32 ((361/25)*v) := by
  simp only [slopeInterior7Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row32,mul_pow]

theorem slopeInterior7Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row33 ((361/25)*v) := by
  simp only [slopeInterior7Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row33,mul_pow]

theorem slopeInterior7Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row34 ((361/25)*v) := by
  simp only [slopeInterior7Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row34,mul_pow]

theorem slopeInterior7Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row35 ((361/25)*v) := by
  simp only [slopeInterior7Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row35,mul_pow]

theorem slopeInterior7Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row36 ((361/25)*v) := by
  simp only [slopeInterior7Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row36,mul_pow]

theorem slopeInterior7Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row37 ((361/25)*v) := by
  simp only [slopeInterior7Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row37,mul_pow]

theorem slopeInterior7Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row38 ((361/25)*v) := by
  simp only [slopeInterior7Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row38,mul_pow]

theorem slopeInterior7Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row39 ((361/25)*v) := by
  simp only [slopeInterior7Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row39,mul_pow]

theorem slopeInterior7Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row40 ((361/25)*v) := by
  simp only [slopeInterior7Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row40,mul_pow]

theorem slopeInterior7Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row41 ((361/25)*v) := by
  simp only [slopeInterior7Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row41,mul_pow]

theorem slopeInterior7Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior7Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior7Row42 ((361/25)*v) := by
  simp only [slopeInterior7Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior7Row42,mul_pow]

def slopeInterior7TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior7TensorCoefficient A) v) t

theorem slopeInterior7TensorValue_reconstruction (t v : ℝ) :
    slopeInterior7TensorValue t v=slopeInterior7Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior7TensorValue slopeInterior7TensorCoefficient slopeInterior7ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior7Form4_reconstruction,slopeInterior7Form5_reconstruction,slopeInterior7Form6_reconstruction,slopeInterior7Form7_reconstruction,slopeInterior7Form8_reconstruction,slopeInterior7Form9_reconstruction,slopeInterior7Form10_reconstruction,slopeInterior7Form11_reconstruction,slopeInterior7Form12_reconstruction,slopeInterior7Form13_reconstruction,slopeInterior7Form14_reconstruction,slopeInterior7Form15_reconstruction,slopeInterior7Form16_reconstruction,slopeInterior7Form17_reconstruction,slopeInterior7Form18_reconstruction,slopeInterior7Form19_reconstruction,slopeInterior7Form20_reconstruction,slopeInterior7Form21_reconstruction,slopeInterior7Form22_reconstruction,slopeInterior7Form23_reconstruction,slopeInterior7Form24_reconstruction,slopeInterior7Form25_reconstruction,slopeInterior7Form26_reconstruction,slopeInterior7Form27_reconstruction,slopeInterior7Form28_reconstruction,slopeInterior7Form29_reconstruction,slopeInterior7Form30_reconstruction,slopeInterior7Form31_reconstruction,slopeInterior7Form32_reconstruction,slopeInterior7Form33_reconstruction,slopeInterior7Form34_reconstruction,slopeInterior7Form35_reconstruction,slopeInterior7Form36_reconstruction,slopeInterior7Form37_reconstruction,slopeInterior7Form38_reconstruction,slopeInterior7Form39_reconstruction,slopeInterior7Form40_reconstruction,slopeInterior7Form41_reconstruction,slopeInterior7Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior7Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

