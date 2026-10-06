import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior16TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior16Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row4 ((361/25)*v) := by
  simp only [slopeInterior16Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior16Row4,mul_pow]

theorem slopeInterior16Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row5 ((361/25)*v) := by
  simp only [slopeInterior16Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior16Row5,mul_pow]

theorem slopeInterior16Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row6 ((361/25)*v) := by
  simp only [slopeInterior16Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior16Row6,mul_pow]

theorem slopeInterior16Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row7 ((361/25)*v) := by
  simp only [slopeInterior16Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior16Row7,mul_pow]

theorem slopeInterior16Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row8 ((361/25)*v) := by
  simp only [slopeInterior16Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior16Row8,mul_pow]

theorem slopeInterior16Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row9 ((361/25)*v) := by
  simp only [slopeInterior16Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior16Row9,mul_pow]

theorem slopeInterior16Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row10 ((361/25)*v) := by
  simp only [slopeInterior16Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior16Row10,mul_pow]

theorem slopeInterior16Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row11 ((361/25)*v) := by
  simp only [slopeInterior16Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior16Row11,mul_pow]

theorem slopeInterior16Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row12 ((361/25)*v) := by
  simp only [slopeInterior16Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior16Row12,mul_pow]

theorem slopeInterior16Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row13 ((361/25)*v) := by
  simp only [slopeInterior16Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior16Row13,mul_pow]

theorem slopeInterior16Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row14 ((361/25)*v) := by
  simp only [slopeInterior16Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior16Row14,mul_pow]

theorem slopeInterior16Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row15 ((361/25)*v) := by
  simp only [slopeInterior16Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior16Row15,mul_pow]

theorem slopeInterior16Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row16 ((361/25)*v) := by
  simp only [slopeInterior16Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior16Row16,mul_pow]

theorem slopeInterior16Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row17 ((361/25)*v) := by
  simp only [slopeInterior16Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior16Row17,mul_pow]

theorem slopeInterior16Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row18 ((361/25)*v) := by
  simp only [slopeInterior16Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior16Row18,mul_pow]

theorem slopeInterior16Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row19 ((361/25)*v) := by
  simp only [slopeInterior16Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior16Row19,mul_pow]

theorem slopeInterior16Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row20 ((361/25)*v) := by
  simp only [slopeInterior16Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior16Row20,mul_pow]

theorem slopeInterior16Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row21 ((361/25)*v) := by
  simp only [slopeInterior16Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row21,mul_pow]

theorem slopeInterior16Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row22 ((361/25)*v) := by
  simp only [slopeInterior16Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row22,mul_pow]

theorem slopeInterior16Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row23 ((361/25)*v) := by
  simp only [slopeInterior16Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row23,mul_pow]

theorem slopeInterior16Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row24 ((361/25)*v) := by
  simp only [slopeInterior16Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row24,mul_pow]

theorem slopeInterior16Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row25 ((361/25)*v) := by
  simp only [slopeInterior16Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row25,mul_pow]

theorem slopeInterior16Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row26 ((361/25)*v) := by
  simp only [slopeInterior16Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row26,mul_pow]

theorem slopeInterior16Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row27 ((361/25)*v) := by
  simp only [slopeInterior16Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row27,mul_pow]

theorem slopeInterior16Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row28 ((361/25)*v) := by
  simp only [slopeInterior16Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row28,mul_pow]

theorem slopeInterior16Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row29 ((361/25)*v) := by
  simp only [slopeInterior16Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row29,mul_pow]

theorem slopeInterior16Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row30 ((361/25)*v) := by
  simp only [slopeInterior16Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row30,mul_pow]

theorem slopeInterior16Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row31 ((361/25)*v) := by
  simp only [slopeInterior16Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row31,mul_pow]

theorem slopeInterior16Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row32 ((361/25)*v) := by
  simp only [slopeInterior16Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row32,mul_pow]

theorem slopeInterior16Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row33 ((361/25)*v) := by
  simp only [slopeInterior16Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row33,mul_pow]

theorem slopeInterior16Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row34 ((361/25)*v) := by
  simp only [slopeInterior16Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row34,mul_pow]

theorem slopeInterior16Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row35 ((361/25)*v) := by
  simp only [slopeInterior16Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row35,mul_pow]

theorem slopeInterior16Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row36 ((361/25)*v) := by
  simp only [slopeInterior16Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row36,mul_pow]

theorem slopeInterior16Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row37 ((361/25)*v) := by
  simp only [slopeInterior16Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row37,mul_pow]

theorem slopeInterior16Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row38 ((361/25)*v) := by
  simp only [slopeInterior16Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row38,mul_pow]

theorem slopeInterior16Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row39 ((361/25)*v) := by
  simp only [slopeInterior16Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row39,mul_pow]

theorem slopeInterior16Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row40 ((361/25)*v) := by
  simp only [slopeInterior16Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row40,mul_pow]

theorem slopeInterior16Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row41 ((361/25)*v) := by
  simp only [slopeInterior16Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row41,mul_pow]

theorem slopeInterior16Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior16Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior16Row42 ((361/25)*v) := by
  simp only [slopeInterior16Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior16Row42,mul_pow]

def slopeInterior16TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior16TensorCoefficient A) v) t

theorem slopeInterior16TensorValue_reconstruction (t v : ℝ) :
    slopeInterior16TensorValue t v=slopeInterior16Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior16TensorValue slopeInterior16TensorCoefficient slopeInterior16ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior16Form4_reconstruction,slopeInterior16Form5_reconstruction,slopeInterior16Form6_reconstruction,slopeInterior16Form7_reconstruction,slopeInterior16Form8_reconstruction,slopeInterior16Form9_reconstruction,slopeInterior16Form10_reconstruction,slopeInterior16Form11_reconstruction,slopeInterior16Form12_reconstruction,slopeInterior16Form13_reconstruction,slopeInterior16Form14_reconstruction,slopeInterior16Form15_reconstruction,slopeInterior16Form16_reconstruction,slopeInterior16Form17_reconstruction,slopeInterior16Form18_reconstruction,slopeInterior16Form19_reconstruction,slopeInterior16Form20_reconstruction,slopeInterior16Form21_reconstruction,slopeInterior16Form22_reconstruction,slopeInterior16Form23_reconstruction,slopeInterior16Form24_reconstruction,slopeInterior16Form25_reconstruction,slopeInterior16Form26_reconstruction,slopeInterior16Form27_reconstruction,slopeInterior16Form28_reconstruction,slopeInterior16Form29_reconstruction,slopeInterior16Form30_reconstruction,slopeInterior16Form31_reconstruction,slopeInterior16Form32_reconstruction,slopeInterior16Form33_reconstruction,slopeInterior16Form34_reconstruction,slopeInterior16Form35_reconstruction,slopeInterior16Form36_reconstruction,slopeInterior16Form37_reconstruction,slopeInterior16Form38_reconstruction,slopeInterior16Form39_reconstruction,slopeInterior16Form40_reconstruction,slopeInterior16Form41_reconstruction,slopeInterior16Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior16Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

