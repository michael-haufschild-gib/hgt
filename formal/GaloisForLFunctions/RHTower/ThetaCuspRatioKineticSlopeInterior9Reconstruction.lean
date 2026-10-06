import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior9TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior9Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row4 ((361/25)*v) := by
  simp only [slopeInterior9Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior9Row4,mul_pow]

theorem slopeInterior9Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row5 ((361/25)*v) := by
  simp only [slopeInterior9Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior9Row5,mul_pow]

theorem slopeInterior9Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row6 ((361/25)*v) := by
  simp only [slopeInterior9Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior9Row6,mul_pow]

theorem slopeInterior9Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row7 ((361/25)*v) := by
  simp only [slopeInterior9Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior9Row7,mul_pow]

theorem slopeInterior9Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row8 ((361/25)*v) := by
  simp only [slopeInterior9Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior9Row8,mul_pow]

theorem slopeInterior9Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row9 ((361/25)*v) := by
  simp only [slopeInterior9Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior9Row9,mul_pow]

theorem slopeInterior9Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row10 ((361/25)*v) := by
  simp only [slopeInterior9Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior9Row10,mul_pow]

theorem slopeInterior9Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row11 ((361/25)*v) := by
  simp only [slopeInterior9Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior9Row11,mul_pow]

theorem slopeInterior9Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row12 ((361/25)*v) := by
  simp only [slopeInterior9Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior9Row12,mul_pow]

theorem slopeInterior9Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row13 ((361/25)*v) := by
  simp only [slopeInterior9Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior9Row13,mul_pow]

theorem slopeInterior9Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row14 ((361/25)*v) := by
  simp only [slopeInterior9Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior9Row14,mul_pow]

theorem slopeInterior9Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row15 ((361/25)*v) := by
  simp only [slopeInterior9Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior9Row15,mul_pow]

theorem slopeInterior9Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row16 ((361/25)*v) := by
  simp only [slopeInterior9Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior9Row16,mul_pow]

theorem slopeInterior9Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row17 ((361/25)*v) := by
  simp only [slopeInterior9Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior9Row17,mul_pow]

theorem slopeInterior9Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row18 ((361/25)*v) := by
  simp only [slopeInterior9Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior9Row18,mul_pow]

theorem slopeInterior9Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row19 ((361/25)*v) := by
  simp only [slopeInterior9Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior9Row19,mul_pow]

theorem slopeInterior9Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row20 ((361/25)*v) := by
  simp only [slopeInterior9Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior9Row20,mul_pow]

theorem slopeInterior9Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row21 ((361/25)*v) := by
  simp only [slopeInterior9Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row21,mul_pow]

theorem slopeInterior9Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row22 ((361/25)*v) := by
  simp only [slopeInterior9Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row22,mul_pow]

theorem slopeInterior9Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row23 ((361/25)*v) := by
  simp only [slopeInterior9Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row23,mul_pow]

theorem slopeInterior9Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row24 ((361/25)*v) := by
  simp only [slopeInterior9Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row24,mul_pow]

theorem slopeInterior9Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row25 ((361/25)*v) := by
  simp only [slopeInterior9Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row25,mul_pow]

theorem slopeInterior9Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row26 ((361/25)*v) := by
  simp only [slopeInterior9Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row26,mul_pow]

theorem slopeInterior9Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row27 ((361/25)*v) := by
  simp only [slopeInterior9Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row27,mul_pow]

theorem slopeInterior9Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row28 ((361/25)*v) := by
  simp only [slopeInterior9Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row28,mul_pow]

theorem slopeInterior9Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row29 ((361/25)*v) := by
  simp only [slopeInterior9Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row29,mul_pow]

theorem slopeInterior9Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row30 ((361/25)*v) := by
  simp only [slopeInterior9Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row30,mul_pow]

theorem slopeInterior9Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row31 ((361/25)*v) := by
  simp only [slopeInterior9Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row31,mul_pow]

theorem slopeInterior9Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row32 ((361/25)*v) := by
  simp only [slopeInterior9Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row32,mul_pow]

theorem slopeInterior9Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row33 ((361/25)*v) := by
  simp only [slopeInterior9Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row33,mul_pow]

theorem slopeInterior9Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row34 ((361/25)*v) := by
  simp only [slopeInterior9Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row34,mul_pow]

theorem slopeInterior9Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row35 ((361/25)*v) := by
  simp only [slopeInterior9Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row35,mul_pow]

theorem slopeInterior9Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row36 ((361/25)*v) := by
  simp only [slopeInterior9Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row36,mul_pow]

theorem slopeInterior9Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row37 ((361/25)*v) := by
  simp only [slopeInterior9Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row37,mul_pow]

theorem slopeInterior9Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row38 ((361/25)*v) := by
  simp only [slopeInterior9Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row38,mul_pow]

theorem slopeInterior9Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row39 ((361/25)*v) := by
  simp only [slopeInterior9Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row39,mul_pow]

theorem slopeInterior9Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row40 ((361/25)*v) := by
  simp only [slopeInterior9Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row40,mul_pow]

theorem slopeInterior9Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row41 ((361/25)*v) := by
  simp only [slopeInterior9Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row41,mul_pow]

theorem slopeInterior9Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior9Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior9Row42 ((361/25)*v) := by
  simp only [slopeInterior9Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior9Row42,mul_pow]

def slopeInterior9TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior9TensorCoefficient A) v) t

theorem slopeInterior9TensorValue_reconstruction (t v : ℝ) :
    slopeInterior9TensorValue t v=slopeInterior9Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior9TensorValue slopeInterior9TensorCoefficient slopeInterior9ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior9Form4_reconstruction,slopeInterior9Form5_reconstruction,slopeInterior9Form6_reconstruction,slopeInterior9Form7_reconstruction,slopeInterior9Form8_reconstruction,slopeInterior9Form9_reconstruction,slopeInterior9Form10_reconstruction,slopeInterior9Form11_reconstruction,slopeInterior9Form12_reconstruction,slopeInterior9Form13_reconstruction,slopeInterior9Form14_reconstruction,slopeInterior9Form15_reconstruction,slopeInterior9Form16_reconstruction,slopeInterior9Form17_reconstruction,slopeInterior9Form18_reconstruction,slopeInterior9Form19_reconstruction,slopeInterior9Form20_reconstruction,slopeInterior9Form21_reconstruction,slopeInterior9Form22_reconstruction,slopeInterior9Form23_reconstruction,slopeInterior9Form24_reconstruction,slopeInterior9Form25_reconstruction,slopeInterior9Form26_reconstruction,slopeInterior9Form27_reconstruction,slopeInterior9Form28_reconstruction,slopeInterior9Form29_reconstruction,slopeInterior9Form30_reconstruction,slopeInterior9Form31_reconstruction,slopeInterior9Form32_reconstruction,slopeInterior9Form33_reconstruction,slopeInterior9Form34_reconstruction,slopeInterior9Form35_reconstruction,slopeInterior9Form36_reconstruction,slopeInterior9Form37_reconstruction,slopeInterior9Form38_reconstruction,slopeInterior9Form39_reconstruction,slopeInterior9Form40_reconstruction,slopeInterior9Form41_reconstruction,slopeInterior9Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior9Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

