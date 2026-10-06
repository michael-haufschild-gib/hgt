import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior14TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior14Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row4 ((361/25)*v) := by
  simp only [slopeInterior14Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior14Row4,mul_pow]

theorem slopeInterior14Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row5 ((361/25)*v) := by
  simp only [slopeInterior14Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior14Row5,mul_pow]

theorem slopeInterior14Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row6 ((361/25)*v) := by
  simp only [slopeInterior14Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior14Row6,mul_pow]

theorem slopeInterior14Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row7 ((361/25)*v) := by
  simp only [slopeInterior14Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior14Row7,mul_pow]

theorem slopeInterior14Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row8 ((361/25)*v) := by
  simp only [slopeInterior14Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior14Row8,mul_pow]

theorem slopeInterior14Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row9 ((361/25)*v) := by
  simp only [slopeInterior14Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior14Row9,mul_pow]

theorem slopeInterior14Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row10 ((361/25)*v) := by
  simp only [slopeInterior14Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior14Row10,mul_pow]

theorem slopeInterior14Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row11 ((361/25)*v) := by
  simp only [slopeInterior14Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior14Row11,mul_pow]

theorem slopeInterior14Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row12 ((361/25)*v) := by
  simp only [slopeInterior14Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior14Row12,mul_pow]

theorem slopeInterior14Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row13 ((361/25)*v) := by
  simp only [slopeInterior14Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior14Row13,mul_pow]

theorem slopeInterior14Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row14 ((361/25)*v) := by
  simp only [slopeInterior14Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior14Row14,mul_pow]

theorem slopeInterior14Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row15 ((361/25)*v) := by
  simp only [slopeInterior14Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior14Row15,mul_pow]

theorem slopeInterior14Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row16 ((361/25)*v) := by
  simp only [slopeInterior14Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior14Row16,mul_pow]

theorem slopeInterior14Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row17 ((361/25)*v) := by
  simp only [slopeInterior14Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior14Row17,mul_pow]

theorem slopeInterior14Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row18 ((361/25)*v) := by
  simp only [slopeInterior14Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior14Row18,mul_pow]

theorem slopeInterior14Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row19 ((361/25)*v) := by
  simp only [slopeInterior14Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior14Row19,mul_pow]

theorem slopeInterior14Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row20 ((361/25)*v) := by
  simp only [slopeInterior14Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior14Row20,mul_pow]

theorem slopeInterior14Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row21 ((361/25)*v) := by
  simp only [slopeInterior14Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row21,mul_pow]

theorem slopeInterior14Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row22 ((361/25)*v) := by
  simp only [slopeInterior14Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row22,mul_pow]

theorem slopeInterior14Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row23 ((361/25)*v) := by
  simp only [slopeInterior14Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row23,mul_pow]

theorem slopeInterior14Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row24 ((361/25)*v) := by
  simp only [slopeInterior14Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row24,mul_pow]

theorem slopeInterior14Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row25 ((361/25)*v) := by
  simp only [slopeInterior14Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row25,mul_pow]

theorem slopeInterior14Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row26 ((361/25)*v) := by
  simp only [slopeInterior14Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row26,mul_pow]

theorem slopeInterior14Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row27 ((361/25)*v) := by
  simp only [slopeInterior14Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row27,mul_pow]

theorem slopeInterior14Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row28 ((361/25)*v) := by
  simp only [slopeInterior14Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row28,mul_pow]

theorem slopeInterior14Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row29 ((361/25)*v) := by
  simp only [slopeInterior14Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row29,mul_pow]

theorem slopeInterior14Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row30 ((361/25)*v) := by
  simp only [slopeInterior14Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row30,mul_pow]

theorem slopeInterior14Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row31 ((361/25)*v) := by
  simp only [slopeInterior14Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row31,mul_pow]

theorem slopeInterior14Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row32 ((361/25)*v) := by
  simp only [slopeInterior14Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row32,mul_pow]

theorem slopeInterior14Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row33 ((361/25)*v) := by
  simp only [slopeInterior14Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row33,mul_pow]

theorem slopeInterior14Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row34 ((361/25)*v) := by
  simp only [slopeInterior14Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row34,mul_pow]

theorem slopeInterior14Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row35 ((361/25)*v) := by
  simp only [slopeInterior14Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row35,mul_pow]

theorem slopeInterior14Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row36 ((361/25)*v) := by
  simp only [slopeInterior14Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row36,mul_pow]

theorem slopeInterior14Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row37 ((361/25)*v) := by
  simp only [slopeInterior14Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row37,mul_pow]

theorem slopeInterior14Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row38 ((361/25)*v) := by
  simp only [slopeInterior14Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row38,mul_pow]

theorem slopeInterior14Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row39 ((361/25)*v) := by
  simp only [slopeInterior14Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row39,mul_pow]

theorem slopeInterior14Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row40 ((361/25)*v) := by
  simp only [slopeInterior14Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row40,mul_pow]

theorem slopeInterior14Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row41 ((361/25)*v) := by
  simp only [slopeInterior14Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row41,mul_pow]

theorem slopeInterior14Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior14Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior14Row42 ((361/25)*v) := by
  simp only [slopeInterior14Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior14Row42,mul_pow]

def slopeInterior14TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior14TensorCoefficient A) v) t

theorem slopeInterior14TensorValue_reconstruction (t v : ℝ) :
    slopeInterior14TensorValue t v=slopeInterior14Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior14TensorValue slopeInterior14TensorCoefficient slopeInterior14ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior14Form4_reconstruction,slopeInterior14Form5_reconstruction,slopeInterior14Form6_reconstruction,slopeInterior14Form7_reconstruction,slopeInterior14Form8_reconstruction,slopeInterior14Form9_reconstruction,slopeInterior14Form10_reconstruction,slopeInterior14Form11_reconstruction,slopeInterior14Form12_reconstruction,slopeInterior14Form13_reconstruction,slopeInterior14Form14_reconstruction,slopeInterior14Form15_reconstruction,slopeInterior14Form16_reconstruction,slopeInterior14Form17_reconstruction,slopeInterior14Form18_reconstruction,slopeInterior14Form19_reconstruction,slopeInterior14Form20_reconstruction,slopeInterior14Form21_reconstruction,slopeInterior14Form22_reconstruction,slopeInterior14Form23_reconstruction,slopeInterior14Form24_reconstruction,slopeInterior14Form25_reconstruction,slopeInterior14Form26_reconstruction,slopeInterior14Form27_reconstruction,slopeInterior14Form28_reconstruction,slopeInterior14Form29_reconstruction,slopeInterior14Form30_reconstruction,slopeInterior14Form31_reconstruction,slopeInterior14Form32_reconstruction,slopeInterior14Form33_reconstruction,slopeInterior14Form34_reconstruction,slopeInterior14Form35_reconstruction,slopeInterior14Form36_reconstruction,slopeInterior14Form37_reconstruction,slopeInterior14Form38_reconstruction,slopeInterior14Form39_reconstruction,slopeInterior14Form40_reconstruction,slopeInterior14Form41_reconstruction,slopeInterior14Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior14Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

