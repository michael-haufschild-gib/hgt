import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior15TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior15Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row4 ((361/25)*v) := by
  simp only [slopeInterior15Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior15Row4,mul_pow]

theorem slopeInterior15Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row5 ((361/25)*v) := by
  simp only [slopeInterior15Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior15Row5,mul_pow]

theorem slopeInterior15Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row6 ((361/25)*v) := by
  simp only [slopeInterior15Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior15Row6,mul_pow]

theorem slopeInterior15Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row7 ((361/25)*v) := by
  simp only [slopeInterior15Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior15Row7,mul_pow]

theorem slopeInterior15Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row8 ((361/25)*v) := by
  simp only [slopeInterior15Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior15Row8,mul_pow]

theorem slopeInterior15Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row9 ((361/25)*v) := by
  simp only [slopeInterior15Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior15Row9,mul_pow]

theorem slopeInterior15Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row10 ((361/25)*v) := by
  simp only [slopeInterior15Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior15Row10,mul_pow]

theorem slopeInterior15Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row11 ((361/25)*v) := by
  simp only [slopeInterior15Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior15Row11,mul_pow]

theorem slopeInterior15Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row12 ((361/25)*v) := by
  simp only [slopeInterior15Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior15Row12,mul_pow]

theorem slopeInterior15Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row13 ((361/25)*v) := by
  simp only [slopeInterior15Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior15Row13,mul_pow]

theorem slopeInterior15Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row14 ((361/25)*v) := by
  simp only [slopeInterior15Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior15Row14,mul_pow]

theorem slopeInterior15Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row15 ((361/25)*v) := by
  simp only [slopeInterior15Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior15Row15,mul_pow]

theorem slopeInterior15Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row16 ((361/25)*v) := by
  simp only [slopeInterior15Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior15Row16,mul_pow]

theorem slopeInterior15Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row17 ((361/25)*v) := by
  simp only [slopeInterior15Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior15Row17,mul_pow]

theorem slopeInterior15Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row18 ((361/25)*v) := by
  simp only [slopeInterior15Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior15Row18,mul_pow]

theorem slopeInterior15Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row19 ((361/25)*v) := by
  simp only [slopeInterior15Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior15Row19,mul_pow]

theorem slopeInterior15Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row20 ((361/25)*v) := by
  simp only [slopeInterior15Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior15Row20,mul_pow]

theorem slopeInterior15Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row21 ((361/25)*v) := by
  simp only [slopeInterior15Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row21,mul_pow]

theorem slopeInterior15Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row22 ((361/25)*v) := by
  simp only [slopeInterior15Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row22,mul_pow]

theorem slopeInterior15Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row23 ((361/25)*v) := by
  simp only [slopeInterior15Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row23,mul_pow]

theorem slopeInterior15Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row24 ((361/25)*v) := by
  simp only [slopeInterior15Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row24,mul_pow]

theorem slopeInterior15Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row25 ((361/25)*v) := by
  simp only [slopeInterior15Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row25,mul_pow]

theorem slopeInterior15Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row26 ((361/25)*v) := by
  simp only [slopeInterior15Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row26,mul_pow]

theorem slopeInterior15Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row27 ((361/25)*v) := by
  simp only [slopeInterior15Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row27,mul_pow]

theorem slopeInterior15Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row28 ((361/25)*v) := by
  simp only [slopeInterior15Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row28,mul_pow]

theorem slopeInterior15Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row29 ((361/25)*v) := by
  simp only [slopeInterior15Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row29,mul_pow]

theorem slopeInterior15Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row30 ((361/25)*v) := by
  simp only [slopeInterior15Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row30,mul_pow]

theorem slopeInterior15Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row31 ((361/25)*v) := by
  simp only [slopeInterior15Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row31,mul_pow]

theorem slopeInterior15Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row32 ((361/25)*v) := by
  simp only [slopeInterior15Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row32,mul_pow]

theorem slopeInterior15Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row33 ((361/25)*v) := by
  simp only [slopeInterior15Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row33,mul_pow]

theorem slopeInterior15Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row34 ((361/25)*v) := by
  simp only [slopeInterior15Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row34,mul_pow]

theorem slopeInterior15Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row35 ((361/25)*v) := by
  simp only [slopeInterior15Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row35,mul_pow]

theorem slopeInterior15Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row36 ((361/25)*v) := by
  simp only [slopeInterior15Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row36,mul_pow]

theorem slopeInterior15Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row37 ((361/25)*v) := by
  simp only [slopeInterior15Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row37,mul_pow]

theorem slopeInterior15Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row38 ((361/25)*v) := by
  simp only [slopeInterior15Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row38,mul_pow]

theorem slopeInterior15Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row39 ((361/25)*v) := by
  simp only [slopeInterior15Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row39,mul_pow]

theorem slopeInterior15Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row40 ((361/25)*v) := by
  simp only [slopeInterior15Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row40,mul_pow]

theorem slopeInterior15Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row41 ((361/25)*v) := by
  simp only [slopeInterior15Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row41,mul_pow]

theorem slopeInterior15Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior15Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior15Row42 ((361/25)*v) := by
  simp only [slopeInterior15Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior15Row42,mul_pow]

def slopeInterior15TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior15TensorCoefficient A) v) t

theorem slopeInterior15TensorValue_reconstruction (t v : ℝ) :
    slopeInterior15TensorValue t v=slopeInterior15Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior15TensorValue slopeInterior15TensorCoefficient slopeInterior15ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior15Form4_reconstruction,slopeInterior15Form5_reconstruction,slopeInterior15Form6_reconstruction,slopeInterior15Form7_reconstruction,slopeInterior15Form8_reconstruction,slopeInterior15Form9_reconstruction,slopeInterior15Form10_reconstruction,slopeInterior15Form11_reconstruction,slopeInterior15Form12_reconstruction,slopeInterior15Form13_reconstruction,slopeInterior15Form14_reconstruction,slopeInterior15Form15_reconstruction,slopeInterior15Form16_reconstruction,slopeInterior15Form17_reconstruction,slopeInterior15Form18_reconstruction,slopeInterior15Form19_reconstruction,slopeInterior15Form20_reconstruction,slopeInterior15Form21_reconstruction,slopeInterior15Form22_reconstruction,slopeInterior15Form23_reconstruction,slopeInterior15Form24_reconstruction,slopeInterior15Form25_reconstruction,slopeInterior15Form26_reconstruction,slopeInterior15Form27_reconstruction,slopeInterior15Form28_reconstruction,slopeInterior15Form29_reconstruction,slopeInterior15Form30_reconstruction,slopeInterior15Form31_reconstruction,slopeInterior15Form32_reconstruction,slopeInterior15Form33_reconstruction,slopeInterior15Form34_reconstruction,slopeInterior15Form35_reconstruction,slopeInterior15Form36_reconstruction,slopeInterior15Form37_reconstruction,slopeInterior15Form38_reconstruction,slopeInterior15Form39_reconstruction,slopeInterior15Form40_reconstruction,slopeInterior15Form41_reconstruction,slopeInterior15Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior15Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

