import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior12TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior12Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row4 ((361/25)*v) := by
  simp only [slopeInterior12Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior12Row4,mul_pow]

theorem slopeInterior12Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row5 ((361/25)*v) := by
  simp only [slopeInterior12Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior12Row5,mul_pow]

theorem slopeInterior12Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row6 ((361/25)*v) := by
  simp only [slopeInterior12Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior12Row6,mul_pow]

theorem slopeInterior12Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row7 ((361/25)*v) := by
  simp only [slopeInterior12Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior12Row7,mul_pow]

theorem slopeInterior12Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row8 ((361/25)*v) := by
  simp only [slopeInterior12Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior12Row8,mul_pow]

theorem slopeInterior12Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row9 ((361/25)*v) := by
  simp only [slopeInterior12Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior12Row9,mul_pow]

theorem slopeInterior12Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row10 ((361/25)*v) := by
  simp only [slopeInterior12Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior12Row10,mul_pow]

theorem slopeInterior12Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row11 ((361/25)*v) := by
  simp only [slopeInterior12Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior12Row11,mul_pow]

theorem slopeInterior12Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row12 ((361/25)*v) := by
  simp only [slopeInterior12Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior12Row12,mul_pow]

theorem slopeInterior12Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row13 ((361/25)*v) := by
  simp only [slopeInterior12Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior12Row13,mul_pow]

theorem slopeInterior12Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row14 ((361/25)*v) := by
  simp only [slopeInterior12Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior12Row14,mul_pow]

theorem slopeInterior12Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row15 ((361/25)*v) := by
  simp only [slopeInterior12Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior12Row15,mul_pow]

theorem slopeInterior12Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row16 ((361/25)*v) := by
  simp only [slopeInterior12Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior12Row16,mul_pow]

theorem slopeInterior12Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row17 ((361/25)*v) := by
  simp only [slopeInterior12Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior12Row17,mul_pow]

theorem slopeInterior12Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row18 ((361/25)*v) := by
  simp only [slopeInterior12Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior12Row18,mul_pow]

theorem slopeInterior12Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row19 ((361/25)*v) := by
  simp only [slopeInterior12Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior12Row19,mul_pow]

theorem slopeInterior12Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row20 ((361/25)*v) := by
  simp only [slopeInterior12Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior12Row20,mul_pow]

theorem slopeInterior12Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row21 ((361/25)*v) := by
  simp only [slopeInterior12Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row21,mul_pow]

theorem slopeInterior12Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row22 ((361/25)*v) := by
  simp only [slopeInterior12Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row22,mul_pow]

theorem slopeInterior12Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row23 ((361/25)*v) := by
  simp only [slopeInterior12Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row23,mul_pow]

theorem slopeInterior12Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row24 ((361/25)*v) := by
  simp only [slopeInterior12Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row24,mul_pow]

theorem slopeInterior12Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row25 ((361/25)*v) := by
  simp only [slopeInterior12Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row25,mul_pow]

theorem slopeInterior12Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row26 ((361/25)*v) := by
  simp only [slopeInterior12Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row26,mul_pow]

theorem slopeInterior12Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row27 ((361/25)*v) := by
  simp only [slopeInterior12Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row27,mul_pow]

theorem slopeInterior12Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row28 ((361/25)*v) := by
  simp only [slopeInterior12Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row28,mul_pow]

theorem slopeInterior12Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row29 ((361/25)*v) := by
  simp only [slopeInterior12Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row29,mul_pow]

theorem slopeInterior12Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row30 ((361/25)*v) := by
  simp only [slopeInterior12Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row30,mul_pow]

theorem slopeInterior12Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row31 ((361/25)*v) := by
  simp only [slopeInterior12Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row31,mul_pow]

theorem slopeInterior12Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row32 ((361/25)*v) := by
  simp only [slopeInterior12Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row32,mul_pow]

theorem slopeInterior12Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row33 ((361/25)*v) := by
  simp only [slopeInterior12Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row33,mul_pow]

theorem slopeInterior12Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row34 ((361/25)*v) := by
  simp only [slopeInterior12Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row34,mul_pow]

theorem slopeInterior12Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row35 ((361/25)*v) := by
  simp only [slopeInterior12Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row35,mul_pow]

theorem slopeInterior12Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row36 ((361/25)*v) := by
  simp only [slopeInterior12Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row36,mul_pow]

theorem slopeInterior12Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row37 ((361/25)*v) := by
  simp only [slopeInterior12Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row37,mul_pow]

theorem slopeInterior12Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row38 ((361/25)*v) := by
  simp only [slopeInterior12Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row38,mul_pow]

theorem slopeInterior12Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row39 ((361/25)*v) := by
  simp only [slopeInterior12Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row39,mul_pow]

theorem slopeInterior12Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row40 ((361/25)*v) := by
  simp only [slopeInterior12Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row40,mul_pow]

theorem slopeInterior12Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row41 ((361/25)*v) := by
  simp only [slopeInterior12Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row41,mul_pow]

theorem slopeInterior12Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior12Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior12Row42 ((361/25)*v) := by
  simp only [slopeInterior12Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior12Row42,mul_pow]

def slopeInterior12TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior12TensorCoefficient A) v) t

theorem slopeInterior12TensorValue_reconstruction (t v : ℝ) :
    slopeInterior12TensorValue t v=slopeInterior12Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior12TensorValue slopeInterior12TensorCoefficient slopeInterior12ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior12Form4_reconstruction,slopeInterior12Form5_reconstruction,slopeInterior12Form6_reconstruction,slopeInterior12Form7_reconstruction,slopeInterior12Form8_reconstruction,slopeInterior12Form9_reconstruction,slopeInterior12Form10_reconstruction,slopeInterior12Form11_reconstruction,slopeInterior12Form12_reconstruction,slopeInterior12Form13_reconstruction,slopeInterior12Form14_reconstruction,slopeInterior12Form15_reconstruction,slopeInterior12Form16_reconstruction,slopeInterior12Form17_reconstruction,slopeInterior12Form18_reconstruction,slopeInterior12Form19_reconstruction,slopeInterior12Form20_reconstruction,slopeInterior12Form21_reconstruction,slopeInterior12Form22_reconstruction,slopeInterior12Form23_reconstruction,slopeInterior12Form24_reconstruction,slopeInterior12Form25_reconstruction,slopeInterior12Form26_reconstruction,slopeInterior12Form27_reconstruction,slopeInterior12Form28_reconstruction,slopeInterior12Form29_reconstruction,slopeInterior12Form30_reconstruction,slopeInterior12Form31_reconstruction,slopeInterior12Form32_reconstruction,slopeInterior12Form33_reconstruction,slopeInterior12Form34_reconstruction,slopeInterior12Form35_reconstruction,slopeInterior12Form36_reconstruction,slopeInterior12Form37_reconstruction,slopeInterior12Form38_reconstruction,slopeInterior12Form39_reconstruction,slopeInterior12Form40_reconstruction,slopeInterior12Form41_reconstruction,slopeInterior12Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior12Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

