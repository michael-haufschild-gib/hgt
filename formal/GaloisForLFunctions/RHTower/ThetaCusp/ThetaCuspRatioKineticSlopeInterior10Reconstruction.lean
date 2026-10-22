import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior10TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior10Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row4 ((361/25)*v) := by
  simp only [slopeInterior10Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior10Row4,mul_pow]

theorem slopeInterior10Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row5 ((361/25)*v) := by
  simp only [slopeInterior10Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior10Row5,mul_pow]

theorem slopeInterior10Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row6 ((361/25)*v) := by
  simp only [slopeInterior10Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior10Row6,mul_pow]

theorem slopeInterior10Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row7 ((361/25)*v) := by
  simp only [slopeInterior10Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior10Row7,mul_pow]

theorem slopeInterior10Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row8 ((361/25)*v) := by
  simp only [slopeInterior10Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior10Row8,mul_pow]

theorem slopeInterior10Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row9 ((361/25)*v) := by
  simp only [slopeInterior10Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior10Row9,mul_pow]

theorem slopeInterior10Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row10 ((361/25)*v) := by
  simp only [slopeInterior10Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior10Row10,mul_pow]

theorem slopeInterior10Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row11 ((361/25)*v) := by
  simp only [slopeInterior10Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior10Row11,mul_pow]

theorem slopeInterior10Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row12 ((361/25)*v) := by
  simp only [slopeInterior10Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior10Row12,mul_pow]

theorem slopeInterior10Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row13 ((361/25)*v) := by
  simp only [slopeInterior10Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior10Row13,mul_pow]

theorem slopeInterior10Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row14 ((361/25)*v) := by
  simp only [slopeInterior10Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior10Row14,mul_pow]

theorem slopeInterior10Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row15 ((361/25)*v) := by
  simp only [slopeInterior10Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior10Row15,mul_pow]

theorem slopeInterior10Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row16 ((361/25)*v) := by
  simp only [slopeInterior10Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior10Row16,mul_pow]

theorem slopeInterior10Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row17 ((361/25)*v) := by
  simp only [slopeInterior10Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior10Row17,mul_pow]

theorem slopeInterior10Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row18 ((361/25)*v) := by
  simp only [slopeInterior10Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior10Row18,mul_pow]

theorem slopeInterior10Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row19 ((361/25)*v) := by
  simp only [slopeInterior10Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior10Row19,mul_pow]

theorem slopeInterior10Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row20 ((361/25)*v) := by
  simp only [slopeInterior10Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior10Row20,mul_pow]

theorem slopeInterior10Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row21 ((361/25)*v) := by
  simp only [slopeInterior10Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row21,mul_pow]

theorem slopeInterior10Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row22 ((361/25)*v) := by
  simp only [slopeInterior10Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row22,mul_pow]

theorem slopeInterior10Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row23 ((361/25)*v) := by
  simp only [slopeInterior10Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row23,mul_pow]

theorem slopeInterior10Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row24 ((361/25)*v) := by
  simp only [slopeInterior10Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row24,mul_pow]

theorem slopeInterior10Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row25 ((361/25)*v) := by
  simp only [slopeInterior10Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row25,mul_pow]

theorem slopeInterior10Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row26 ((361/25)*v) := by
  simp only [slopeInterior10Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row26,mul_pow]

theorem slopeInterior10Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row27 ((361/25)*v) := by
  simp only [slopeInterior10Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row27,mul_pow]

theorem slopeInterior10Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row28 ((361/25)*v) := by
  simp only [slopeInterior10Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row28,mul_pow]

theorem slopeInterior10Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row29 ((361/25)*v) := by
  simp only [slopeInterior10Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row29,mul_pow]

theorem slopeInterior10Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row30 ((361/25)*v) := by
  simp only [slopeInterior10Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row30,mul_pow]

theorem slopeInterior10Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row31 ((361/25)*v) := by
  simp only [slopeInterior10Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row31,mul_pow]

theorem slopeInterior10Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row32 ((361/25)*v) := by
  simp only [slopeInterior10Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row32,mul_pow]

theorem slopeInterior10Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row33 ((361/25)*v) := by
  simp only [slopeInterior10Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row33,mul_pow]

theorem slopeInterior10Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row34 ((361/25)*v) := by
  simp only [slopeInterior10Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row34,mul_pow]

theorem slopeInterior10Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row35 ((361/25)*v) := by
  simp only [slopeInterior10Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row35,mul_pow]

theorem slopeInterior10Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row36 ((361/25)*v) := by
  simp only [slopeInterior10Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row36,mul_pow]

theorem slopeInterior10Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row37 ((361/25)*v) := by
  simp only [slopeInterior10Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row37,mul_pow]

theorem slopeInterior10Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row38 ((361/25)*v) := by
  simp only [slopeInterior10Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row38,mul_pow]

theorem slopeInterior10Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row39 ((361/25)*v) := by
  simp only [slopeInterior10Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row39,mul_pow]

theorem slopeInterior10Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row40 ((361/25)*v) := by
  simp only [slopeInterior10Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row40,mul_pow]

theorem slopeInterior10Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row41 ((361/25)*v) := by
  simp only [slopeInterior10Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row41,mul_pow]

theorem slopeInterior10Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior10Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior10Row42 ((361/25)*v) := by
  simp only [slopeInterior10Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior10Row42,mul_pow]

def slopeInterior10TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior10TensorCoefficient A) v) t

theorem slopeInterior10TensorValue_reconstruction (t v : ℝ) :
    slopeInterior10TensorValue t v=slopeInterior10Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior10TensorValue slopeInterior10TensorCoefficient slopeInterior10ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior10Form4_reconstruction,slopeInterior10Form5_reconstruction,slopeInterior10Form6_reconstruction,slopeInterior10Form7_reconstruction,slopeInterior10Form8_reconstruction,slopeInterior10Form9_reconstruction,slopeInterior10Form10_reconstruction,slopeInterior10Form11_reconstruction,slopeInterior10Form12_reconstruction,slopeInterior10Form13_reconstruction,slopeInterior10Form14_reconstruction,slopeInterior10Form15_reconstruction,slopeInterior10Form16_reconstruction,slopeInterior10Form17_reconstruction,slopeInterior10Form18_reconstruction,slopeInterior10Form19_reconstruction,slopeInterior10Form20_reconstruction,slopeInterior10Form21_reconstruction,slopeInterior10Form22_reconstruction,slopeInterior10Form23_reconstruction,slopeInterior10Form24_reconstruction,slopeInterior10Form25_reconstruction,slopeInterior10Form26_reconstruction,slopeInterior10Form27_reconstruction,slopeInterior10Form28_reconstruction,slopeInterior10Form29_reconstruction,slopeInterior10Form30_reconstruction,slopeInterior10Form31_reconstruction,slopeInterior10Form32_reconstruction,slopeInterior10Form33_reconstruction,slopeInterior10Form34_reconstruction,slopeInterior10Form35_reconstruction,slopeInterior10Form36_reconstruction,slopeInterior10Form37_reconstruction,slopeInterior10Form38_reconstruction,slopeInterior10Form39_reconstruction,slopeInterior10Form40_reconstruction,slopeInterior10Form41_reconstruction,slopeInterior10Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior10Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

