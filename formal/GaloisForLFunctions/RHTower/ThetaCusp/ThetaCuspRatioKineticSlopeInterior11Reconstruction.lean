import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior11TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior11Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row4 ((361/25)*v) := by
  simp only [slopeInterior11Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior11Row4,mul_pow]

theorem slopeInterior11Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row5 ((361/25)*v) := by
  simp only [slopeInterior11Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior11Row5,mul_pow]

theorem slopeInterior11Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row6 ((361/25)*v) := by
  simp only [slopeInterior11Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior11Row6,mul_pow]

theorem slopeInterior11Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row7 ((361/25)*v) := by
  simp only [slopeInterior11Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior11Row7,mul_pow]

theorem slopeInterior11Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row8 ((361/25)*v) := by
  simp only [slopeInterior11Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior11Row8,mul_pow]

theorem slopeInterior11Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row9 ((361/25)*v) := by
  simp only [slopeInterior11Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior11Row9,mul_pow]

theorem slopeInterior11Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row10 ((361/25)*v) := by
  simp only [slopeInterior11Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior11Row10,mul_pow]

theorem slopeInterior11Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row11 ((361/25)*v) := by
  simp only [slopeInterior11Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior11Row11,mul_pow]

theorem slopeInterior11Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row12 ((361/25)*v) := by
  simp only [slopeInterior11Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior11Row12,mul_pow]

theorem slopeInterior11Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row13 ((361/25)*v) := by
  simp only [slopeInterior11Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior11Row13,mul_pow]

theorem slopeInterior11Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row14 ((361/25)*v) := by
  simp only [slopeInterior11Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior11Row14,mul_pow]

theorem slopeInterior11Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row15 ((361/25)*v) := by
  simp only [slopeInterior11Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior11Row15,mul_pow]

theorem slopeInterior11Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row16 ((361/25)*v) := by
  simp only [slopeInterior11Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior11Row16,mul_pow]

theorem slopeInterior11Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row17 ((361/25)*v) := by
  simp only [slopeInterior11Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior11Row17,mul_pow]

theorem slopeInterior11Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row18 ((361/25)*v) := by
  simp only [slopeInterior11Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior11Row18,mul_pow]

theorem slopeInterior11Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row19 ((361/25)*v) := by
  simp only [slopeInterior11Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior11Row19,mul_pow]

theorem slopeInterior11Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row20 ((361/25)*v) := by
  simp only [slopeInterior11Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior11Row20,mul_pow]

theorem slopeInterior11Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row21 ((361/25)*v) := by
  simp only [slopeInterior11Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row21,mul_pow]

theorem slopeInterior11Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row22 ((361/25)*v) := by
  simp only [slopeInterior11Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row22,mul_pow]

theorem slopeInterior11Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row23 ((361/25)*v) := by
  simp only [slopeInterior11Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row23,mul_pow]

theorem slopeInterior11Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row24 ((361/25)*v) := by
  simp only [slopeInterior11Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row24,mul_pow]

theorem slopeInterior11Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row25 ((361/25)*v) := by
  simp only [slopeInterior11Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row25,mul_pow]

theorem slopeInterior11Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row26 ((361/25)*v) := by
  simp only [slopeInterior11Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row26,mul_pow]

theorem slopeInterior11Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row27 ((361/25)*v) := by
  simp only [slopeInterior11Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row27,mul_pow]

theorem slopeInterior11Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row28 ((361/25)*v) := by
  simp only [slopeInterior11Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row28,mul_pow]

theorem slopeInterior11Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row29 ((361/25)*v) := by
  simp only [slopeInterior11Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row29,mul_pow]

theorem slopeInterior11Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row30 ((361/25)*v) := by
  simp only [slopeInterior11Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row30,mul_pow]

theorem slopeInterior11Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row31 ((361/25)*v) := by
  simp only [slopeInterior11Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row31,mul_pow]

theorem slopeInterior11Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row32 ((361/25)*v) := by
  simp only [slopeInterior11Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row32,mul_pow]

theorem slopeInterior11Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row33 ((361/25)*v) := by
  simp only [slopeInterior11Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row33,mul_pow]

theorem slopeInterior11Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row34 ((361/25)*v) := by
  simp only [slopeInterior11Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row34,mul_pow]

theorem slopeInterior11Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row35 ((361/25)*v) := by
  simp only [slopeInterior11Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row35,mul_pow]

theorem slopeInterior11Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row36 ((361/25)*v) := by
  simp only [slopeInterior11Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row36,mul_pow]

theorem slopeInterior11Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row37 ((361/25)*v) := by
  simp only [slopeInterior11Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row37,mul_pow]

theorem slopeInterior11Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row38 ((361/25)*v) := by
  simp only [slopeInterior11Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row38,mul_pow]

theorem slopeInterior11Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row39 ((361/25)*v) := by
  simp only [slopeInterior11Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row39,mul_pow]

theorem slopeInterior11Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row40 ((361/25)*v) := by
  simp only [slopeInterior11Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row40,mul_pow]

theorem slopeInterior11Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row41 ((361/25)*v) := by
  simp only [slopeInterior11Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row41,mul_pow]

theorem slopeInterior11Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior11Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior11Row42 ((361/25)*v) := by
  simp only [slopeInterior11Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior11Row42,mul_pow]

def slopeInterior11TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior11TensorCoefficient A) v) t

theorem slopeInterior11TensorValue_reconstruction (t v : ℝ) :
    slopeInterior11TensorValue t v=slopeInterior11Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior11TensorValue slopeInterior11TensorCoefficient slopeInterior11ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior11Form4_reconstruction,slopeInterior11Form5_reconstruction,slopeInterior11Form6_reconstruction,slopeInterior11Form7_reconstruction,slopeInterior11Form8_reconstruction,slopeInterior11Form9_reconstruction,slopeInterior11Form10_reconstruction,slopeInterior11Form11_reconstruction,slopeInterior11Form12_reconstruction,slopeInterior11Form13_reconstruction,slopeInterior11Form14_reconstruction,slopeInterior11Form15_reconstruction,slopeInterior11Form16_reconstruction,slopeInterior11Form17_reconstruction,slopeInterior11Form18_reconstruction,slopeInterior11Form19_reconstruction,slopeInterior11Form20_reconstruction,slopeInterior11Form21_reconstruction,slopeInterior11Form22_reconstruction,slopeInterior11Form23_reconstruction,slopeInterior11Form24_reconstruction,slopeInterior11Form25_reconstruction,slopeInterior11Form26_reconstruction,slopeInterior11Form27_reconstruction,slopeInterior11Form28_reconstruction,slopeInterior11Form29_reconstruction,slopeInterior11Form30_reconstruction,slopeInterior11Form31_reconstruction,slopeInterior11Form32_reconstruction,slopeInterior11Form33_reconstruction,slopeInterior11Form34_reconstruction,slopeInterior11Form35_reconstruction,slopeInterior11Form36_reconstruction,slopeInterior11Form37_reconstruction,slopeInterior11Form38_reconstruction,slopeInterior11Form39_reconstruction,slopeInterior11Form40_reconstruction,slopeInterior11Form41_reconstruction,slopeInterior11Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior11Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

