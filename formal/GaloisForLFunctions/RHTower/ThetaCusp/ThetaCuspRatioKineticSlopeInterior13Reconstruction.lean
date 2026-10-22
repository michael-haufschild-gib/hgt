import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior13TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior13Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row4 ((361/25)*v) := by
  simp only [slopeInterior13Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior13Row4,mul_pow]

theorem slopeInterior13Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row5 ((361/25)*v) := by
  simp only [slopeInterior13Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior13Row5,mul_pow]

theorem slopeInterior13Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row6 ((361/25)*v) := by
  simp only [slopeInterior13Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior13Row6,mul_pow]

theorem slopeInterior13Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row7 ((361/25)*v) := by
  simp only [slopeInterior13Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior13Row7,mul_pow]

theorem slopeInterior13Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row8 ((361/25)*v) := by
  simp only [slopeInterior13Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior13Row8,mul_pow]

theorem slopeInterior13Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row9 ((361/25)*v) := by
  simp only [slopeInterior13Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior13Row9,mul_pow]

theorem slopeInterior13Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row10 ((361/25)*v) := by
  simp only [slopeInterior13Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior13Row10,mul_pow]

theorem slopeInterior13Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row11 ((361/25)*v) := by
  simp only [slopeInterior13Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior13Row11,mul_pow]

theorem slopeInterior13Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row12 ((361/25)*v) := by
  simp only [slopeInterior13Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior13Row12,mul_pow]

theorem slopeInterior13Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row13 ((361/25)*v) := by
  simp only [slopeInterior13Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior13Row13,mul_pow]

theorem slopeInterior13Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row14 ((361/25)*v) := by
  simp only [slopeInterior13Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior13Row14,mul_pow]

theorem slopeInterior13Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row15 ((361/25)*v) := by
  simp only [slopeInterior13Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior13Row15,mul_pow]

theorem slopeInterior13Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row16 ((361/25)*v) := by
  simp only [slopeInterior13Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior13Row16,mul_pow]

theorem slopeInterior13Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row17 ((361/25)*v) := by
  simp only [slopeInterior13Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior13Row17,mul_pow]

theorem slopeInterior13Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row18 ((361/25)*v) := by
  simp only [slopeInterior13Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior13Row18,mul_pow]

theorem slopeInterior13Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row19 ((361/25)*v) := by
  simp only [slopeInterior13Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior13Row19,mul_pow]

theorem slopeInterior13Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row20 ((361/25)*v) := by
  simp only [slopeInterior13Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior13Row20,mul_pow]

theorem slopeInterior13Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row21 ((361/25)*v) := by
  simp only [slopeInterior13Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row21,mul_pow]

theorem slopeInterior13Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row22 ((361/25)*v) := by
  simp only [slopeInterior13Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row22,mul_pow]

theorem slopeInterior13Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row23 ((361/25)*v) := by
  simp only [slopeInterior13Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row23,mul_pow]

theorem slopeInterior13Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row24 ((361/25)*v) := by
  simp only [slopeInterior13Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row24,mul_pow]

theorem slopeInterior13Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row25 ((361/25)*v) := by
  simp only [slopeInterior13Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row25,mul_pow]

theorem slopeInterior13Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row26 ((361/25)*v) := by
  simp only [slopeInterior13Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row26,mul_pow]

theorem slopeInterior13Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row27 ((361/25)*v) := by
  simp only [slopeInterior13Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row27,mul_pow]

theorem slopeInterior13Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row28 ((361/25)*v) := by
  simp only [slopeInterior13Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row28,mul_pow]

theorem slopeInterior13Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row29 ((361/25)*v) := by
  simp only [slopeInterior13Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row29,mul_pow]

theorem slopeInterior13Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row30 ((361/25)*v) := by
  simp only [slopeInterior13Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row30,mul_pow]

theorem slopeInterior13Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row31 ((361/25)*v) := by
  simp only [slopeInterior13Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row31,mul_pow]

theorem slopeInterior13Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row32 ((361/25)*v) := by
  simp only [slopeInterior13Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row32,mul_pow]

theorem slopeInterior13Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row33 ((361/25)*v) := by
  simp only [slopeInterior13Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row33,mul_pow]

theorem slopeInterior13Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row34 ((361/25)*v) := by
  simp only [slopeInterior13Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row34,mul_pow]

theorem slopeInterior13Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row35 ((361/25)*v) := by
  simp only [slopeInterior13Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row35,mul_pow]

theorem slopeInterior13Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row36 ((361/25)*v) := by
  simp only [slopeInterior13Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row36,mul_pow]

theorem slopeInterior13Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row37 ((361/25)*v) := by
  simp only [slopeInterior13Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row37,mul_pow]

theorem slopeInterior13Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row38 ((361/25)*v) := by
  simp only [slopeInterior13Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row38,mul_pow]

theorem slopeInterior13Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row39 ((361/25)*v) := by
  simp only [slopeInterior13Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row39,mul_pow]

theorem slopeInterior13Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row40 ((361/25)*v) := by
  simp only [slopeInterior13Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row40,mul_pow]

theorem slopeInterior13Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row41 ((361/25)*v) := by
  simp only [slopeInterior13Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row41,mul_pow]

theorem slopeInterior13Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior13Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior13Row42 ((361/25)*v) := by
  simp only [slopeInterior13Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior13Row42,mul_pow]

def slopeInterior13TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior13TensorCoefficient A) v) t

theorem slopeInterior13TensorValue_reconstruction (t v : ℝ) :
    slopeInterior13TensorValue t v=slopeInterior13Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior13TensorValue slopeInterior13TensorCoefficient slopeInterior13ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior13Form4_reconstruction,slopeInterior13Form5_reconstruction,slopeInterior13Form6_reconstruction,slopeInterior13Form7_reconstruction,slopeInterior13Form8_reconstruction,slopeInterior13Form9_reconstruction,slopeInterior13Form10_reconstruction,slopeInterior13Form11_reconstruction,slopeInterior13Form12_reconstruction,slopeInterior13Form13_reconstruction,slopeInterior13Form14_reconstruction,slopeInterior13Form15_reconstruction,slopeInterior13Form16_reconstruction,slopeInterior13Form17_reconstruction,slopeInterior13Form18_reconstruction,slopeInterior13Form19_reconstruction,slopeInterior13Form20_reconstruction,slopeInterior13Form21_reconstruction,slopeInterior13Form22_reconstruction,slopeInterior13Form23_reconstruction,slopeInterior13Form24_reconstruction,slopeInterior13Form25_reconstruction,slopeInterior13Form26_reconstruction,slopeInterior13Form27_reconstruction,slopeInterior13Form28_reconstruction,slopeInterior13Form29_reconstruction,slopeInterior13Form30_reconstruction,slopeInterior13Form31_reconstruction,slopeInterior13Form32_reconstruction,slopeInterior13Form33_reconstruction,slopeInterior13Form34_reconstruction,slopeInterior13Form35_reconstruction,slopeInterior13Form36_reconstruction,slopeInterior13Form37_reconstruction,slopeInterior13Form38_reconstruction,slopeInterior13Form39_reconstruction,slopeInterior13Form40_reconstruction,slopeInterior13Form41_reconstruction,slopeInterior13Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior13Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

