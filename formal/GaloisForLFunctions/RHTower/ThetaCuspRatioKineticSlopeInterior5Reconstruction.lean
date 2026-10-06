import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior5TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior5Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row4 ((361/25)*v) := by
  simp only [slopeInterior5Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior5Row4,mul_pow]

theorem slopeInterior5Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row5 ((361/25)*v) := by
  simp only [slopeInterior5Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior5Row5,mul_pow]

theorem slopeInterior5Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row6 ((361/25)*v) := by
  simp only [slopeInterior5Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior5Row6,mul_pow]

theorem slopeInterior5Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row7 ((361/25)*v) := by
  simp only [slopeInterior5Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior5Row7,mul_pow]

theorem slopeInterior5Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row8 ((361/25)*v) := by
  simp only [slopeInterior5Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior5Row8,mul_pow]

theorem slopeInterior5Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row9 ((361/25)*v) := by
  simp only [slopeInterior5Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior5Row9,mul_pow]

theorem slopeInterior5Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row10 ((361/25)*v) := by
  simp only [slopeInterior5Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior5Row10,mul_pow]

theorem slopeInterior5Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row11 ((361/25)*v) := by
  simp only [slopeInterior5Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior5Row11,mul_pow]

theorem slopeInterior5Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row12 ((361/25)*v) := by
  simp only [slopeInterior5Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior5Row12,mul_pow]

theorem slopeInterior5Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row13 ((361/25)*v) := by
  simp only [slopeInterior5Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior5Row13,mul_pow]

theorem slopeInterior5Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row14 ((361/25)*v) := by
  simp only [slopeInterior5Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior5Row14,mul_pow]

theorem slopeInterior5Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row15 ((361/25)*v) := by
  simp only [slopeInterior5Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior5Row15,mul_pow]

theorem slopeInterior5Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row16 ((361/25)*v) := by
  simp only [slopeInterior5Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior5Row16,mul_pow]

theorem slopeInterior5Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row17 ((361/25)*v) := by
  simp only [slopeInterior5Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior5Row17,mul_pow]

theorem slopeInterior5Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row18 ((361/25)*v) := by
  simp only [slopeInterior5Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior5Row18,mul_pow]

theorem slopeInterior5Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row19 ((361/25)*v) := by
  simp only [slopeInterior5Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior5Row19,mul_pow]

theorem slopeInterior5Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row20 ((361/25)*v) := by
  simp only [slopeInterior5Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior5Row20,mul_pow]

theorem slopeInterior5Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row21 ((361/25)*v) := by
  simp only [slopeInterior5Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row21,mul_pow]

theorem slopeInterior5Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row22 ((361/25)*v) := by
  simp only [slopeInterior5Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row22,mul_pow]

theorem slopeInterior5Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row23 ((361/25)*v) := by
  simp only [slopeInterior5Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row23,mul_pow]

theorem slopeInterior5Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row24 ((361/25)*v) := by
  simp only [slopeInterior5Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row24,mul_pow]

theorem slopeInterior5Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row25 ((361/25)*v) := by
  simp only [slopeInterior5Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row25,mul_pow]

theorem slopeInterior5Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row26 ((361/25)*v) := by
  simp only [slopeInterior5Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row26,mul_pow]

theorem slopeInterior5Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row27 ((361/25)*v) := by
  simp only [slopeInterior5Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row27,mul_pow]

theorem slopeInterior5Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row28 ((361/25)*v) := by
  simp only [slopeInterior5Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row28,mul_pow]

theorem slopeInterior5Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row29 ((361/25)*v) := by
  simp only [slopeInterior5Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row29,mul_pow]

theorem slopeInterior5Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row30 ((361/25)*v) := by
  simp only [slopeInterior5Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row30,mul_pow]

theorem slopeInterior5Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row31 ((361/25)*v) := by
  simp only [slopeInterior5Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row31,mul_pow]

theorem slopeInterior5Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row32 ((361/25)*v) := by
  simp only [slopeInterior5Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row32,mul_pow]

theorem slopeInterior5Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row33 ((361/25)*v) := by
  simp only [slopeInterior5Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row33,mul_pow]

theorem slopeInterior5Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row34 ((361/25)*v) := by
  simp only [slopeInterior5Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row34,mul_pow]

theorem slopeInterior5Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row35 ((361/25)*v) := by
  simp only [slopeInterior5Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row35,mul_pow]

theorem slopeInterior5Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row36 ((361/25)*v) := by
  simp only [slopeInterior5Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row36,mul_pow]

theorem slopeInterior5Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row37 ((361/25)*v) := by
  simp only [slopeInterior5Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row37,mul_pow]

theorem slopeInterior5Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row38 ((361/25)*v) := by
  simp only [slopeInterior5Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row38,mul_pow]

theorem slopeInterior5Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row39 ((361/25)*v) := by
  simp only [slopeInterior5Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row39,mul_pow]

theorem slopeInterior5Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row40 ((361/25)*v) := by
  simp only [slopeInterior5Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row40,mul_pow]

theorem slopeInterior5Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row41 ((361/25)*v) := by
  simp only [slopeInterior5Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row41,mul_pow]

theorem slopeInterior5Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior5Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior5Row42 ((361/25)*v) := by
  simp only [slopeInterior5Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior5Row42,mul_pow]

def slopeInterior5TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior5TensorCoefficient A) v) t

theorem slopeInterior5TensorValue_reconstruction (t v : ℝ) :
    slopeInterior5TensorValue t v=slopeInterior5Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior5TensorValue slopeInterior5TensorCoefficient slopeInterior5ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior5Form4_reconstruction,slopeInterior5Form5_reconstruction,slopeInterior5Form6_reconstruction,slopeInterior5Form7_reconstruction,slopeInterior5Form8_reconstruction,slopeInterior5Form9_reconstruction,slopeInterior5Form10_reconstruction,slopeInterior5Form11_reconstruction,slopeInterior5Form12_reconstruction,slopeInterior5Form13_reconstruction,slopeInterior5Form14_reconstruction,slopeInterior5Form15_reconstruction,slopeInterior5Form16_reconstruction,slopeInterior5Form17_reconstruction,slopeInterior5Form18_reconstruction,slopeInterior5Form19_reconstruction,slopeInterior5Form20_reconstruction,slopeInterior5Form21_reconstruction,slopeInterior5Form22_reconstruction,slopeInterior5Form23_reconstruction,slopeInterior5Form24_reconstruction,slopeInterior5Form25_reconstruction,slopeInterior5Form26_reconstruction,slopeInterior5Form27_reconstruction,slopeInterior5Form28_reconstruction,slopeInterior5Form29_reconstruction,slopeInterior5Form30_reconstruction,slopeInterior5Form31_reconstruction,slopeInterior5Form32_reconstruction,slopeInterior5Form33_reconstruction,slopeInterior5Form34_reconstruction,slopeInterior5Form35_reconstruction,slopeInterior5Form36_reconstruction,slopeInterior5Form37_reconstruction,slopeInterior5Form38_reconstruction,slopeInterior5Form39_reconstruction,slopeInterior5Form40_reconstruction,slopeInterior5Form41_reconstruction,slopeInterior5Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior5Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

