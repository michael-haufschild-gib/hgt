import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior17TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior17Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row4 ((361/25)*v) := by
  simp only [slopeInterior17Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior17Row4,mul_pow]

theorem slopeInterior17Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row5 ((361/25)*v) := by
  simp only [slopeInterior17Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior17Row5,mul_pow]

theorem slopeInterior17Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row6 ((361/25)*v) := by
  simp only [slopeInterior17Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior17Row6,mul_pow]

theorem slopeInterior17Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row7 ((361/25)*v) := by
  simp only [slopeInterior17Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior17Row7,mul_pow]

theorem slopeInterior17Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row8 ((361/25)*v) := by
  simp only [slopeInterior17Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior17Row8,mul_pow]

theorem slopeInterior17Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row9 ((361/25)*v) := by
  simp only [slopeInterior17Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior17Row9,mul_pow]

theorem slopeInterior17Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row10 ((361/25)*v) := by
  simp only [slopeInterior17Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior17Row10,mul_pow]

theorem slopeInterior17Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row11 ((361/25)*v) := by
  simp only [slopeInterior17Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior17Row11,mul_pow]

theorem slopeInterior17Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row12 ((361/25)*v) := by
  simp only [slopeInterior17Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior17Row12,mul_pow]

theorem slopeInterior17Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row13 ((361/25)*v) := by
  simp only [slopeInterior17Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior17Row13,mul_pow]

theorem slopeInterior17Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row14 ((361/25)*v) := by
  simp only [slopeInterior17Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior17Row14,mul_pow]

theorem slopeInterior17Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row15 ((361/25)*v) := by
  simp only [slopeInterior17Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior17Row15,mul_pow]

theorem slopeInterior17Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row16 ((361/25)*v) := by
  simp only [slopeInterior17Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior17Row16,mul_pow]

theorem slopeInterior17Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row17 ((361/25)*v) := by
  simp only [slopeInterior17Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior17Row17,mul_pow]

theorem slopeInterior17Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row18 ((361/25)*v) := by
  simp only [slopeInterior17Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior17Row18,mul_pow]

theorem slopeInterior17Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row19 ((361/25)*v) := by
  simp only [slopeInterior17Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior17Row19,mul_pow]

theorem slopeInterior17Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row20 ((361/25)*v) := by
  simp only [slopeInterior17Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior17Row20,mul_pow]

theorem slopeInterior17Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row21 ((361/25)*v) := by
  simp only [slopeInterior17Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row21,mul_pow]

theorem slopeInterior17Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row22 ((361/25)*v) := by
  simp only [slopeInterior17Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row22,mul_pow]

theorem slopeInterior17Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row23 ((361/25)*v) := by
  simp only [slopeInterior17Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row23,mul_pow]

theorem slopeInterior17Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row24 ((361/25)*v) := by
  simp only [slopeInterior17Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row24,mul_pow]

theorem slopeInterior17Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row25 ((361/25)*v) := by
  simp only [slopeInterior17Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row25,mul_pow]

theorem slopeInterior17Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row26 ((361/25)*v) := by
  simp only [slopeInterior17Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row26,mul_pow]

theorem slopeInterior17Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row27 ((361/25)*v) := by
  simp only [slopeInterior17Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row27,mul_pow]

theorem slopeInterior17Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row28 ((361/25)*v) := by
  simp only [slopeInterior17Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row28,mul_pow]

theorem slopeInterior17Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row29 ((361/25)*v) := by
  simp only [slopeInterior17Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row29,mul_pow]

theorem slopeInterior17Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row30 ((361/25)*v) := by
  simp only [slopeInterior17Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row30,mul_pow]

theorem slopeInterior17Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row31 ((361/25)*v) := by
  simp only [slopeInterior17Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row31,mul_pow]

theorem slopeInterior17Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row32 ((361/25)*v) := by
  simp only [slopeInterior17Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row32,mul_pow]

theorem slopeInterior17Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row33 ((361/25)*v) := by
  simp only [slopeInterior17Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row33,mul_pow]

theorem slopeInterior17Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row34 ((361/25)*v) := by
  simp only [slopeInterior17Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row34,mul_pow]

theorem slopeInterior17Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row35 ((361/25)*v) := by
  simp only [slopeInterior17Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row35,mul_pow]

theorem slopeInterior17Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row36 ((361/25)*v) := by
  simp only [slopeInterior17Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row36,mul_pow]

theorem slopeInterior17Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row37 ((361/25)*v) := by
  simp only [slopeInterior17Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row37,mul_pow]

theorem slopeInterior17Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row38 ((361/25)*v) := by
  simp only [slopeInterior17Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row38,mul_pow]

theorem slopeInterior17Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row39 ((361/25)*v) := by
  simp only [slopeInterior17Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row39,mul_pow]

theorem slopeInterior17Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row40 ((361/25)*v) := by
  simp only [slopeInterior17Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row40,mul_pow]

theorem slopeInterior17Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row41 ((361/25)*v) := by
  simp only [slopeInterior17Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row41,mul_pow]

theorem slopeInterior17Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior17Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior17Row42 ((361/25)*v) := by
  simp only [slopeInterior17Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior17Row42,mul_pow]

def slopeInterior17TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior17TensorCoefficient A) v) t

theorem slopeInterior17TensorValue_reconstruction (t v : ℝ) :
    slopeInterior17TensorValue t v=slopeInterior17Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior17TensorValue slopeInterior17TensorCoefficient slopeInterior17ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior17Form4_reconstruction,slopeInterior17Form5_reconstruction,slopeInterior17Form6_reconstruction,slopeInterior17Form7_reconstruction,slopeInterior17Form8_reconstruction,slopeInterior17Form9_reconstruction,slopeInterior17Form10_reconstruction,slopeInterior17Form11_reconstruction,slopeInterior17Form12_reconstruction,slopeInterior17Form13_reconstruction,slopeInterior17Form14_reconstruction,slopeInterior17Form15_reconstruction,slopeInterior17Form16_reconstruction,slopeInterior17Form17_reconstruction,slopeInterior17Form18_reconstruction,slopeInterior17Form19_reconstruction,slopeInterior17Form20_reconstruction,slopeInterior17Form21_reconstruction,slopeInterior17Form22_reconstruction,slopeInterior17Form23_reconstruction,slopeInterior17Form24_reconstruction,slopeInterior17Form25_reconstruction,slopeInterior17Form26_reconstruction,slopeInterior17Form27_reconstruction,slopeInterior17Form28_reconstruction,slopeInterior17Form29_reconstruction,slopeInterior17Form30_reconstruction,slopeInterior17Form31_reconstruction,slopeInterior17Form32_reconstruction,slopeInterior17Form33_reconstruction,slopeInterior17Form34_reconstruction,slopeInterior17Form35_reconstruction,slopeInterior17Form36_reconstruction,slopeInterior17Form37_reconstruction,slopeInterior17Form38_reconstruction,slopeInterior17Form39_reconstruction,slopeInterior17Form40_reconstruction,slopeInterior17Form41_reconstruction,slopeInterior17Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior17Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

