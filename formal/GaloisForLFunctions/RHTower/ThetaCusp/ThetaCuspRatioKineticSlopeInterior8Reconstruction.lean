import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior8Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row4 ((361/25)*v) := by
  simp only [slopeInterior8Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior8Row4,mul_pow]

theorem slopeInterior8Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row5 ((361/25)*v) := by
  simp only [slopeInterior8Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior8Row5,mul_pow]

theorem slopeInterior8Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row6 ((361/25)*v) := by
  simp only [slopeInterior8Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior8Row6,mul_pow]

theorem slopeInterior8Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row7 ((361/25)*v) := by
  simp only [slopeInterior8Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior8Row7,mul_pow]

theorem slopeInterior8Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row8 ((361/25)*v) := by
  simp only [slopeInterior8Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior8Row8,mul_pow]

theorem slopeInterior8Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row9 ((361/25)*v) := by
  simp only [slopeInterior8Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior8Row9,mul_pow]

theorem slopeInterior8Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row10 ((361/25)*v) := by
  simp only [slopeInterior8Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior8Row10,mul_pow]

theorem slopeInterior8Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row11 ((361/25)*v) := by
  simp only [slopeInterior8Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior8Row11,mul_pow]

theorem slopeInterior8Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row12 ((361/25)*v) := by
  simp only [slopeInterior8Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior8Row12,mul_pow]

theorem slopeInterior8Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row13 ((361/25)*v) := by
  simp only [slopeInterior8Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior8Row13,mul_pow]

theorem slopeInterior8Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row14 ((361/25)*v) := by
  simp only [slopeInterior8Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior8Row14,mul_pow]

theorem slopeInterior8Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row15 ((361/25)*v) := by
  simp only [slopeInterior8Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior8Row15,mul_pow]

theorem slopeInterior8Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row16 ((361/25)*v) := by
  simp only [slopeInterior8Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior8Row16,mul_pow]

theorem slopeInterior8Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row17 ((361/25)*v) := by
  simp only [slopeInterior8Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior8Row17,mul_pow]

theorem slopeInterior8Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row18 ((361/25)*v) := by
  simp only [slopeInterior8Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior8Row18,mul_pow]

theorem slopeInterior8Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row19 ((361/25)*v) := by
  simp only [slopeInterior8Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior8Row19,mul_pow]

theorem slopeInterior8Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row20 ((361/25)*v) := by
  simp only [slopeInterior8Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior8Row20,mul_pow]

theorem slopeInterior8Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row21 ((361/25)*v) := by
  simp only [slopeInterior8Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row21,mul_pow]

theorem slopeInterior8Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row22 ((361/25)*v) := by
  simp only [slopeInterior8Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row22,mul_pow]

theorem slopeInterior8Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row23 ((361/25)*v) := by
  simp only [slopeInterior8Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row23,mul_pow]

theorem slopeInterior8Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row24 ((361/25)*v) := by
  simp only [slopeInterior8Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row24,mul_pow]

theorem slopeInterior8Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row25 ((361/25)*v) := by
  simp only [slopeInterior8Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row25,mul_pow]

theorem slopeInterior8Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row26 ((361/25)*v) := by
  simp only [slopeInterior8Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row26,mul_pow]

theorem slopeInterior8Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row27 ((361/25)*v) := by
  simp only [slopeInterior8Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row27,mul_pow]

theorem slopeInterior8Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row28 ((361/25)*v) := by
  simp only [slopeInterior8Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row28,mul_pow]

theorem slopeInterior8Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row29 ((361/25)*v) := by
  simp only [slopeInterior8Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row29,mul_pow]

theorem slopeInterior8Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row30 ((361/25)*v) := by
  simp only [slopeInterior8Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row30,mul_pow]

theorem slopeInterior8Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row31 ((361/25)*v) := by
  simp only [slopeInterior8Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row31,mul_pow]

theorem slopeInterior8Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row32 ((361/25)*v) := by
  simp only [slopeInterior8Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row32,mul_pow]

theorem slopeInterior8Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row33 ((361/25)*v) := by
  simp only [slopeInterior8Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row33,mul_pow]

theorem slopeInterior8Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row34 ((361/25)*v) := by
  simp only [slopeInterior8Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row34,mul_pow]

theorem slopeInterior8Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row35 ((361/25)*v) := by
  simp only [slopeInterior8Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row35,mul_pow]

theorem slopeInterior8Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row36 ((361/25)*v) := by
  simp only [slopeInterior8Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row36,mul_pow]

theorem slopeInterior8Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row37 ((361/25)*v) := by
  simp only [slopeInterior8Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row37,mul_pow]

theorem slopeInterior8Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row38 ((361/25)*v) := by
  simp only [slopeInterior8Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row38,mul_pow]

theorem slopeInterior8Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row39 ((361/25)*v) := by
  simp only [slopeInterior8Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row39,mul_pow]

theorem slopeInterior8Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row40 ((361/25)*v) := by
  simp only [slopeInterior8Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row40,mul_pow]

theorem slopeInterior8Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row41 ((361/25)*v) := by
  simp only [slopeInterior8Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row41,mul_pow]

theorem slopeInterior8Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior8Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior8Row42 ((361/25)*v) := by
  simp only [slopeInterior8Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior8Row42,mul_pow]

def slopeInterior8TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior8TensorCoefficient A) v) t

theorem slopeInterior8TensorValue_reconstruction (t v : ℝ) :
    slopeInterior8TensorValue t v=slopeInterior8Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior8TensorValue slopeInterior8TensorCoefficient slopeInterior8ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior8Form4_reconstruction,slopeInterior8Form5_reconstruction,slopeInterior8Form6_reconstruction,slopeInterior8Form7_reconstruction,slopeInterior8Form8_reconstruction,slopeInterior8Form9_reconstruction,slopeInterior8Form10_reconstruction,slopeInterior8Form11_reconstruction,slopeInterior8Form12_reconstruction,slopeInterior8Form13_reconstruction,slopeInterior8Form14_reconstruction,slopeInterior8Form15_reconstruction,slopeInterior8Form16_reconstruction,slopeInterior8Form17_reconstruction,slopeInterior8Form18_reconstruction,slopeInterior8Form19_reconstruction,slopeInterior8Form20_reconstruction,slopeInterior8Form21_reconstruction,slopeInterior8Form22_reconstruction,slopeInterior8Form23_reconstruction,slopeInterior8Form24_reconstruction,slopeInterior8Form25_reconstruction,slopeInterior8Form26_reconstruction,slopeInterior8Form27_reconstruction,slopeInterior8Form28_reconstruction,slopeInterior8Form29_reconstruction,slopeInterior8Form30_reconstruction,slopeInterior8Form31_reconstruction,slopeInterior8Form32_reconstruction,slopeInterior8Form33_reconstruction,slopeInterior8Form34_reconstruction,slopeInterior8Form35_reconstruction,slopeInterior8Form36_reconstruction,slopeInterior8Form37_reconstruction,slopeInterior8Form38_reconstruction,slopeInterior8Form39_reconstruction,slopeInterior8Form40_reconstruction,slopeInterior8Form41_reconstruction,slopeInterior8Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior8Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

