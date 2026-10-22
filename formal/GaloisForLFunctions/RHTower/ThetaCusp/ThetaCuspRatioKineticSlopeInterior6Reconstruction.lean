import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior6TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior6Form4_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form4
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row4 ((361/25)*v) := by
  simp only [slopeInterior6Form4,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega)]
  simp only [slopeInterior6Row4,mul_pow]

theorem slopeInterior6Form5_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form5
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row5 ((361/25)*v) := by
  simp only [slopeInterior6Form5,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior6Row5,mul_pow]

theorem slopeInterior6Form6_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form6
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row6 ((361/25)*v) := by
  simp only [slopeInterior6Form6,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega)]
  simp only [slopeInterior6Row6,mul_pow]

theorem slopeInterior6Form7_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form7
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row7 ((361/25)*v) := by
  simp only [slopeInterior6Form7,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior6Row7,mul_pow]

theorem slopeInterior6Form8_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form8
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row8 ((361/25)*v) := by
  simp only [slopeInterior6Form8,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega)]
  simp only [slopeInterior6Row8,mul_pow]

theorem slopeInterior6Form9_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form9
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row9 ((361/25)*v) := by
  simp only [slopeInterior6Form9,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior6Row9,mul_pow]

theorem slopeInterior6Form10_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form10
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row10 ((361/25)*v) := by
  simp only [slopeInterior6Form10,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega)]
  simp only [slopeInterior6Row10,mul_pow]

theorem slopeInterior6Form11_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form11
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row11 ((361/25)*v) := by
  simp only [slopeInterior6Form11,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior6Row11,mul_pow]

theorem slopeInterior6Form12_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form12
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row12 ((361/25)*v) := by
  simp only [slopeInterior6Form12,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega)]
  simp only [slopeInterior6Row12,mul_pow]

theorem slopeInterior6Form13_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form13
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row13 ((361/25)*v) := by
  simp only [slopeInterior6Form13,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior6Row13,mul_pow]

theorem slopeInterior6Form14_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form14
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row14 ((361/25)*v) := by
  simp only [slopeInterior6Form14,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega)]
  simp only [slopeInterior6Row14,mul_pow]

theorem slopeInterior6Form15_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form15
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row15 ((361/25)*v) := by
  simp only [slopeInterior6Form15,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior6Row15,mul_pow]

theorem slopeInterior6Form16_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form16
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row16 ((361/25)*v) := by
  simp only [slopeInterior6Form16,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega)]
  simp only [slopeInterior6Row16,mul_pow]

theorem slopeInterior6Form17_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form17
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row17 ((361/25)*v) := by
  simp only [slopeInterior6Form17,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior6Row17,mul_pow]

theorem slopeInterior6Form18_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form18
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row18 ((361/25)*v) := by
  simp only [slopeInterior6Form18,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega)]
  simp only [slopeInterior6Row18,mul_pow]

theorem slopeInterior6Form19_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form19
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row19 ((361/25)*v) := by
  simp only [slopeInterior6Form19,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior6Row19,mul_pow]

theorem slopeInterior6Form20_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form20
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row20 ((361/25)*v) := by
  simp only [slopeInterior6Form20,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega)]
  simp only [slopeInterior6Row20,mul_pow]

theorem slopeInterior6Form21_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form21
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row21 ((361/25)*v) := by
  simp only [slopeInterior6Form21,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row21,mul_pow]

theorem slopeInterior6Form22_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form22
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row22 ((361/25)*v) := by
  simp only [slopeInterior6Form22,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row22,mul_pow]

theorem slopeInterior6Form23_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form23
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row23 ((361/25)*v) := by
  simp only [slopeInterior6Form23,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row23,mul_pow]

theorem slopeInterior6Form24_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form24
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row24 ((361/25)*v) := by
  simp only [slopeInterior6Form24,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 0 (by omega),kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row24,mul_pow]

theorem slopeInterior6Form25_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form25
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row25 ((361/25)*v) := by
  simp only [slopeInterior6Form25,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row25,mul_pow]

theorem slopeInterior6Form26_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form26
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row26 ((361/25)*v) := by
  simp only [slopeInterior6Form26,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 1 (by omega),kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row26,mul_pow]

theorem slopeInterior6Form27_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form27
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row27 ((361/25)*v) := by
  simp only [slopeInterior6Form27,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row27,mul_pow]

theorem slopeInterior6Form28_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form28
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row28 ((361/25)*v) := by
  simp only [slopeInterior6Form28,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 2 (by omega),kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row28,mul_pow]

theorem slopeInterior6Form29_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form29
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row29 ((361/25)*v) := by
  simp only [slopeInterior6Form29,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row29,mul_pow]

theorem slopeInterior6Form30_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form30
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row30 ((361/25)*v) := by
  simp only [slopeInterior6Form30,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 3 (by omega),kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row30,mul_pow]

theorem slopeInterior6Form31_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form31
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row31 ((361/25)*v) := by
  simp only [slopeInterior6Form31,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row31,mul_pow]

theorem slopeInterior6Form32_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form32
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row32 ((361/25)*v) := by
  simp only [slopeInterior6Form32,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 4 (by omega),kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row32,mul_pow]

theorem slopeInterior6Form33_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form33
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row33 ((361/25)*v) := by
  simp only [slopeInterior6Form33,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row33,mul_pow]

theorem slopeInterior6Form34_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form34
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row34 ((361/25)*v) := by
  simp only [slopeInterior6Form34,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 5 (by omega),kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row34,mul_pow]

theorem slopeInterior6Form35_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form35
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row35 ((361/25)*v) := by
  simp only [slopeInterior6Form35,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row35,mul_pow]

theorem slopeInterior6Form36_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form36
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row36 ((361/25)*v) := by
  simp only [slopeInterior6Form36,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 6 (by omega),kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row36,mul_pow]

theorem slopeInterior6Form37_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form37
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row37 ((361/25)*v) := by
  simp only [slopeInterior6Form37,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row37,mul_pow]

theorem slopeInterior6Form38_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form38
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row38 ((361/25)*v) := by
  simp only [slopeInterior6Form38,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 7 (by omega),kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row38,mul_pow]

theorem slopeInterior6Form39_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form39
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row39 ((361/25)*v) := by
  simp only [slopeInterior6Form39,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row39,mul_pow]

theorem slopeInterior6Form40_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form40
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row40 ((361/25)*v) := by
  simp only [slopeInterior6Form40,kineticBernstein_add,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 8 (by omega),kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row40,mul_pow]

theorem slopeInterior6Form41_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form41
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row41 ((361/25)*v) := by
  simp only [slopeInterior6Form41,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row41,mul_pow]

theorem slopeInterior6Form42_reconstruction (v : ℝ) :
    kineticBernstein 9 (fun B => slopeInterior6Form42
      (fun b => (361/25)^b*degreeElevationCoefficient 9 b B)) v=
        slopeInterior6Row42 ((361/25)*v) := by
  simp only [slopeInterior6Form42,kineticBernstein_const_mul]
  rw [kineticBernstein_degree 9 9 (by omega)]
  simp only [slopeInterior6Row42,mul_pow]

def slopeInterior6TensorValue (t v : ℝ) : ℝ :=
  kineticBernstein 38 (fun A => kineticBernstein 9 (slopeInterior6TensorCoefficient A) v) t

theorem slopeInterior6TensorValue_reconstruction (t v : ℝ) :
    slopeInterior6TensorValue t v=slopeInterior6Quotient ((4/5)*t) ((361/25)*v) := by
  delta slopeInterior6TensorValue slopeInterior6TensorCoefficient slopeInterior6ClockForm
  simp only [kineticBernstein_add,kineticBernstein_mul_const,kineticBernstein_const_mul,
    slopeInterior6Form4_reconstruction,slopeInterior6Form5_reconstruction,slopeInterior6Form6_reconstruction,slopeInterior6Form7_reconstruction,slopeInterior6Form8_reconstruction,slopeInterior6Form9_reconstruction,slopeInterior6Form10_reconstruction,slopeInterior6Form11_reconstruction,slopeInterior6Form12_reconstruction,slopeInterior6Form13_reconstruction,slopeInterior6Form14_reconstruction,slopeInterior6Form15_reconstruction,slopeInterior6Form16_reconstruction,slopeInterior6Form17_reconstruction,slopeInterior6Form18_reconstruction,slopeInterior6Form19_reconstruction,slopeInterior6Form20_reconstruction,slopeInterior6Form21_reconstruction,slopeInterior6Form22_reconstruction,slopeInterior6Form23_reconstruction,slopeInterior6Form24_reconstruction,slopeInterior6Form25_reconstruction,slopeInterior6Form26_reconstruction,slopeInterior6Form27_reconstruction,slopeInterior6Form28_reconstruction,slopeInterior6Form29_reconstruction,slopeInterior6Form30_reconstruction,slopeInterior6Form31_reconstruction,slopeInterior6Form32_reconstruction,slopeInterior6Form33_reconstruction,slopeInterior6Form34_reconstruction,slopeInterior6Form35_reconstruction,slopeInterior6Form36_reconstruction,slopeInterior6Form37_reconstruction,slopeInterior6Form38_reconstruction,slopeInterior6Form39_reconstruction,slopeInterior6Form40_reconstruction,slopeInterior6Form41_reconstruction,slopeInterior6Form42_reconstruction]
  rw [kineticBernstein_degree 38 (4-4) (by omega),kineticBernstein_degree 38 (5-4) (by omega),kineticBernstein_degree 38 (6-4) (by omega),kineticBernstein_degree 38 (7-4) (by omega),kineticBernstein_degree 38 (8-4) (by omega),kineticBernstein_degree 38 (9-4) (by omega),kineticBernstein_degree 38 (10-4) (by omega),kineticBernstein_degree 38 (11-4) (by omega),kineticBernstein_degree 38 (12-4) (by omega),kineticBernstein_degree 38 (13-4) (by omega),kineticBernstein_degree 38 (14-4) (by omega),kineticBernstein_degree 38 (15-4) (by omega),kineticBernstein_degree 38 (16-4) (by omega),kineticBernstein_degree 38 (17-4) (by omega),kineticBernstein_degree 38 (18-4) (by omega),kineticBernstein_degree 38 (19-4) (by omega),kineticBernstein_degree 38 (20-4) (by omega),kineticBernstein_degree 38 (21-4) (by omega),kineticBernstein_degree 38 (22-4) (by omega),kineticBernstein_degree 38 (23-4) (by omega),kineticBernstein_degree 38 (24-4) (by omega),kineticBernstein_degree 38 (25-4) (by omega),kineticBernstein_degree 38 (26-4) (by omega),kineticBernstein_degree 38 (27-4) (by omega),kineticBernstein_degree 38 (28-4) (by omega),kineticBernstein_degree 38 (29-4) (by omega),kineticBernstein_degree 38 (30-4) (by omega),kineticBernstein_degree 38 (31-4) (by omega),kineticBernstein_degree 38 (32-4) (by omega),kineticBernstein_degree 38 (33-4) (by omega),kineticBernstein_degree 38 (34-4) (by omega),kineticBernstein_degree 38 (35-4) (by omega),kineticBernstein_degree 38 (36-4) (by omega),kineticBernstein_degree 38 (37-4) (by omega),kineticBernstein_degree 38 (38-4) (by omega),kineticBernstein_degree 38 (39-4) (by omega),kineticBernstein_degree 38 (40-4) (by omega),kineticBernstein_degree 38 (41-4) (by omega),kineticBernstein_degree 38 (42-4) (by omega)]
  simp only [slopeInterior6Quotient,mul_pow,mul_assoc,mul_comm]

end
end HTGeometry.ThetaRatioKineticContraction

