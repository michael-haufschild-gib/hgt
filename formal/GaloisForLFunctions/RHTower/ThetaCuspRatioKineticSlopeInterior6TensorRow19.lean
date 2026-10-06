import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior6TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior6ClockForm19Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior6ClockForm 19 x=c} := by
  have he : slopeInterior6ClockForm 19 x=slopeInterior6ClockForm 19 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior6ClockForm,
      slopeInterior6Form4,slopeInterior6Form5,slopeInterior6Form6,slopeInterior6Form7,slopeInterior6Form8,slopeInterior6Form9,slopeInterior6Form10,slopeInterior6Form11,slopeInterior6Form12,slopeInterior6Form13,slopeInterior6Form14,slopeInterior6Form15,slopeInterior6Form16,slopeInterior6Form17,slopeInterior6Form18,slopeInterior6Form19,slopeInterior6Form20,slopeInterior6Form21,slopeInterior6Form22,slopeInterior6Form23,slopeInterior6Form24,slopeInterior6Form25,slopeInterior6Form26,slopeInterior6Form27,slopeInterior6Form28,slopeInterior6Form29,slopeInterior6Form30,slopeInterior6Form31,slopeInterior6Form32,slopeInterior6Form33,slopeInterior6Form34,slopeInterior6Form35,slopeInterior6Form36,slopeInterior6Form37,slopeInterior6Form38,slopeInterior6Form39,slopeInterior6Form40,slopeInterior6Form41,slopeInterior6Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior6TensorCoefficient_19_0_pos :
    0 < slopeInterior6TensorCoefficient 19 0 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_1_pos :
    0 < slopeInterior6TensorCoefficient 19 1 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_2_pos :
    0 < slopeInterior6TensorCoefficient 19 2 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_3_pos :
    0 < slopeInterior6TensorCoefficient 19 3 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_4_pos :
    0 < slopeInterior6TensorCoefficient 19 4 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_5_pos :
    0 < slopeInterior6TensorCoefficient 19 5 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_6_pos :
    0 < slopeInterior6TensorCoefficient 19 6 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_7_pos :
    0 < slopeInterior6TensorCoefficient 19 7 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_8_pos :
    0 < slopeInterior6TensorCoefficient 19 8 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_19_9_pos :
    0 < slopeInterior6TensorCoefficient 19 9 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm19Norm _).property]
  norm_num [slopeInterior6ClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

