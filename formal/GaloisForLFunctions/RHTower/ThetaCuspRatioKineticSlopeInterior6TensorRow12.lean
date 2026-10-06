import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior6TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior6ClockForm12Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior6ClockForm 12 x=c} := by
  have he : slopeInterior6ClockForm 12 x=slopeInterior6ClockForm 12 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior6ClockForm,
      slopeInterior6Form4,slopeInterior6Form5,slopeInterior6Form6,slopeInterior6Form7,slopeInterior6Form8,slopeInterior6Form9,slopeInterior6Form10,slopeInterior6Form11,slopeInterior6Form12,slopeInterior6Form13,slopeInterior6Form14,slopeInterior6Form15,slopeInterior6Form16,slopeInterior6Form17,slopeInterior6Form18,slopeInterior6Form19,slopeInterior6Form20,slopeInterior6Form21,slopeInterior6Form22,slopeInterior6Form23,slopeInterior6Form24,slopeInterior6Form25,slopeInterior6Form26,slopeInterior6Form27,slopeInterior6Form28,slopeInterior6Form29,slopeInterior6Form30,slopeInterior6Form31,slopeInterior6Form32,slopeInterior6Form33,slopeInterior6Form34,slopeInterior6Form35,slopeInterior6Form36,slopeInterior6Form37,slopeInterior6Form38,slopeInterior6Form39,slopeInterior6Form40,slopeInterior6Form41,slopeInterior6Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior6TensorCoefficient_12_0_pos :
    0 < slopeInterior6TensorCoefficient 12 0 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_1_pos :
    0 < slopeInterior6TensorCoefficient 12 1 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_2_pos :
    0 < slopeInterior6TensorCoefficient 12 2 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_3_pos :
    0 < slopeInterior6TensorCoefficient 12 3 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_4_pos :
    0 < slopeInterior6TensorCoefficient 12 4 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_5_pos :
    0 < slopeInterior6TensorCoefficient 12 5 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_6_pos :
    0 < slopeInterior6TensorCoefficient 12 6 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_7_pos :
    0 < slopeInterior6TensorCoefficient 12 7 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_8_pos :
    0 < slopeInterior6TensorCoefficient 12 8 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior6TensorCoefficient_12_9_pos :
    0 < slopeInterior6TensorCoefficient 12 9 := by
  rw [slopeInterior6TensorCoefficient,(slopeInterior6ClockForm12Norm _).property]
  norm_num [slopeInterior6ClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

