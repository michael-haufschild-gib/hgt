import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior10TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior10ClockForm14Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior10ClockForm 14 x=c} := by
  have he : slopeInterior10ClockForm 14 x=slopeInterior10ClockForm 14 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior10ClockForm,
      slopeInterior10Form4,slopeInterior10Form5,slopeInterior10Form6,slopeInterior10Form7,slopeInterior10Form8,slopeInterior10Form9,slopeInterior10Form10,slopeInterior10Form11,slopeInterior10Form12,slopeInterior10Form13,slopeInterior10Form14,slopeInterior10Form15,slopeInterior10Form16,slopeInterior10Form17,slopeInterior10Form18,slopeInterior10Form19,slopeInterior10Form20,slopeInterior10Form21,slopeInterior10Form22,slopeInterior10Form23,slopeInterior10Form24,slopeInterior10Form25,slopeInterior10Form26,slopeInterior10Form27,slopeInterior10Form28,slopeInterior10Form29,slopeInterior10Form30,slopeInterior10Form31,slopeInterior10Form32,slopeInterior10Form33,slopeInterior10Form34,slopeInterior10Form35,slopeInterior10Form36,slopeInterior10Form37,slopeInterior10Form38,slopeInterior10Form39,slopeInterior10Form40,slopeInterior10Form41,slopeInterior10Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior10TensorCoefficient_14_0_pos :
    0 < slopeInterior10TensorCoefficient 14 0 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_1_pos :
    0 < slopeInterior10TensorCoefficient 14 1 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_2_pos :
    0 < slopeInterior10TensorCoefficient 14 2 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_3_pos :
    0 < slopeInterior10TensorCoefficient 14 3 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_4_pos :
    0 < slopeInterior10TensorCoefficient 14 4 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_5_pos :
    0 < slopeInterior10TensorCoefficient 14 5 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_6_pos :
    0 < slopeInterior10TensorCoefficient 14 6 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_7_pos :
    0 < slopeInterior10TensorCoefficient 14 7 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_8_pos :
    0 < slopeInterior10TensorCoefficient 14 8 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_14_9_pos :
    0 < slopeInterior10TensorCoefficient 14 9 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm14Norm _).property]
  norm_num [slopeInterior10ClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

