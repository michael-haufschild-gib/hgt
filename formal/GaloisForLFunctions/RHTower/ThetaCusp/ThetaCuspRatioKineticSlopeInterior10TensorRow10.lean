import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior10TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior10ClockForm10Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior10ClockForm 10 x=c} := by
  have he : slopeInterior10ClockForm 10 x=slopeInterior10ClockForm 10 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior10ClockForm,
      slopeInterior10Form4,slopeInterior10Form5,slopeInterior10Form6,slopeInterior10Form7,slopeInterior10Form8,slopeInterior10Form9,slopeInterior10Form10,slopeInterior10Form11,slopeInterior10Form12,slopeInterior10Form13,slopeInterior10Form14,slopeInterior10Form15,slopeInterior10Form16,slopeInterior10Form17,slopeInterior10Form18,slopeInterior10Form19,slopeInterior10Form20,slopeInterior10Form21,slopeInterior10Form22,slopeInterior10Form23,slopeInterior10Form24,slopeInterior10Form25,slopeInterior10Form26,slopeInterior10Form27,slopeInterior10Form28,slopeInterior10Form29,slopeInterior10Form30,slopeInterior10Form31,slopeInterior10Form32,slopeInterior10Form33,slopeInterior10Form34,slopeInterior10Form35,slopeInterior10Form36,slopeInterior10Form37,slopeInterior10Form38,slopeInterior10Form39,slopeInterior10Form40,slopeInterior10Form41,slopeInterior10Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior10TensorCoefficient_10_0_pos :
    0 < slopeInterior10TensorCoefficient 10 0 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_1_pos :
    0 < slopeInterior10TensorCoefficient 10 1 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_2_pos :
    0 < slopeInterior10TensorCoefficient 10 2 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_3_pos :
    0 < slopeInterior10TensorCoefficient 10 3 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_4_pos :
    0 < slopeInterior10TensorCoefficient 10 4 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_5_pos :
    0 < slopeInterior10TensorCoefficient 10 5 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_6_pos :
    0 < slopeInterior10TensorCoefficient 10 6 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_7_pos :
    0 < slopeInterior10TensorCoefficient 10 7 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_8_pos :
    0 < slopeInterior10TensorCoefficient 10 8 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior10TensorCoefficient_10_9_pos :
    0 < slopeInterior10TensorCoefficient 10 9 := by
  rw [slopeInterior10TensorCoefficient,(slopeInterior10ClockForm10Norm _).property]
  norm_num [slopeInterior10ClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

