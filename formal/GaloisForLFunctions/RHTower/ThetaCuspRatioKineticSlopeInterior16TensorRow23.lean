import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior16TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior16ClockForm23Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior16ClockForm 23 x=c} := by
  have he : slopeInterior16ClockForm 23 x=slopeInterior16ClockForm 23 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior16ClockForm,
      slopeInterior16Form4,slopeInterior16Form5,slopeInterior16Form6,slopeInterior16Form7,slopeInterior16Form8,slopeInterior16Form9,slopeInterior16Form10,slopeInterior16Form11,slopeInterior16Form12,slopeInterior16Form13,slopeInterior16Form14,slopeInterior16Form15,slopeInterior16Form16,slopeInterior16Form17,slopeInterior16Form18,slopeInterior16Form19,slopeInterior16Form20,slopeInterior16Form21,slopeInterior16Form22,slopeInterior16Form23,slopeInterior16Form24,slopeInterior16Form25,slopeInterior16Form26,slopeInterior16Form27,slopeInterior16Form28,slopeInterior16Form29,slopeInterior16Form30,slopeInterior16Form31,slopeInterior16Form32,slopeInterior16Form33,slopeInterior16Form34,slopeInterior16Form35,slopeInterior16Form36,slopeInterior16Form37,slopeInterior16Form38,slopeInterior16Form39,slopeInterior16Form40,slopeInterior16Form41,slopeInterior16Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior16TensorCoefficient_23_0_pos :
    0 < slopeInterior16TensorCoefficient 23 0 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_1_pos :
    0 < slopeInterior16TensorCoefficient 23 1 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_2_pos :
    0 < slopeInterior16TensorCoefficient 23 2 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_3_pos :
    0 < slopeInterior16TensorCoefficient 23 3 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_4_pos :
    0 < slopeInterior16TensorCoefficient 23 4 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_5_pos :
    0 < slopeInterior16TensorCoefficient 23 5 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_6_pos :
    0 < slopeInterior16TensorCoefficient 23 6 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_7_pos :
    0 < slopeInterior16TensorCoefficient 23 7 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_8_pos :
    0 < slopeInterior16TensorCoefficient 23 8 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_23_9_pos :
    0 < slopeInterior16TensorCoefficient 23 9 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm23Norm _).property]
  norm_num [slopeInterior16ClockForm23Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

