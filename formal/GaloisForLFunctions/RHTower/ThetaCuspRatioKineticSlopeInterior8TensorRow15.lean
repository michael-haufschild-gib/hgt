import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior8TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior8ClockForm15Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior8ClockForm 15 x=c} := by
  have he : slopeInterior8ClockForm 15 x=slopeInterior8ClockForm 15 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior8ClockForm,
      slopeInterior8Form4,slopeInterior8Form5,slopeInterior8Form6,slopeInterior8Form7,slopeInterior8Form8,slopeInterior8Form9,slopeInterior8Form10,slopeInterior8Form11,slopeInterior8Form12,slopeInterior8Form13,slopeInterior8Form14,slopeInterior8Form15,slopeInterior8Form16,slopeInterior8Form17,slopeInterior8Form18,slopeInterior8Form19,slopeInterior8Form20,slopeInterior8Form21,slopeInterior8Form22,slopeInterior8Form23,slopeInterior8Form24,slopeInterior8Form25,slopeInterior8Form26,slopeInterior8Form27,slopeInterior8Form28,slopeInterior8Form29,slopeInterior8Form30,slopeInterior8Form31,slopeInterior8Form32,slopeInterior8Form33,slopeInterior8Form34,slopeInterior8Form35,slopeInterior8Form36,slopeInterior8Form37,slopeInterior8Form38,slopeInterior8Form39,slopeInterior8Form40,slopeInterior8Form41,slopeInterior8Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior8TensorCoefficient_15_0_pos :
    0 < slopeInterior8TensorCoefficient 15 0 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_1_pos :
    0 < slopeInterior8TensorCoefficient 15 1 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_2_pos :
    0 < slopeInterior8TensorCoefficient 15 2 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_3_pos :
    0 < slopeInterior8TensorCoefficient 15 3 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_4_pos :
    0 < slopeInterior8TensorCoefficient 15 4 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_5_pos :
    0 < slopeInterior8TensorCoefficient 15 5 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_6_pos :
    0 < slopeInterior8TensorCoefficient 15 6 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_7_pos :
    0 < slopeInterior8TensorCoefficient 15 7 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_8_pos :
    0 < slopeInterior8TensorCoefficient 15 8 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior8TensorCoefficient_15_9_pos :
    0 < slopeInterior8TensorCoefficient 15 9 := by
  rw [slopeInterior8TensorCoefficient,(slopeInterior8ClockForm15Norm _).property]
  norm_num [slopeInterior8ClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

