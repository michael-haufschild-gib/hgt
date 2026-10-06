import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior12TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior12ClockForm25Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior12ClockForm 25 x=c} := by
  have he : slopeInterior12ClockForm 25 x=slopeInterior12ClockForm 25 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior12ClockForm,
      slopeInterior12Form4,slopeInterior12Form5,slopeInterior12Form6,slopeInterior12Form7,slopeInterior12Form8,slopeInterior12Form9,slopeInterior12Form10,slopeInterior12Form11,slopeInterior12Form12,slopeInterior12Form13,slopeInterior12Form14,slopeInterior12Form15,slopeInterior12Form16,slopeInterior12Form17,slopeInterior12Form18,slopeInterior12Form19,slopeInterior12Form20,slopeInterior12Form21,slopeInterior12Form22,slopeInterior12Form23,slopeInterior12Form24,slopeInterior12Form25,slopeInterior12Form26,slopeInterior12Form27,slopeInterior12Form28,slopeInterior12Form29,slopeInterior12Form30,slopeInterior12Form31,slopeInterior12Form32,slopeInterior12Form33,slopeInterior12Form34,slopeInterior12Form35,slopeInterior12Form36,slopeInterior12Form37,slopeInterior12Form38,slopeInterior12Form39,slopeInterior12Form40,slopeInterior12Form41,slopeInterior12Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior12TensorCoefficient_25_0_pos :
    0 < slopeInterior12TensorCoefficient 25 0 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_1_pos :
    0 < slopeInterior12TensorCoefficient 25 1 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_2_pos :
    0 < slopeInterior12TensorCoefficient 25 2 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_3_pos :
    0 < slopeInterior12TensorCoefficient 25 3 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_4_pos :
    0 < slopeInterior12TensorCoefficient 25 4 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_5_pos :
    0 < slopeInterior12TensorCoefficient 25 5 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_6_pos :
    0 < slopeInterior12TensorCoefficient 25 6 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_7_pos :
    0 < slopeInterior12TensorCoefficient 25 7 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_8_pos :
    0 < slopeInterior12TensorCoefficient 25 8 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_25_9_pos :
    0 < slopeInterior12TensorCoefficient 25 9 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm25Norm _).property]
  norm_num [slopeInterior12ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

