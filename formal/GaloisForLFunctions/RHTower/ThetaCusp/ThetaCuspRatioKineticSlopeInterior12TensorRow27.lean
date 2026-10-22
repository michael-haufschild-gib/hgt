import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior12TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior12ClockForm27Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior12ClockForm 27 x=c} := by
  have he : slopeInterior12ClockForm 27 x=slopeInterior12ClockForm 27 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior12ClockForm,
      slopeInterior12Form4,slopeInterior12Form5,slopeInterior12Form6,slopeInterior12Form7,slopeInterior12Form8,slopeInterior12Form9,slopeInterior12Form10,slopeInterior12Form11,slopeInterior12Form12,slopeInterior12Form13,slopeInterior12Form14,slopeInterior12Form15,slopeInterior12Form16,slopeInterior12Form17,slopeInterior12Form18,slopeInterior12Form19,slopeInterior12Form20,slopeInterior12Form21,slopeInterior12Form22,slopeInterior12Form23,slopeInterior12Form24,slopeInterior12Form25,slopeInterior12Form26,slopeInterior12Form27,slopeInterior12Form28,slopeInterior12Form29,slopeInterior12Form30,slopeInterior12Form31,slopeInterior12Form32,slopeInterior12Form33,slopeInterior12Form34,slopeInterior12Form35,slopeInterior12Form36,slopeInterior12Form37,slopeInterior12Form38,slopeInterior12Form39,slopeInterior12Form40,slopeInterior12Form41,slopeInterior12Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior12TensorCoefficient_27_0_pos :
    0 < slopeInterior12TensorCoefficient 27 0 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_1_pos :
    0 < slopeInterior12TensorCoefficient 27 1 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_2_pos :
    0 < slopeInterior12TensorCoefficient 27 2 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_3_pos :
    0 < slopeInterior12TensorCoefficient 27 3 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_4_pos :
    0 < slopeInterior12TensorCoefficient 27 4 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_5_pos :
    0 < slopeInterior12TensorCoefficient 27 5 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_6_pos :
    0 < slopeInterior12TensorCoefficient 27 6 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_7_pos :
    0 < slopeInterior12TensorCoefficient 27 7 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_8_pos :
    0 < slopeInterior12TensorCoefficient 27 8 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior12TensorCoefficient_27_9_pos :
    0 < slopeInterior12TensorCoefficient 27 9 := by
  rw [slopeInterior12TensorCoefficient,(slopeInterior12ClockForm27Norm _).property]
  norm_num [slopeInterior12ClockForm27Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

