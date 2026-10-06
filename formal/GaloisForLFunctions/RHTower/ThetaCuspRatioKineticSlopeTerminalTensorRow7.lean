import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeTerminalTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalClockForm7Norm (x : ℕ → ℝ) : {c : ℝ // slopeTerminalClockForm 7 x=c} := by
  have he : slopeTerminalClockForm 7 x=slopeTerminalClockForm 7 x := rfl
  conv at he =>
    rhs
    norm_num [slopeTerminalClockForm,
      slopeTerminalForm4,slopeTerminalForm5,slopeTerminalForm6,slopeTerminalForm7,slopeTerminalForm8,slopeTerminalForm9,slopeTerminalForm10,slopeTerminalForm11,slopeTerminalForm12,slopeTerminalForm13,slopeTerminalForm14,slopeTerminalForm15,slopeTerminalForm16,slopeTerminalForm17,slopeTerminalForm18,slopeTerminalForm19,slopeTerminalForm20,slopeTerminalForm21,slopeTerminalForm22,slopeTerminalForm23,slopeTerminalForm24,slopeTerminalForm25,slopeTerminalForm26,slopeTerminalForm27,slopeTerminalForm28,slopeTerminalForm29,slopeTerminalForm30,slopeTerminalForm31,slopeTerminalForm32,slopeTerminalForm33,slopeTerminalForm34,slopeTerminalForm35,slopeTerminalForm36,slopeTerminalForm37,slopeTerminalForm38,slopeTerminalForm39,slopeTerminalForm40,slopeTerminalForm41,slopeTerminalForm42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeTerminalTensorCoefficient_7_0_pos :
    0 < slopeTerminalTensorCoefficient 7 0 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_1_pos :
    0 < slopeTerminalTensorCoefficient 7 1 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_2_pos :
    0 < slopeTerminalTensorCoefficient 7 2 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_3_pos :
    0 < slopeTerminalTensorCoefficient 7 3 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_4_pos :
    0 < slopeTerminalTensorCoefficient 7 4 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_5_pos :
    0 < slopeTerminalTensorCoefficient 7 5 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_6_pos :
    0 < slopeTerminalTensorCoefficient 7 6 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_7_pos :
    0 < slopeTerminalTensorCoefficient 7 7 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_8_pos :
    0 < slopeTerminalTensorCoefficient 7 8 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_7_9_pos :
    0 < slopeTerminalTensorCoefficient 7 9 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm7Norm _).property]
  norm_num [slopeTerminalClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

