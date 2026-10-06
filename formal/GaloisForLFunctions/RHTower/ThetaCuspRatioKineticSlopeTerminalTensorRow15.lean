import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeTerminalTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalClockForm15Norm (x : ℕ → ℝ) : {c : ℝ // slopeTerminalClockForm 15 x=c} := by
  have he : slopeTerminalClockForm 15 x=slopeTerminalClockForm 15 x := rfl
  conv at he =>
    rhs
    norm_num [slopeTerminalClockForm,
      slopeTerminalForm4,slopeTerminalForm5,slopeTerminalForm6,slopeTerminalForm7,slopeTerminalForm8,slopeTerminalForm9,slopeTerminalForm10,slopeTerminalForm11,slopeTerminalForm12,slopeTerminalForm13,slopeTerminalForm14,slopeTerminalForm15,slopeTerminalForm16,slopeTerminalForm17,slopeTerminalForm18,slopeTerminalForm19,slopeTerminalForm20,slopeTerminalForm21,slopeTerminalForm22,slopeTerminalForm23,slopeTerminalForm24,slopeTerminalForm25,slopeTerminalForm26,slopeTerminalForm27,slopeTerminalForm28,slopeTerminalForm29,slopeTerminalForm30,slopeTerminalForm31,slopeTerminalForm32,slopeTerminalForm33,slopeTerminalForm34,slopeTerminalForm35,slopeTerminalForm36,slopeTerminalForm37,slopeTerminalForm38,slopeTerminalForm39,slopeTerminalForm40,slopeTerminalForm41,slopeTerminalForm42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeTerminalTensorCoefficient_15_0_pos :
    0 < slopeTerminalTensorCoefficient 15 0 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_1_pos :
    0 < slopeTerminalTensorCoefficient 15 1 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_2_pos :
    0 < slopeTerminalTensorCoefficient 15 2 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_3_pos :
    0 < slopeTerminalTensorCoefficient 15 3 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_4_pos :
    0 < slopeTerminalTensorCoefficient 15 4 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_5_pos :
    0 < slopeTerminalTensorCoefficient 15 5 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_6_pos :
    0 < slopeTerminalTensorCoefficient 15 6 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_7_pos :
    0 < slopeTerminalTensorCoefficient 15 7 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_8_pos :
    0 < slopeTerminalTensorCoefficient 15 8 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_15_9_pos :
    0 < slopeTerminalTensorCoefficient 15 9 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm15Norm _).property]
  norm_num [slopeTerminalClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

