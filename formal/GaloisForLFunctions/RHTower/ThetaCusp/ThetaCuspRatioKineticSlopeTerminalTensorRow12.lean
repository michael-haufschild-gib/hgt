import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalClockForm12Norm (x : ℕ → ℝ) : {c : ℝ // slopeTerminalClockForm 12 x=c} := by
  have he : slopeTerminalClockForm 12 x=slopeTerminalClockForm 12 x := rfl
  conv at he =>
    rhs
    norm_num [slopeTerminalClockForm,
      slopeTerminalForm4,slopeTerminalForm5,slopeTerminalForm6,slopeTerminalForm7,slopeTerminalForm8,slopeTerminalForm9,slopeTerminalForm10,slopeTerminalForm11,slopeTerminalForm12,slopeTerminalForm13,slopeTerminalForm14,slopeTerminalForm15,slopeTerminalForm16,slopeTerminalForm17,slopeTerminalForm18,slopeTerminalForm19,slopeTerminalForm20,slopeTerminalForm21,slopeTerminalForm22,slopeTerminalForm23,slopeTerminalForm24,slopeTerminalForm25,slopeTerminalForm26,slopeTerminalForm27,slopeTerminalForm28,slopeTerminalForm29,slopeTerminalForm30,slopeTerminalForm31,slopeTerminalForm32,slopeTerminalForm33,slopeTerminalForm34,slopeTerminalForm35,slopeTerminalForm36,slopeTerminalForm37,slopeTerminalForm38,slopeTerminalForm39,slopeTerminalForm40,slopeTerminalForm41,slopeTerminalForm42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeTerminalTensorCoefficient_12_0_pos :
    0 < slopeTerminalTensorCoefficient 12 0 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_1_pos :
    0 < slopeTerminalTensorCoefficient 12 1 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_2_pos :
    0 < slopeTerminalTensorCoefficient 12 2 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_3_pos :
    0 < slopeTerminalTensorCoefficient 12 3 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_4_pos :
    0 < slopeTerminalTensorCoefficient 12 4 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_5_pos :
    0 < slopeTerminalTensorCoefficient 12 5 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_6_pos :
    0 < slopeTerminalTensorCoefficient 12 6 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_7_pos :
    0 < slopeTerminalTensorCoefficient 12 7 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_8_pos :
    0 < slopeTerminalTensorCoefficient 12 8 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_12_9_pos :
    0 < slopeTerminalTensorCoefficient 12 9 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm12Norm _).property]
  norm_num [slopeTerminalClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

