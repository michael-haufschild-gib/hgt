import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeTerminalTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalClockForm32Norm (x : ℕ → ℝ) : {c : ℝ // slopeTerminalClockForm 32 x=c} := by
  have he : slopeTerminalClockForm 32 x=slopeTerminalClockForm 32 x := rfl
  conv at he =>
    rhs
    norm_num [slopeTerminalClockForm,
      slopeTerminalForm4,slopeTerminalForm5,slopeTerminalForm6,slopeTerminalForm7,slopeTerminalForm8,slopeTerminalForm9,slopeTerminalForm10,slopeTerminalForm11,slopeTerminalForm12,slopeTerminalForm13,slopeTerminalForm14,slopeTerminalForm15,slopeTerminalForm16,slopeTerminalForm17,slopeTerminalForm18,slopeTerminalForm19,slopeTerminalForm20,slopeTerminalForm21,slopeTerminalForm22,slopeTerminalForm23,slopeTerminalForm24,slopeTerminalForm25,slopeTerminalForm26,slopeTerminalForm27,slopeTerminalForm28,slopeTerminalForm29,slopeTerminalForm30,slopeTerminalForm31,slopeTerminalForm32,slopeTerminalForm33,slopeTerminalForm34,slopeTerminalForm35,slopeTerminalForm36,slopeTerminalForm37,slopeTerminalForm38,slopeTerminalForm39,slopeTerminalForm40,slopeTerminalForm41,slopeTerminalForm42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeTerminalTensorCoefficient_32_0_pos :
    0 < slopeTerminalTensorCoefficient 32 0 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_1_pos :
    0 < slopeTerminalTensorCoefficient 32 1 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_2_pos :
    0 < slopeTerminalTensorCoefficient 32 2 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_3_pos :
    0 < slopeTerminalTensorCoefficient 32 3 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_4_pos :
    0 < slopeTerminalTensorCoefficient 32 4 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_5_pos :
    0 < slopeTerminalTensorCoefficient 32 5 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_6_pos :
    0 < slopeTerminalTensorCoefficient 32 6 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_7_pos :
    0 < slopeTerminalTensorCoefficient 32 7 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_8_pos :
    0 < slopeTerminalTensorCoefficient 32 8 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_32_9_pos :
    0 < slopeTerminalTensorCoefficient 32 9 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm32Norm _).property]
  norm_num [slopeTerminalClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

