import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeTerminalClockForm38Norm (x : ℕ → ℝ) : {c : ℝ // slopeTerminalClockForm 38 x=c} := by
  have he : slopeTerminalClockForm 38 x=slopeTerminalClockForm 38 x := rfl
  conv at he =>
    rhs
    norm_num [slopeTerminalClockForm,
      slopeTerminalForm4,slopeTerminalForm5,slopeTerminalForm6,slopeTerminalForm7,slopeTerminalForm8,slopeTerminalForm9,slopeTerminalForm10,slopeTerminalForm11,slopeTerminalForm12,slopeTerminalForm13,slopeTerminalForm14,slopeTerminalForm15,slopeTerminalForm16,slopeTerminalForm17,slopeTerminalForm18,slopeTerminalForm19,slopeTerminalForm20,slopeTerminalForm21,slopeTerminalForm22,slopeTerminalForm23,slopeTerminalForm24,slopeTerminalForm25,slopeTerminalForm26,slopeTerminalForm27,slopeTerminalForm28,slopeTerminalForm29,slopeTerminalForm30,slopeTerminalForm31,slopeTerminalForm32,slopeTerminalForm33,slopeTerminalForm34,slopeTerminalForm35,slopeTerminalForm36,slopeTerminalForm37,slopeTerminalForm38,slopeTerminalForm39,slopeTerminalForm40,slopeTerminalForm41,slopeTerminalForm42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeTerminalTensorCoefficient_38_0_pos :
    0 < slopeTerminalTensorCoefficient 38 0 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_1_pos :
    0 < slopeTerminalTensorCoefficient 38 1 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_2_pos :
    0 < slopeTerminalTensorCoefficient 38 2 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_3_pos :
    0 < slopeTerminalTensorCoefficient 38 3 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_4_pos :
    0 < slopeTerminalTensorCoefficient 38 4 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_5_pos :
    0 < slopeTerminalTensorCoefficient 38 5 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_6_pos :
    0 < slopeTerminalTensorCoefficient 38 6 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_7_pos :
    0 < slopeTerminalTensorCoefficient 38 7 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_8_pos :
    0 < slopeTerminalTensorCoefficient 38 8 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeTerminalTensorCoefficient_38_9_pos :
    0 < slopeTerminalTensorCoefficient 38 9 := by
  rw [slopeTerminalTensorCoefficient,(slopeTerminalClockForm38Norm _).property]
  norm_num [slopeTerminalClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

