import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInitialClockForm7Norm (x : ℕ → ℝ) : {c : ℝ // slopeInitialClockForm 7 x=c} := by
  have he : slopeInitialClockForm 7 x=slopeInitialClockForm 7 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInitialClockForm,
      slopeInitialForm5,slopeInitialForm6,slopeInitialForm7,slopeInitialForm8,slopeInitialForm9,slopeInitialForm10,slopeInitialForm11,slopeInitialForm12,slopeInitialForm13,slopeInitialForm14,slopeInitialForm15,slopeInitialForm16,slopeInitialForm17,slopeInitialForm18,slopeInitialForm19,slopeInitialForm20,slopeInitialForm21,slopeInitialForm22,slopeInitialForm23,slopeInitialForm24,slopeInitialForm25,slopeInitialForm26,slopeInitialForm27,slopeInitialForm28,slopeInitialForm29,slopeInitialForm30,slopeInitialForm31,slopeInitialForm32,slopeInitialForm33,slopeInitialForm34,slopeInitialForm35,slopeInitialForm36,slopeInitialForm37,slopeInitialForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInitialTensorCoefficient_7_0_pos :
    0 < slopeInitialTensorCoefficient 7 0 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_1_pos :
    0 < slopeInitialTensorCoefficient 7 1 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_2_pos :
    0 < slopeInitialTensorCoefficient 7 2 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_3_pos :
    0 < slopeInitialTensorCoefficient 7 3 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_4_pos :
    0 < slopeInitialTensorCoefficient 7 4 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_5_pos :
    0 < slopeInitialTensorCoefficient 7 5 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_6_pos :
    0 < slopeInitialTensorCoefficient 7 6 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_7_pos :
    0 < slopeInitialTensorCoefficient 7 7 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_8_pos :
    0 < slopeInitialTensorCoefficient 7 8 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_7_9_pos :
    0 < slopeInitialTensorCoefficient 7 9 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm7Norm _).property]
  norm_num [slopeInitialClockForm7Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

