import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInitialClockForm18Norm (x : ℕ → ℝ) : {c : ℝ // slopeInitialClockForm 18 x=c} := by
  have he : slopeInitialClockForm 18 x=slopeInitialClockForm 18 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInitialClockForm,
      slopeInitialForm5,slopeInitialForm6,slopeInitialForm7,slopeInitialForm8,slopeInitialForm9,slopeInitialForm10,slopeInitialForm11,slopeInitialForm12,slopeInitialForm13,slopeInitialForm14,slopeInitialForm15,slopeInitialForm16,slopeInitialForm17,slopeInitialForm18,slopeInitialForm19,slopeInitialForm20,slopeInitialForm21,slopeInitialForm22,slopeInitialForm23,slopeInitialForm24,slopeInitialForm25,slopeInitialForm26,slopeInitialForm27,slopeInitialForm28,slopeInitialForm29,slopeInitialForm30,slopeInitialForm31,slopeInitialForm32,slopeInitialForm33,slopeInitialForm34,slopeInitialForm35,slopeInitialForm36,slopeInitialForm37,slopeInitialForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInitialTensorCoefficient_18_0_pos :
    0 < slopeInitialTensorCoefficient 18 0 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_1_pos :
    0 < slopeInitialTensorCoefficient 18 1 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_2_pos :
    0 < slopeInitialTensorCoefficient 18 2 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_3_pos :
    0 < slopeInitialTensorCoefficient 18 3 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_4_pos :
    0 < slopeInitialTensorCoefficient 18 4 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_5_pos :
    0 < slopeInitialTensorCoefficient 18 5 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_6_pos :
    0 < slopeInitialTensorCoefficient 18 6 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_7_pos :
    0 < slopeInitialTensorCoefficient 18 7 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_8_pos :
    0 < slopeInitialTensorCoefficient 18 8 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_18_9_pos :
    0 < slopeInitialTensorCoefficient 18 9 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm18Norm _).property]
  norm_num [slopeInitialClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

