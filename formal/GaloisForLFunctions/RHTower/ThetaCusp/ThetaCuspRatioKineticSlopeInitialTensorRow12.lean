import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInitialClockForm12Norm (x : ℕ → ℝ) : {c : ℝ // slopeInitialClockForm 12 x=c} := by
  have he : slopeInitialClockForm 12 x=slopeInitialClockForm 12 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInitialClockForm,
      slopeInitialForm5,slopeInitialForm6,slopeInitialForm7,slopeInitialForm8,slopeInitialForm9,slopeInitialForm10,slopeInitialForm11,slopeInitialForm12,slopeInitialForm13,slopeInitialForm14,slopeInitialForm15,slopeInitialForm16,slopeInitialForm17,slopeInitialForm18,slopeInitialForm19,slopeInitialForm20,slopeInitialForm21,slopeInitialForm22,slopeInitialForm23,slopeInitialForm24,slopeInitialForm25,slopeInitialForm26,slopeInitialForm27,slopeInitialForm28,slopeInitialForm29,slopeInitialForm30,slopeInitialForm31,slopeInitialForm32,slopeInitialForm33,slopeInitialForm34,slopeInitialForm35,slopeInitialForm36,slopeInitialForm37,slopeInitialForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInitialTensorCoefficient_12_0_pos :
    0 < slopeInitialTensorCoefficient 12 0 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_1_pos :
    0 < slopeInitialTensorCoefficient 12 1 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_2_pos :
    0 < slopeInitialTensorCoefficient 12 2 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_3_pos :
    0 < slopeInitialTensorCoefficient 12 3 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_4_pos :
    0 < slopeInitialTensorCoefficient 12 4 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_5_pos :
    0 < slopeInitialTensorCoefficient 12 5 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_6_pos :
    0 < slopeInitialTensorCoefficient 12 6 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_7_pos :
    0 < slopeInitialTensorCoefficient 12 7 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_8_pos :
    0 < slopeInitialTensorCoefficient 12 8 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_12_9_pos :
    0 < slopeInitialTensorCoefficient 12 9 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm12Norm _).property]
  norm_num [slopeInitialClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

