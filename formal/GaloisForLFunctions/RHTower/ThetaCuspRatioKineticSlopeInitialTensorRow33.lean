import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInitialClockForm33Norm (x : ℕ → ℝ) : {c : ℝ // slopeInitialClockForm 33 x=c} := by
  have he : slopeInitialClockForm 33 x=slopeInitialClockForm 33 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInitialClockForm,
      slopeInitialForm5,slopeInitialForm6,slopeInitialForm7,slopeInitialForm8,slopeInitialForm9,slopeInitialForm10,slopeInitialForm11,slopeInitialForm12,slopeInitialForm13,slopeInitialForm14,slopeInitialForm15,slopeInitialForm16,slopeInitialForm17,slopeInitialForm18,slopeInitialForm19,slopeInitialForm20,slopeInitialForm21,slopeInitialForm22,slopeInitialForm23,slopeInitialForm24,slopeInitialForm25,slopeInitialForm26,slopeInitialForm27,slopeInitialForm28,slopeInitialForm29,slopeInitialForm30,slopeInitialForm31,slopeInitialForm32,slopeInitialForm33,slopeInitialForm34,slopeInitialForm35,slopeInitialForm36,slopeInitialForm37,slopeInitialForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInitialTensorCoefficient_33_0_pos :
    0 < slopeInitialTensorCoefficient 33 0 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_1_pos :
    0 < slopeInitialTensorCoefficient 33 1 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_2_pos :
    0 < slopeInitialTensorCoefficient 33 2 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_3_pos :
    0 < slopeInitialTensorCoefficient 33 3 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_4_pos :
    0 < slopeInitialTensorCoefficient 33 4 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_5_pos :
    0 < slopeInitialTensorCoefficient 33 5 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_6_pos :
    0 < slopeInitialTensorCoefficient 33 6 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_7_pos :
    0 < slopeInitialTensorCoefficient 33 7 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_8_pos :
    0 < slopeInitialTensorCoefficient 33 8 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInitialTensorCoefficient_33_9_pos :
    0 < slopeInitialTensorCoefficient 33 9 := by
  rw [slopeInitialTensorCoefficient,(slopeInitialClockForm33Norm _).property]
  norm_num [slopeInitialClockForm33Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

