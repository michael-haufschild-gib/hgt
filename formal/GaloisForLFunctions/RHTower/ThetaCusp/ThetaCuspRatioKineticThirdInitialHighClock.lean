import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticThirdInitialTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def thirdInitialClockForm34Norm (x : ℕ → ℝ) : {c : ℝ // thirdInitialClockForm 34 x=c} := by
  have he : thirdInitialClockForm 34 x=thirdInitialClockForm 34 x := rfl
  conv at he =>
    rhs
    norm_num [thirdInitialClockForm,
      thirdInitialForm5,thirdInitialForm6,thirdInitialForm7,thirdInitialForm8,thirdInitialForm9,thirdInitialForm10,thirdInitialForm11,thirdInitialForm12,thirdInitialForm13,thirdInitialForm14,thirdInitialForm15,thirdInitialForm16,thirdInitialForm17,thirdInitialForm18,thirdInitialForm19,thirdInitialForm20,thirdInitialForm21,thirdInitialForm22,thirdInitialForm23,thirdInitialForm24,thirdInitialForm25,thirdInitialForm26,thirdInitialForm27,thirdInitialForm28,thirdInitialForm29,thirdInitialForm30,thirdInitialForm31,thirdInitialForm32,thirdInitialForm33,thirdInitialForm34,thirdInitialForm35,thirdInitialForm36,thirdInitialForm37,thirdInitialForm38,thirdInitialForm39,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem thirdInitialTensorCoefficient_34_0_neg :
    thirdInitialTensorCoefficient 34 0 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_1_neg :
    thirdInitialTensorCoefficient 34 1 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_2_neg :
    thirdInitialTensorCoefficient 34 2 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_3_neg :
    thirdInitialTensorCoefficient 34 3 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_4_neg :
    thirdInitialTensorCoefficient 34 4 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_5_neg :
    thirdInitialTensorCoefficient 34 5 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_6_neg :
    thirdInitialTensorCoefficient 34 6 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_7_neg :
    thirdInitialTensorCoefficient 34 7 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem thirdInitialTensorCoefficient_34_8_neg :
    thirdInitialTensorCoefficient 34 8 < 0 := by
  rw [thirdInitialTensorCoefficient,(thirdInitialClockForm34Norm _).property]
  norm_num [thirdInitialClockForm34Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

