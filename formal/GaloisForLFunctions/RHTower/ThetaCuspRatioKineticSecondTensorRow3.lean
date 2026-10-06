import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm3Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 3 x=c} := by
  have he : secondControlDefectClockForm 3 x=secondControlDefectClockForm 3 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_3_0_pos :
    0<secondControlDefectTensorCoefficient 3 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_1_pos :
    0<secondControlDefectTensorCoefficient 3 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_2_pos :
    0<secondControlDefectTensorCoefficient 3 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_3_pos :
    0<secondControlDefectTensorCoefficient 3 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_4_pos :
    0<secondControlDefectTensorCoefficient 3 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_5_pos :
    0<secondControlDefectTensorCoefficient 3 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_6_pos :
    0<secondControlDefectTensorCoefficient 3 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_7_pos :
    0<secondControlDefectTensorCoefficient 3 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_8_pos :
    0<secondControlDefectTensorCoefficient 3 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_3_9_pos :
    0<secondControlDefectTensorCoefficient 3 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm3Norm _).property]
  norm_num [secondControlDefectClockForm3Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
