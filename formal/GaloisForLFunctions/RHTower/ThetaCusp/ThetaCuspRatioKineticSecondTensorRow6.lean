import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm6Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 6 x=c} := by
  have he : secondControlDefectClockForm 6 x=secondControlDefectClockForm 6 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_6_0_pos :
    0<secondControlDefectTensorCoefficient 6 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_1_pos :
    0<secondControlDefectTensorCoefficient 6 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_2_pos :
    0<secondControlDefectTensorCoefficient 6 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_3_pos :
    0<secondControlDefectTensorCoefficient 6 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_4_pos :
    0<secondControlDefectTensorCoefficient 6 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_5_pos :
    0<secondControlDefectTensorCoefficient 6 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_6_pos :
    0<secondControlDefectTensorCoefficient 6 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_7_pos :
    0<secondControlDefectTensorCoefficient 6 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_8_pos :
    0<secondControlDefectTensorCoefficient 6 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_6_9_pos :
    0<secondControlDefectTensorCoefficient 6 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm6Norm _).property]
  norm_num [secondControlDefectClockForm6Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
