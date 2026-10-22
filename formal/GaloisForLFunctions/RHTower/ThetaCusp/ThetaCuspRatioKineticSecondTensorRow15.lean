import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm15Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 15 x=c} := by
  have he : secondControlDefectClockForm 15 x=secondControlDefectClockForm 15 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_15_0_pos :
    0<secondControlDefectTensorCoefficient 15 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_1_pos :
    0<secondControlDefectTensorCoefficient 15 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_2_pos :
    0<secondControlDefectTensorCoefficient 15 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_3_pos :
    0<secondControlDefectTensorCoefficient 15 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_4_pos :
    0<secondControlDefectTensorCoefficient 15 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_5_pos :
    0<secondControlDefectTensorCoefficient 15 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_6_pos :
    0<secondControlDefectTensorCoefficient 15 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_7_pos :
    0<secondControlDefectTensorCoefficient 15 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_8_pos :
    0<secondControlDefectTensorCoefficient 15 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_15_9_pos :
    0<secondControlDefectTensorCoefficient 15 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm15Norm _).property]
  norm_num [secondControlDefectClockForm15Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
