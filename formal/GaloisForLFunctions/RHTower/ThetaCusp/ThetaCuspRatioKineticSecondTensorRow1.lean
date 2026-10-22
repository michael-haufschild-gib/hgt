import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm1Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 1 x=c} := by
  have he : secondControlDefectClockForm 1 x=secondControlDefectClockForm 1 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_1_0_pos :
    0<secondControlDefectTensorCoefficient 1 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_1_pos :
    0<secondControlDefectTensorCoefficient 1 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_2_pos :
    0<secondControlDefectTensorCoefficient 1 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_3_pos :
    0<secondControlDefectTensorCoefficient 1 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_4_pos :
    0<secondControlDefectTensorCoefficient 1 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_5_pos :
    0<secondControlDefectTensorCoefficient 1 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_6_pos :
    0<secondControlDefectTensorCoefficient 1 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_7_pos :
    0<secondControlDefectTensorCoefficient 1 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_8_pos :
    0<secondControlDefectTensorCoefficient 1 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_1_9_pos :
    0<secondControlDefectTensorCoefficient 1 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm1Norm _).property]
  norm_num [secondControlDefectClockForm1Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
