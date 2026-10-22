import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm18Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 18 x=c} := by
  have he : secondControlDefectClockForm 18 x=secondControlDefectClockForm 18 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_18_0_pos :
    0<secondControlDefectTensorCoefficient 18 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_1_pos :
    0<secondControlDefectTensorCoefficient 18 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_2_pos :
    0<secondControlDefectTensorCoefficient 18 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_3_pos :
    0<secondControlDefectTensorCoefficient 18 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_4_pos :
    0<secondControlDefectTensorCoefficient 18 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_5_pos :
    0<secondControlDefectTensorCoefficient 18 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_6_pos :
    0<secondControlDefectTensorCoefficient 18 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_7_pos :
    0<secondControlDefectTensorCoefficient 18 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_8_pos :
    0<secondControlDefectTensorCoefficient 18 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_18_9_pos :
    0<secondControlDefectTensorCoefficient 18 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm18Norm _).property]
  norm_num [secondControlDefectClockForm18Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
