import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm12Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 12 x=c} := by
  have he : secondControlDefectClockForm 12 x=secondControlDefectClockForm 12 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_12_0_pos :
    0<secondControlDefectTensorCoefficient 12 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_1_pos :
    0<secondControlDefectTensorCoefficient 12 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_2_pos :
    0<secondControlDefectTensorCoefficient 12 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_3_pos :
    0<secondControlDefectTensorCoefficient 12 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_4_pos :
    0<secondControlDefectTensorCoefficient 12 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_5_pos :
    0<secondControlDefectTensorCoefficient 12 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_6_pos :
    0<secondControlDefectTensorCoefficient 12 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_7_pos :
    0<secondControlDefectTensorCoefficient 12 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_8_pos :
    0<secondControlDefectTensorCoefficient 12 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_12_9_pos :
    0<secondControlDefectTensorCoefficient 12 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm12Norm _).property]
  norm_num [secondControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
