import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm16Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 16 x=c} := by
  have he : secondControlDefectClockForm 16 x=secondControlDefectClockForm 16 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_16_0_pos :
    0<secondControlDefectTensorCoefficient 16 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_1_pos :
    0<secondControlDefectTensorCoefficient 16 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_2_pos :
    0<secondControlDefectTensorCoefficient 16 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_3_pos :
    0<secondControlDefectTensorCoefficient 16 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_4_pos :
    0<secondControlDefectTensorCoefficient 16 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_5_pos :
    0<secondControlDefectTensorCoefficient 16 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_6_pos :
    0<secondControlDefectTensorCoefficient 16 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_7_pos :
    0<secondControlDefectTensorCoefficient 16 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_8_pos :
    0<secondControlDefectTensorCoefficient 16 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_16_9_pos :
    0<secondControlDefectTensorCoefficient 16 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm16Norm _).property]
  norm_num [secondControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
