import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm10Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 10 x=c} := by
  have he : secondControlDefectClockForm 10 x=secondControlDefectClockForm 10 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_10_0_pos :
    0<secondControlDefectTensorCoefficient 10 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_1_pos :
    0<secondControlDefectTensorCoefficient 10 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_2_pos :
    0<secondControlDefectTensorCoefficient 10 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_3_pos :
    0<secondControlDefectTensorCoefficient 10 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_4_pos :
    0<secondControlDefectTensorCoefficient 10 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_5_pos :
    0<secondControlDefectTensorCoefficient 10 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_6_pos :
    0<secondControlDefectTensorCoefficient 10 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_7_pos :
    0<secondControlDefectTensorCoefficient 10 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_8_pos :
    0<secondControlDefectTensorCoefficient 10 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_10_9_pos :
    0<secondControlDefectTensorCoefficient 10 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm10Norm _).property]
  norm_num [secondControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
