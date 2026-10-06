import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm24Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 24 x=c} := by
  have he : secondControlDefectClockForm 24 x=secondControlDefectClockForm 24 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_24_0_pos :
    0<secondControlDefectTensorCoefficient 24 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_1_pos :
    0<secondControlDefectTensorCoefficient 24 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_2_pos :
    0<secondControlDefectTensorCoefficient 24 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_3_pos :
    0<secondControlDefectTensorCoefficient 24 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_4_pos :
    0<secondControlDefectTensorCoefficient 24 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_5_pos :
    0<secondControlDefectTensorCoefficient 24 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_6_pos :
    0<secondControlDefectTensorCoefficient 24 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_7_pos :
    0<secondControlDefectTensorCoefficient 24 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_8_pos :
    0<secondControlDefectTensorCoefficient 24 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_24_9_pos :
    0<secondControlDefectTensorCoefficient 24 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm24Norm _).property]
  norm_num [secondControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
