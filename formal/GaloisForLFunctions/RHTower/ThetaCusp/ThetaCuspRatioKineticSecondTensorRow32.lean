import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def secondControlDefectClockForm32Norm (x : ℕ → ℝ) :
    {c : ℝ // secondControlDefectClockForm 32 x=c} := by
  have he : secondControlDefectClockForm 32 x=secondControlDefectClockForm 32 x := rfl
  conv at he =>
    rhs
    norm_num [secondControlDefectClockForm,
      secondControlDefectForm4,secondControlDefectForm5,secondControlDefectForm6,secondControlDefectForm7,secondControlDefectForm8,secondControlDefectForm9,secondControlDefectForm10,secondControlDefectForm11,secondControlDefectForm12,secondControlDefectForm13,secondControlDefectForm14,secondControlDefectForm15,secondControlDefectForm16,secondControlDefectForm17,secondControlDefectForm18,secondControlDefectForm19,secondControlDefectForm20,secondControlDefectForm21,secondControlDefectForm22,secondControlDefectForm23,secondControlDefectForm24,secondControlDefectForm25,secondControlDefectForm26,secondControlDefectForm27,secondControlDefectForm28,secondControlDefectForm29,secondControlDefectForm30,secondControlDefectForm31,secondControlDefectForm32,secondControlDefectForm33,secondControlDefectForm34,secondControlDefectForm35,secondControlDefectForm36,secondControlDefectForm37,secondControlDefectForm38,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem secondControlDefectTensorCoefficient_32_0_pos :
    0<secondControlDefectTensorCoefficient 32 0 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_1_pos :
    0<secondControlDefectTensorCoefficient 32 1 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_2_pos :
    0<secondControlDefectTensorCoefficient 32 2 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_3_pos :
    0<secondControlDefectTensorCoefficient 32 3 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_4_pos :
    0<secondControlDefectTensorCoefficient 32 4 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_5_pos :
    0<secondControlDefectTensorCoefficient 32 5 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_6_pos :
    0<secondControlDefectTensorCoefficient 32 6 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_7_pos :
    0<secondControlDefectTensorCoefficient 32 7 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_8_pos :
    0<secondControlDefectTensorCoefficient 32 8 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem secondControlDefectTensorCoefficient_32_9_pos :
    0<secondControlDefectTensorCoefficient 32 9 := by
  rw [secondControlDefectTensorCoefficient,(secondControlDefectClockForm32Norm _).property]
  norm_num [secondControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
