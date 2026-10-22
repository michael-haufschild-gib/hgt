import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm32Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 32 x=c} := by
  have he : firstControlDefectClockForm 32 x=firstControlDefectClockForm 32 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_32_0_pos :
    0<firstControlDefectTensorCoefficient 32 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_1_pos :
    0<firstControlDefectTensorCoefficient 32 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_2_pos :
    0<firstControlDefectTensorCoefficient 32 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_3_pos :
    0<firstControlDefectTensorCoefficient 32 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_4_pos :
    0<firstControlDefectTensorCoefficient 32 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_5_pos :
    0<firstControlDefectTensorCoefficient 32 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_6_pos :
    0<firstControlDefectTensorCoefficient 32 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_7_pos :
    0<firstControlDefectTensorCoefficient 32 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_8_pos :
    0<firstControlDefectTensorCoefficient 32 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_32_9_pos :
    0<firstControlDefectTensorCoefficient 32 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm32Norm _).property]
  norm_num [firstControlDefectClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
