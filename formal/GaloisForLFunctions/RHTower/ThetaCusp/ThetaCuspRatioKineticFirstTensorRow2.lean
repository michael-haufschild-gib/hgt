import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm2Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 2 x=c} := by
  have he : firstControlDefectClockForm 2 x=firstControlDefectClockForm 2 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_2_0_pos :
    0<firstControlDefectTensorCoefficient 2 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_1_pos :
    0<firstControlDefectTensorCoefficient 2 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_2_pos :
    0<firstControlDefectTensorCoefficient 2 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_3_pos :
    0<firstControlDefectTensorCoefficient 2 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_4_pos :
    0<firstControlDefectTensorCoefficient 2 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_5_pos :
    0<firstControlDefectTensorCoefficient 2 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_6_pos :
    0<firstControlDefectTensorCoefficient 2 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_7_pos :
    0<firstControlDefectTensorCoefficient 2 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_8_pos :
    0<firstControlDefectTensorCoefficient 2 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_2_9_pos :
    0<firstControlDefectTensorCoefficient 2 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm2Norm _).property]
  norm_num [firstControlDefectClockForm2Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
