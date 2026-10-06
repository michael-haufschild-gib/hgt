import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm12Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 12 x=c} := by
  have he : firstControlDefectClockForm 12 x=firstControlDefectClockForm 12 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_12_0_pos :
    0<firstControlDefectTensorCoefficient 12 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_1_pos :
    0<firstControlDefectTensorCoefficient 12 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_2_pos :
    0<firstControlDefectTensorCoefficient 12 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_3_pos :
    0<firstControlDefectTensorCoefficient 12 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_4_pos :
    0<firstControlDefectTensorCoefficient 12 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_5_pos :
    0<firstControlDefectTensorCoefficient 12 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_6_pos :
    0<firstControlDefectTensorCoefficient 12 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_7_pos :
    0<firstControlDefectTensorCoefficient 12 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_8_pos :
    0<firstControlDefectTensorCoefficient 12 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_12_9_pos :
    0<firstControlDefectTensorCoefficient 12 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm12Norm _).property]
  norm_num [firstControlDefectClockForm12Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
