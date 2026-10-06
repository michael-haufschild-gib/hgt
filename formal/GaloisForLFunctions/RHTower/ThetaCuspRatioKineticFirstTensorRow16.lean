import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm16Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 16 x=c} := by
  have he : firstControlDefectClockForm 16 x=firstControlDefectClockForm 16 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_16_0_pos :
    0<firstControlDefectTensorCoefficient 16 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_1_pos :
    0<firstControlDefectTensorCoefficient 16 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_2_pos :
    0<firstControlDefectTensorCoefficient 16 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_3_pos :
    0<firstControlDefectTensorCoefficient 16 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_4_pos :
    0<firstControlDefectTensorCoefficient 16 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_5_pos :
    0<firstControlDefectTensorCoefficient 16 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_6_pos :
    0<firstControlDefectTensorCoefficient 16 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_7_pos :
    0<firstControlDefectTensorCoefficient 16 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_8_pos :
    0<firstControlDefectTensorCoefficient 16 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_16_9_pos :
    0<firstControlDefectTensorCoefficient 16 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm16Norm _).property]
  norm_num [firstControlDefectClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
