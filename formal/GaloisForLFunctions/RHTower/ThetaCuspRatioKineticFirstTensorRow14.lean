import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm14Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 14 x=c} := by
  have he : firstControlDefectClockForm 14 x=firstControlDefectClockForm 14 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_14_0_pos :
    0<firstControlDefectTensorCoefficient 14 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_1_pos :
    0<firstControlDefectTensorCoefficient 14 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_2_pos :
    0<firstControlDefectTensorCoefficient 14 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_3_pos :
    0<firstControlDefectTensorCoefficient 14 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_4_pos :
    0<firstControlDefectTensorCoefficient 14 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_5_pos :
    0<firstControlDefectTensorCoefficient 14 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_6_pos :
    0<firstControlDefectTensorCoefficient 14 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_7_pos :
    0<firstControlDefectTensorCoefficient 14 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_8_pos :
    0<firstControlDefectTensorCoefficient 14 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_14_9_pos :
    0<firstControlDefectTensorCoefficient 14 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm14Norm _).property]
  norm_num [firstControlDefectClockForm14Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
