import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm29Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 29 x=c} := by
  have he : firstControlDefectClockForm 29 x=firstControlDefectClockForm 29 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_29_0_pos :
    0<firstControlDefectTensorCoefficient 29 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_1_pos :
    0<firstControlDefectTensorCoefficient 29 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_2_pos :
    0<firstControlDefectTensorCoefficient 29 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_3_pos :
    0<firstControlDefectTensorCoefficient 29 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_4_pos :
    0<firstControlDefectTensorCoefficient 29 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_5_pos :
    0<firstControlDefectTensorCoefficient 29 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_6_pos :
    0<firstControlDefectTensorCoefficient 29 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_7_pos :
    0<firstControlDefectTensorCoefficient 29 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_8_pos :
    0<firstControlDefectTensorCoefficient 29 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_29_9_pos :
    0<firstControlDefectTensorCoefficient 29 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm29Norm _).property]
  norm_num [firstControlDefectClockForm29Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
