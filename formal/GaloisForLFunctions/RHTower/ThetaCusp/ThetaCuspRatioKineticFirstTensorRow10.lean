import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm10Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 10 x=c} := by
  have he : firstControlDefectClockForm 10 x=firstControlDefectClockForm 10 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_10_0_pos :
    0<firstControlDefectTensorCoefficient 10 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_1_pos :
    0<firstControlDefectTensorCoefficient 10 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_2_pos :
    0<firstControlDefectTensorCoefficient 10 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_3_pos :
    0<firstControlDefectTensorCoefficient 10 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_4_pos :
    0<firstControlDefectTensorCoefficient 10 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_5_pos :
    0<firstControlDefectTensorCoefficient 10 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_6_pos :
    0<firstControlDefectTensorCoefficient 10 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_7_pos :
    0<firstControlDefectTensorCoefficient 10 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_8_pos :
    0<firstControlDefectTensorCoefficient 10 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_10_9_pos :
    0<firstControlDefectTensorCoefficient 10 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm10Norm _).property]
  norm_num [firstControlDefectClockForm10Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
