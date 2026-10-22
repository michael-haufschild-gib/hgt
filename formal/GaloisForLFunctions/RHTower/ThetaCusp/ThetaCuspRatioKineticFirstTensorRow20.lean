import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm20Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 20 x=c} := by
  have he : firstControlDefectClockForm 20 x=firstControlDefectClockForm 20 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_20_0_pos :
    0<firstControlDefectTensorCoefficient 20 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_1_pos :
    0<firstControlDefectTensorCoefficient 20 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_2_pos :
    0<firstControlDefectTensorCoefficient 20 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_3_pos :
    0<firstControlDefectTensorCoefficient 20 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_4_pos :
    0<firstControlDefectTensorCoefficient 20 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_5_pos :
    0<firstControlDefectTensorCoefficient 20 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_6_pos :
    0<firstControlDefectTensorCoefficient 20 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_7_pos :
    0<firstControlDefectTensorCoefficient 20 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_8_pos :
    0<firstControlDefectTensorCoefficient 20 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_20_9_pos :
    0<firstControlDefectTensorCoefficient 20 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm20Norm _).property]
  norm_num [firstControlDefectClockForm20Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
