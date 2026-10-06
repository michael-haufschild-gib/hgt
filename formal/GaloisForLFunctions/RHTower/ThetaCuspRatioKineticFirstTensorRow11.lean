import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm11Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 11 x=c} := by
  have he : firstControlDefectClockForm 11 x=firstControlDefectClockForm 11 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_11_0_pos :
    0<firstControlDefectTensorCoefficient 11 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_1_pos :
    0<firstControlDefectTensorCoefficient 11 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_2_pos :
    0<firstControlDefectTensorCoefficient 11 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_3_pos :
    0<firstControlDefectTensorCoefficient 11 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_4_pos :
    0<firstControlDefectTensorCoefficient 11 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_5_pos :
    0<firstControlDefectTensorCoefficient 11 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_6_pos :
    0<firstControlDefectTensorCoefficient 11 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_7_pos :
    0<firstControlDefectTensorCoefficient 11 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_8_pos :
    0<firstControlDefectTensorCoefficient 11 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_11_9_pos :
    0<firstControlDefectTensorCoefficient 11 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm11Norm _).property]
  norm_num [firstControlDefectClockForm11Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
