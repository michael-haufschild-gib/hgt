import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm25Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 25 x=c} := by
  have he : firstControlDefectClockForm 25 x=firstControlDefectClockForm 25 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_25_0_pos :
    0<firstControlDefectTensorCoefficient 25 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_1_pos :
    0<firstControlDefectTensorCoefficient 25 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_2_pos :
    0<firstControlDefectTensorCoefficient 25 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_3_pos :
    0<firstControlDefectTensorCoefficient 25 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_4_pos :
    0<firstControlDefectTensorCoefficient 25 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_5_pos :
    0<firstControlDefectTensorCoefficient 25 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_6_pos :
    0<firstControlDefectTensorCoefficient 25 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_7_pos :
    0<firstControlDefectTensorCoefficient 25 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_8_pos :
    0<firstControlDefectTensorCoefficient 25 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_25_9_pos :
    0<firstControlDefectTensorCoefficient 25 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm25Norm _).property]
  norm_num [firstControlDefectClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
