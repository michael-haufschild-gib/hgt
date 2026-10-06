import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm19Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 19 x=c} := by
  have he : firstControlDefectClockForm 19 x=firstControlDefectClockForm 19 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_19_0_pos :
    0<firstControlDefectTensorCoefficient 19 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_1_pos :
    0<firstControlDefectTensorCoefficient 19 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_2_pos :
    0<firstControlDefectTensorCoefficient 19 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_3_pos :
    0<firstControlDefectTensorCoefficient 19 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_4_pos :
    0<firstControlDefectTensorCoefficient 19 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_5_pos :
    0<firstControlDefectTensorCoefficient 19 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_6_pos :
    0<firstControlDefectTensorCoefficient 19 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_7_pos :
    0<firstControlDefectTensorCoefficient 19 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_8_pos :
    0<firstControlDefectTensorCoefficient 19 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_19_9_pos :
    0<firstControlDefectTensorCoefficient 19 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm19Norm _).property]
  norm_num [firstControlDefectClockForm19Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
