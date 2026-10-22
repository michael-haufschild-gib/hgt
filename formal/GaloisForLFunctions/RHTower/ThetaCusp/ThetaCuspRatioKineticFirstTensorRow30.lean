import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm30Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 30 x=c} := by
  have he : firstControlDefectClockForm 30 x=firstControlDefectClockForm 30 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_30_0_pos :
    0<firstControlDefectTensorCoefficient 30 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_1_pos :
    0<firstControlDefectTensorCoefficient 30 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_2_pos :
    0<firstControlDefectTensorCoefficient 30 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_3_pos :
    0<firstControlDefectTensorCoefficient 30 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_4_pos :
    0<firstControlDefectTensorCoefficient 30 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_5_pos :
    0<firstControlDefectTensorCoefficient 30 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_6_pos :
    0<firstControlDefectTensorCoefficient 30 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_7_pos :
    0<firstControlDefectTensorCoefficient 30 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_8_pos :
    0<firstControlDefectTensorCoefficient 30 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_30_9_pos :
    0<firstControlDefectTensorCoefficient 30 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm30Norm _).property]
  norm_num [firstControlDefectClockForm30Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
