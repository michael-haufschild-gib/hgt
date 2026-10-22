import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticFirstTensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def firstControlDefectClockForm24Norm (x : ℕ → ℝ) :
    {c : ℝ // firstControlDefectClockForm 24 x=c} := by
  have he : firstControlDefectClockForm 24 x=firstControlDefectClockForm 24 x := rfl
  conv at he =>
    rhs
    norm_num [firstControlDefectClockForm,
      firstControlDefectForm4,firstControlDefectForm5,firstControlDefectForm6,firstControlDefectForm7,firstControlDefectForm8,firstControlDefectForm9,firstControlDefectForm10,firstControlDefectForm11,firstControlDefectForm12,firstControlDefectForm13,firstControlDefectForm14,firstControlDefectForm15,firstControlDefectForm16,firstControlDefectForm17,firstControlDefectForm18,firstControlDefectForm19,firstControlDefectForm20,firstControlDefectForm21,firstControlDefectForm22,firstControlDefectForm23,firstControlDefectForm24,firstControlDefectForm25,firstControlDefectForm26,firstControlDefectForm27,firstControlDefectForm28,firstControlDefectForm29,firstControlDefectForm30,firstControlDefectForm31,firstControlDefectForm32,firstControlDefectForm33,firstControlDefectForm34,firstControlDefectForm35,firstControlDefectForm36,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem firstControlDefectTensorCoefficient_24_0_pos :
    0<firstControlDefectTensorCoefficient 24 0 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_1_pos :
    0<firstControlDefectTensorCoefficient 24 1 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_2_pos :
    0<firstControlDefectTensorCoefficient 24 2 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_3_pos :
    0<firstControlDefectTensorCoefficient 24 3 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_4_pos :
    0<firstControlDefectTensorCoefficient 24 4 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_5_pos :
    0<firstControlDefectTensorCoefficient 24 5 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_6_pos :
    0<firstControlDefectTensorCoefficient 24 6 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_7_pos :
    0<firstControlDefectTensorCoefficient 24 7 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_8_pos :
    0<firstControlDefectTensorCoefficient 24 8 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem firstControlDefectTensorCoefficient_24_9_pos :
    0<firstControlDefectTensorCoefficient 24 9 := by
  rw [firstControlDefectTensorCoefficient,(firstControlDefectClockForm24Norm _).property]
  norm_num [firstControlDefectClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction
