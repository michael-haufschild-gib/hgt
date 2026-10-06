import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior14TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior14ClockForm21Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior14ClockForm 21 x=c} := by
  have he : slopeInterior14ClockForm 21 x=slopeInterior14ClockForm 21 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior14ClockForm,
      slopeInterior14Form4,slopeInterior14Form5,slopeInterior14Form6,slopeInterior14Form7,slopeInterior14Form8,slopeInterior14Form9,slopeInterior14Form10,slopeInterior14Form11,slopeInterior14Form12,slopeInterior14Form13,slopeInterior14Form14,slopeInterior14Form15,slopeInterior14Form16,slopeInterior14Form17,slopeInterior14Form18,slopeInterior14Form19,slopeInterior14Form20,slopeInterior14Form21,slopeInterior14Form22,slopeInterior14Form23,slopeInterior14Form24,slopeInterior14Form25,slopeInterior14Form26,slopeInterior14Form27,slopeInterior14Form28,slopeInterior14Form29,slopeInterior14Form30,slopeInterior14Form31,slopeInterior14Form32,slopeInterior14Form33,slopeInterior14Form34,slopeInterior14Form35,slopeInterior14Form36,slopeInterior14Form37,slopeInterior14Form38,slopeInterior14Form39,slopeInterior14Form40,slopeInterior14Form41,slopeInterior14Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior14TensorCoefficient_21_0_pos :
    0 < slopeInterior14TensorCoefficient 21 0 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_1_pos :
    0 < slopeInterior14TensorCoefficient 21 1 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_2_pos :
    0 < slopeInterior14TensorCoefficient 21 2 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_3_pos :
    0 < slopeInterior14TensorCoefficient 21 3 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_4_pos :
    0 < slopeInterior14TensorCoefficient 21 4 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_5_pos :
    0 < slopeInterior14TensorCoefficient 21 5 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_6_pos :
    0 < slopeInterior14TensorCoefficient 21 6 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_7_pos :
    0 < slopeInterior14TensorCoefficient 21 7 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_8_pos :
    0 < slopeInterior14TensorCoefficient 21 8 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior14TensorCoefficient_21_9_pos :
    0 < slopeInterior14TensorCoefficient 21 9 := by
  rw [slopeInterior14TensorCoefficient,(slopeInterior14ClockForm21Norm _).property]
  norm_num [slopeInterior14ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

