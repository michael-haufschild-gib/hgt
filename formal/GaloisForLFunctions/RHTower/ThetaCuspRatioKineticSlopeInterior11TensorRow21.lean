import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior11TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior11ClockForm21Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior11ClockForm 21 x=c} := by
  have he : slopeInterior11ClockForm 21 x=slopeInterior11ClockForm 21 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior11ClockForm,
      slopeInterior11Form4,slopeInterior11Form5,slopeInterior11Form6,slopeInterior11Form7,slopeInterior11Form8,slopeInterior11Form9,slopeInterior11Form10,slopeInterior11Form11,slopeInterior11Form12,slopeInterior11Form13,slopeInterior11Form14,slopeInterior11Form15,slopeInterior11Form16,slopeInterior11Form17,slopeInterior11Form18,slopeInterior11Form19,slopeInterior11Form20,slopeInterior11Form21,slopeInterior11Form22,slopeInterior11Form23,slopeInterior11Form24,slopeInterior11Form25,slopeInterior11Form26,slopeInterior11Form27,slopeInterior11Form28,slopeInterior11Form29,slopeInterior11Form30,slopeInterior11Form31,slopeInterior11Form32,slopeInterior11Form33,slopeInterior11Form34,slopeInterior11Form35,slopeInterior11Form36,slopeInterior11Form37,slopeInterior11Form38,slopeInterior11Form39,slopeInterior11Form40,slopeInterior11Form41,slopeInterior11Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior11TensorCoefficient_21_0_pos :
    0 < slopeInterior11TensorCoefficient 21 0 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_1_pos :
    0 < slopeInterior11TensorCoefficient 21 1 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_2_pos :
    0 < slopeInterior11TensorCoefficient 21 2 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_3_pos :
    0 < slopeInterior11TensorCoefficient 21 3 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_4_pos :
    0 < slopeInterior11TensorCoefficient 21 4 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_5_pos :
    0 < slopeInterior11TensorCoefficient 21 5 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_6_pos :
    0 < slopeInterior11TensorCoefficient 21 6 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_7_pos :
    0 < slopeInterior11TensorCoefficient 21 7 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_8_pos :
    0 < slopeInterior11TensorCoefficient 21 8 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior11TensorCoefficient_21_9_pos :
    0 < slopeInterior11TensorCoefficient 21 9 := by
  rw [slopeInterior11TensorCoefficient,(slopeInterior11ClockForm21Norm _).property]
  norm_num [slopeInterior11ClockForm21Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

