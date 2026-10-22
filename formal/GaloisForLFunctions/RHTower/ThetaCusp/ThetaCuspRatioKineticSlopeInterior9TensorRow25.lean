import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior9TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior9ClockForm25Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior9ClockForm 25 x=c} := by
  have he : slopeInterior9ClockForm 25 x=slopeInterior9ClockForm 25 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior9ClockForm,
      slopeInterior9Form4,slopeInterior9Form5,slopeInterior9Form6,slopeInterior9Form7,slopeInterior9Form8,slopeInterior9Form9,slopeInterior9Form10,slopeInterior9Form11,slopeInterior9Form12,slopeInterior9Form13,slopeInterior9Form14,slopeInterior9Form15,slopeInterior9Form16,slopeInterior9Form17,slopeInterior9Form18,slopeInterior9Form19,slopeInterior9Form20,slopeInterior9Form21,slopeInterior9Form22,slopeInterior9Form23,slopeInterior9Form24,slopeInterior9Form25,slopeInterior9Form26,slopeInterior9Form27,slopeInterior9Form28,slopeInterior9Form29,slopeInterior9Form30,slopeInterior9Form31,slopeInterior9Form32,slopeInterior9Form33,slopeInterior9Form34,slopeInterior9Form35,slopeInterior9Form36,slopeInterior9Form37,slopeInterior9Form38,slopeInterior9Form39,slopeInterior9Form40,slopeInterior9Form41,slopeInterior9Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior9TensorCoefficient_25_0_pos :
    0 < slopeInterior9TensorCoefficient 25 0 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_1_pos :
    0 < slopeInterior9TensorCoefficient 25 1 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_2_pos :
    0 < slopeInterior9TensorCoefficient 25 2 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_3_pos :
    0 < slopeInterior9TensorCoefficient 25 3 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_4_pos :
    0 < slopeInterior9TensorCoefficient 25 4 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_5_pos :
    0 < slopeInterior9TensorCoefficient 25 5 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_6_pos :
    0 < slopeInterior9TensorCoefficient 25 6 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_7_pos :
    0 < slopeInterior9TensorCoefficient 25 7 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_8_pos :
    0 < slopeInterior9TensorCoefficient 25 8 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_25_9_pos :
    0 < slopeInterior9TensorCoefficient 25 9 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm25Norm _).property]
  norm_num [slopeInterior9ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

