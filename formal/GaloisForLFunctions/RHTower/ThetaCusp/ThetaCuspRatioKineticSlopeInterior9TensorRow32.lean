import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior9TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior9ClockForm32Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior9ClockForm 32 x=c} := by
  have he : slopeInterior9ClockForm 32 x=slopeInterior9ClockForm 32 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior9ClockForm,
      slopeInterior9Form4,slopeInterior9Form5,slopeInterior9Form6,slopeInterior9Form7,slopeInterior9Form8,slopeInterior9Form9,slopeInterior9Form10,slopeInterior9Form11,slopeInterior9Form12,slopeInterior9Form13,slopeInterior9Form14,slopeInterior9Form15,slopeInterior9Form16,slopeInterior9Form17,slopeInterior9Form18,slopeInterior9Form19,slopeInterior9Form20,slopeInterior9Form21,slopeInterior9Form22,slopeInterior9Form23,slopeInterior9Form24,slopeInterior9Form25,slopeInterior9Form26,slopeInterior9Form27,slopeInterior9Form28,slopeInterior9Form29,slopeInterior9Form30,slopeInterior9Form31,slopeInterior9Form32,slopeInterior9Form33,slopeInterior9Form34,slopeInterior9Form35,slopeInterior9Form36,slopeInterior9Form37,slopeInterior9Form38,slopeInterior9Form39,slopeInterior9Form40,slopeInterior9Form41,slopeInterior9Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior9TensorCoefficient_32_0_pos :
    0 < slopeInterior9TensorCoefficient 32 0 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_1_pos :
    0 < slopeInterior9TensorCoefficient 32 1 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_2_pos :
    0 < slopeInterior9TensorCoefficient 32 2 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_3_pos :
    0 < slopeInterior9TensorCoefficient 32 3 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_4_pos :
    0 < slopeInterior9TensorCoefficient 32 4 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_5_pos :
    0 < slopeInterior9TensorCoefficient 32 5 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_6_pos :
    0 < slopeInterior9TensorCoefficient 32 6 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_7_pos :
    0 < slopeInterior9TensorCoefficient 32 7 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_8_pos :
    0 < slopeInterior9TensorCoefficient 32 8 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior9TensorCoefficient_32_9_pos :
    0 < slopeInterior9TensorCoefficient 32 9 := by
  rw [slopeInterior9TensorCoefficient,(slopeInterior9ClockForm32Norm _).property]
  norm_num [slopeInterior9ClockForm32Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

