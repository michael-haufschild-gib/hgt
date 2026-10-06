import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior5TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior5ClockForm24Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior5ClockForm 24 x=c} := by
  have he : slopeInterior5ClockForm 24 x=slopeInterior5ClockForm 24 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior5ClockForm,
      slopeInterior5Form4,slopeInterior5Form5,slopeInterior5Form6,slopeInterior5Form7,slopeInterior5Form8,slopeInterior5Form9,slopeInterior5Form10,slopeInterior5Form11,slopeInterior5Form12,slopeInterior5Form13,slopeInterior5Form14,slopeInterior5Form15,slopeInterior5Form16,slopeInterior5Form17,slopeInterior5Form18,slopeInterior5Form19,slopeInterior5Form20,slopeInterior5Form21,slopeInterior5Form22,slopeInterior5Form23,slopeInterior5Form24,slopeInterior5Form25,slopeInterior5Form26,slopeInterior5Form27,slopeInterior5Form28,slopeInterior5Form29,slopeInterior5Form30,slopeInterior5Form31,slopeInterior5Form32,slopeInterior5Form33,slopeInterior5Form34,slopeInterior5Form35,slopeInterior5Form36,slopeInterior5Form37,slopeInterior5Form38,slopeInterior5Form39,slopeInterior5Form40,slopeInterior5Form41,slopeInterior5Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior5TensorCoefficient_24_0_pos :
    0 < slopeInterior5TensorCoefficient 24 0 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_1_pos :
    0 < slopeInterior5TensorCoefficient 24 1 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_2_pos :
    0 < slopeInterior5TensorCoefficient 24 2 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_3_pos :
    0 < slopeInterior5TensorCoefficient 24 3 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_4_pos :
    0 < slopeInterior5TensorCoefficient 24 4 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_5_pos :
    0 < slopeInterior5TensorCoefficient 24 5 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_6_pos :
    0 < slopeInterior5TensorCoefficient 24 6 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_7_pos :
    0 < slopeInterior5TensorCoefficient 24 7 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_8_pos :
    0 < slopeInterior5TensorCoefficient 24 8 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_24_9_pos :
    0 < slopeInterior5TensorCoefficient 24 9 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm24Norm _).property]
  norm_num [slopeInterior5ClockForm24Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

