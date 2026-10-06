import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior5TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior5ClockForm25Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior5ClockForm 25 x=c} := by
  have he : slopeInterior5ClockForm 25 x=slopeInterior5ClockForm 25 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior5ClockForm,
      slopeInterior5Form4,slopeInterior5Form5,slopeInterior5Form6,slopeInterior5Form7,slopeInterior5Form8,slopeInterior5Form9,slopeInterior5Form10,slopeInterior5Form11,slopeInterior5Form12,slopeInterior5Form13,slopeInterior5Form14,slopeInterior5Form15,slopeInterior5Form16,slopeInterior5Form17,slopeInterior5Form18,slopeInterior5Form19,slopeInterior5Form20,slopeInterior5Form21,slopeInterior5Form22,slopeInterior5Form23,slopeInterior5Form24,slopeInterior5Form25,slopeInterior5Form26,slopeInterior5Form27,slopeInterior5Form28,slopeInterior5Form29,slopeInterior5Form30,slopeInterior5Form31,slopeInterior5Form32,slopeInterior5Form33,slopeInterior5Form34,slopeInterior5Form35,slopeInterior5Form36,slopeInterior5Form37,slopeInterior5Form38,slopeInterior5Form39,slopeInterior5Form40,slopeInterior5Form41,slopeInterior5Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior5TensorCoefficient_25_0_pos :
    0 < slopeInterior5TensorCoefficient 25 0 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_1_pos :
    0 < slopeInterior5TensorCoefficient 25 1 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_2_pos :
    0 < slopeInterior5TensorCoefficient 25 2 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_3_pos :
    0 < slopeInterior5TensorCoefficient 25 3 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_4_pos :
    0 < slopeInterior5TensorCoefficient 25 4 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_5_pos :
    0 < slopeInterior5TensorCoefficient 25 5 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_6_pos :
    0 < slopeInterior5TensorCoefficient 25 6 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_7_pos :
    0 < slopeInterior5TensorCoefficient 25 7 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_8_pos :
    0 < slopeInterior5TensorCoefficient 25 8 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior5TensorCoefficient_25_9_pos :
    0 < slopeInterior5TensorCoefficient 25 9 := by
  rw [slopeInterior5TensorCoefficient,(slopeInterior5ClockForm25Norm _).property]
  norm_num [slopeInterior5ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

