import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior17TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior17ClockForm25Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior17ClockForm 25 x=c} := by
  have he : slopeInterior17ClockForm 25 x=slopeInterior17ClockForm 25 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior17ClockForm,
      slopeInterior17Form4,slopeInterior17Form5,slopeInterior17Form6,slopeInterior17Form7,slopeInterior17Form8,slopeInterior17Form9,slopeInterior17Form10,slopeInterior17Form11,slopeInterior17Form12,slopeInterior17Form13,slopeInterior17Form14,slopeInterior17Form15,slopeInterior17Form16,slopeInterior17Form17,slopeInterior17Form18,slopeInterior17Form19,slopeInterior17Form20,slopeInterior17Form21,slopeInterior17Form22,slopeInterior17Form23,slopeInterior17Form24,slopeInterior17Form25,slopeInterior17Form26,slopeInterior17Form27,slopeInterior17Form28,slopeInterior17Form29,slopeInterior17Form30,slopeInterior17Form31,slopeInterior17Form32,slopeInterior17Form33,slopeInterior17Form34,slopeInterior17Form35,slopeInterior17Form36,slopeInterior17Form37,slopeInterior17Form38,slopeInterior17Form39,slopeInterior17Form40,slopeInterior17Form41,slopeInterior17Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior17TensorCoefficient_25_0_pos :
    0 < slopeInterior17TensorCoefficient 25 0 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_1_pos :
    0 < slopeInterior17TensorCoefficient 25 1 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_2_pos :
    0 < slopeInterior17TensorCoefficient 25 2 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_3_pos :
    0 < slopeInterior17TensorCoefficient 25 3 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_4_pos :
    0 < slopeInterior17TensorCoefficient 25 4 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_5_pos :
    0 < slopeInterior17TensorCoefficient 25 5 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_6_pos :
    0 < slopeInterior17TensorCoefficient 25 6 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_7_pos :
    0 < slopeInterior17TensorCoefficient 25 7 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_8_pos :
    0 < slopeInterior17TensorCoefficient 25 8 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior17TensorCoefficient_25_9_pos :
    0 < slopeInterior17TensorCoefficient 25 9 := by
  rw [slopeInterior17TensorCoefficient,(slopeInterior17ClockForm25Norm _).property]
  norm_num [slopeInterior17ClockForm25Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

