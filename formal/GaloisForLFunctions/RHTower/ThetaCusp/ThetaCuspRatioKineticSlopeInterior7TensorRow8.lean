import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior7TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior7ClockForm8Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior7ClockForm 8 x=c} := by
  have he : slopeInterior7ClockForm 8 x=slopeInterior7ClockForm 8 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior7ClockForm,
      slopeInterior7Form4,slopeInterior7Form5,slopeInterior7Form6,slopeInterior7Form7,slopeInterior7Form8,slopeInterior7Form9,slopeInterior7Form10,slopeInterior7Form11,slopeInterior7Form12,slopeInterior7Form13,slopeInterior7Form14,slopeInterior7Form15,slopeInterior7Form16,slopeInterior7Form17,slopeInterior7Form18,slopeInterior7Form19,slopeInterior7Form20,slopeInterior7Form21,slopeInterior7Form22,slopeInterior7Form23,slopeInterior7Form24,slopeInterior7Form25,slopeInterior7Form26,slopeInterior7Form27,slopeInterior7Form28,slopeInterior7Form29,slopeInterior7Form30,slopeInterior7Form31,slopeInterior7Form32,slopeInterior7Form33,slopeInterior7Form34,slopeInterior7Form35,slopeInterior7Form36,slopeInterior7Form37,slopeInterior7Form38,slopeInterior7Form39,slopeInterior7Form40,slopeInterior7Form41,slopeInterior7Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior7TensorCoefficient_8_0_pos :
    0 < slopeInterior7TensorCoefficient 8 0 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_1_pos :
    0 < slopeInterior7TensorCoefficient 8 1 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_2_pos :
    0 < slopeInterior7TensorCoefficient 8 2 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_3_pos :
    0 < slopeInterior7TensorCoefficient 8 3 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_4_pos :
    0 < slopeInterior7TensorCoefficient 8 4 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_5_pos :
    0 < slopeInterior7TensorCoefficient 8 5 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_6_pos :
    0 < slopeInterior7TensorCoefficient 8 6 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_7_pos :
    0 < slopeInterior7TensorCoefficient 8 7 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_8_pos :
    0 < slopeInterior7TensorCoefficient 8 8 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_8_9_pos :
    0 < slopeInterior7TensorCoefficient 8 9 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm8Norm _).property]
  norm_num [slopeInterior7ClockForm8Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

