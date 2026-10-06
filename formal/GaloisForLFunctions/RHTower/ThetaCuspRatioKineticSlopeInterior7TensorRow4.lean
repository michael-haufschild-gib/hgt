import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior7TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior7ClockForm4Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior7ClockForm 4 x=c} := by
  have he : slopeInterior7ClockForm 4 x=slopeInterior7ClockForm 4 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior7ClockForm,
      slopeInterior7Form4,slopeInterior7Form5,slopeInterior7Form6,slopeInterior7Form7,slopeInterior7Form8,slopeInterior7Form9,slopeInterior7Form10,slopeInterior7Form11,slopeInterior7Form12,slopeInterior7Form13,slopeInterior7Form14,slopeInterior7Form15,slopeInterior7Form16,slopeInterior7Form17,slopeInterior7Form18,slopeInterior7Form19,slopeInterior7Form20,slopeInterior7Form21,slopeInterior7Form22,slopeInterior7Form23,slopeInterior7Form24,slopeInterior7Form25,slopeInterior7Form26,slopeInterior7Form27,slopeInterior7Form28,slopeInterior7Form29,slopeInterior7Form30,slopeInterior7Form31,slopeInterior7Form32,slopeInterior7Form33,slopeInterior7Form34,slopeInterior7Form35,slopeInterior7Form36,slopeInterior7Form37,slopeInterior7Form38,slopeInterior7Form39,slopeInterior7Form40,slopeInterior7Form41,slopeInterior7Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior7TensorCoefficient_4_0_pos :
    0 < slopeInterior7TensorCoefficient 4 0 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_1_pos :
    0 < slopeInterior7TensorCoefficient 4 1 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_2_pos :
    0 < slopeInterior7TensorCoefficient 4 2 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_3_pos :
    0 < slopeInterior7TensorCoefficient 4 3 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_4_pos :
    0 < slopeInterior7TensorCoefficient 4 4 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_5_pos :
    0 < slopeInterior7TensorCoefficient 4 5 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_6_pos :
    0 < slopeInterior7TensorCoefficient 4 6 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_7_pos :
    0 < slopeInterior7TensorCoefficient 4 7 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_8_pos :
    0 < slopeInterior7TensorCoefficient 4 8 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior7TensorCoefficient_4_9_pos :
    0 < slopeInterior7TensorCoefficient 4 9 := by
  rw [slopeInterior7TensorCoefficient,(slopeInterior7ClockForm4Norm _).property]
  norm_num [slopeInterior7ClockForm4Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

