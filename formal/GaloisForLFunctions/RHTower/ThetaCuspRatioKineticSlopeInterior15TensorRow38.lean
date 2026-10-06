import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeInterior15TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior15ClockForm38Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior15ClockForm 38 x=c} := by
  have he : slopeInterior15ClockForm 38 x=slopeInterior15ClockForm 38 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior15ClockForm,
      slopeInterior15Form4,slopeInterior15Form5,slopeInterior15Form6,slopeInterior15Form7,slopeInterior15Form8,slopeInterior15Form9,slopeInterior15Form10,slopeInterior15Form11,slopeInterior15Form12,slopeInterior15Form13,slopeInterior15Form14,slopeInterior15Form15,slopeInterior15Form16,slopeInterior15Form17,slopeInterior15Form18,slopeInterior15Form19,slopeInterior15Form20,slopeInterior15Form21,slopeInterior15Form22,slopeInterior15Form23,slopeInterior15Form24,slopeInterior15Form25,slopeInterior15Form26,slopeInterior15Form27,slopeInterior15Form28,slopeInterior15Form29,slopeInterior15Form30,slopeInterior15Form31,slopeInterior15Form32,slopeInterior15Form33,slopeInterior15Form34,slopeInterior15Form35,slopeInterior15Form36,slopeInterior15Form37,slopeInterior15Form38,slopeInterior15Form39,slopeInterior15Form40,slopeInterior15Form41,slopeInterior15Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior15TensorCoefficient_38_0_pos :
    0 < slopeInterior15TensorCoefficient 38 0 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_1_pos :
    0 < slopeInterior15TensorCoefficient 38 1 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_2_pos :
    0 < slopeInterior15TensorCoefficient 38 2 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_3_pos :
    0 < slopeInterior15TensorCoefficient 38 3 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_4_pos :
    0 < slopeInterior15TensorCoefficient 38 4 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_5_pos :
    0 < slopeInterior15TensorCoefficient 38 5 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_6_pos :
    0 < slopeInterior15TensorCoefficient 38 6 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_7_pos :
    0 < slopeInterior15TensorCoefficient 38 7 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_8_pos :
    0 < slopeInterior15TensorCoefficient 38 8 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior15TensorCoefficient_38_9_pos :
    0 < slopeInterior15TensorCoefficient 38 9 := by
  rw [slopeInterior15TensorCoefficient,(slopeInterior15ClockForm38Norm _).property]
  norm_num [slopeInterior15ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

