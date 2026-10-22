import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior16TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior16ClockForm16Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior16ClockForm 16 x=c} := by
  have he : slopeInterior16ClockForm 16 x=slopeInterior16ClockForm 16 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior16ClockForm,
      slopeInterior16Form4,slopeInterior16Form5,slopeInterior16Form6,slopeInterior16Form7,slopeInterior16Form8,slopeInterior16Form9,slopeInterior16Form10,slopeInterior16Form11,slopeInterior16Form12,slopeInterior16Form13,slopeInterior16Form14,slopeInterior16Form15,slopeInterior16Form16,slopeInterior16Form17,slopeInterior16Form18,slopeInterior16Form19,slopeInterior16Form20,slopeInterior16Form21,slopeInterior16Form22,slopeInterior16Form23,slopeInterior16Form24,slopeInterior16Form25,slopeInterior16Form26,slopeInterior16Form27,slopeInterior16Form28,slopeInterior16Form29,slopeInterior16Form30,slopeInterior16Form31,slopeInterior16Form32,slopeInterior16Form33,slopeInterior16Form34,slopeInterior16Form35,slopeInterior16Form36,slopeInterior16Form37,slopeInterior16Form38,slopeInterior16Form39,slopeInterior16Form40,slopeInterior16Form41,slopeInterior16Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior16TensorCoefficient_16_0_pos :
    0 < slopeInterior16TensorCoefficient 16 0 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_1_pos :
    0 < slopeInterior16TensorCoefficient 16 1 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_2_pos :
    0 < slopeInterior16TensorCoefficient 16 2 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_3_pos :
    0 < slopeInterior16TensorCoefficient 16 3 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_4_pos :
    0 < slopeInterior16TensorCoefficient 16 4 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_5_pos :
    0 < slopeInterior16TensorCoefficient 16 5 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_6_pos :
    0 < slopeInterior16TensorCoefficient 16 6 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_7_pos :
    0 < slopeInterior16TensorCoefficient 16 7 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_8_pos :
    0 < slopeInterior16TensorCoefficient 16 8 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_16_9_pos :
    0 < slopeInterior16TensorCoefficient 16 9 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm16Norm _).property]
  norm_num [slopeInterior16ClockForm16Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

