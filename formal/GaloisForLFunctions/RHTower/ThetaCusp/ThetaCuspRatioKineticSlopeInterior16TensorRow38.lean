import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior16TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior16ClockForm38Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior16ClockForm 38 x=c} := by
  have he : slopeInterior16ClockForm 38 x=slopeInterior16ClockForm 38 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior16ClockForm,
      slopeInterior16Form4,slopeInterior16Form5,slopeInterior16Form6,slopeInterior16Form7,slopeInterior16Form8,slopeInterior16Form9,slopeInterior16Form10,slopeInterior16Form11,slopeInterior16Form12,slopeInterior16Form13,slopeInterior16Form14,slopeInterior16Form15,slopeInterior16Form16,slopeInterior16Form17,slopeInterior16Form18,slopeInterior16Form19,slopeInterior16Form20,slopeInterior16Form21,slopeInterior16Form22,slopeInterior16Form23,slopeInterior16Form24,slopeInterior16Form25,slopeInterior16Form26,slopeInterior16Form27,slopeInterior16Form28,slopeInterior16Form29,slopeInterior16Form30,slopeInterior16Form31,slopeInterior16Form32,slopeInterior16Form33,slopeInterior16Form34,slopeInterior16Form35,slopeInterior16Form36,slopeInterior16Form37,slopeInterior16Form38,slopeInterior16Form39,slopeInterior16Form40,slopeInterior16Form41,slopeInterior16Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior16TensorCoefficient_38_0_pos :
    0 < slopeInterior16TensorCoefficient 38 0 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_1_pos :
    0 < slopeInterior16TensorCoefficient 38 1 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_2_pos :
    0 < slopeInterior16TensorCoefficient 38 2 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_3_pos :
    0 < slopeInterior16TensorCoefficient 38 3 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_4_pos :
    0 < slopeInterior16TensorCoefficient 38 4 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_5_pos :
    0 < slopeInterior16TensorCoefficient 38 5 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_6_pos :
    0 < slopeInterior16TensorCoefficient 38 6 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_7_pos :
    0 < slopeInterior16TensorCoefficient 38 7 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_8_pos :
    0 < slopeInterior16TensorCoefficient 38 8 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior16TensorCoefficient_38_9_pos :
    0 < slopeInterior16TensorCoefficient 38 9 := by
  rw [slopeInterior16TensorCoefficient,(slopeInterior16ClockForm38Norm _).property]
  norm_num [slopeInterior16ClockForm38Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

