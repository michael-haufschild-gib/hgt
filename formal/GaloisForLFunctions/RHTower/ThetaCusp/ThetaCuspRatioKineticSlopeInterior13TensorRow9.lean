import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior13TensorForm
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

def slopeInterior13ClockForm9Norm (x : ℕ → ℝ) : {c : ℝ // slopeInterior13ClockForm 9 x=c} := by
  have he : slopeInterior13ClockForm 9 x=slopeInterior13ClockForm 9 x := rfl
  conv at he =>
    rhs
    norm_num [slopeInterior13ClockForm,
      slopeInterior13Form4,slopeInterior13Form5,slopeInterior13Form6,slopeInterior13Form7,slopeInterior13Form8,slopeInterior13Form9,slopeInterior13Form10,slopeInterior13Form11,slopeInterior13Form12,slopeInterior13Form13,slopeInterior13Form14,slopeInterior13Form15,slopeInterior13Form16,slopeInterior13Form17,slopeInterior13Form18,slopeInterior13Form19,slopeInterior13Form20,slopeInterior13Form21,slopeInterior13Form22,slopeInterior13Form23,slopeInterior13Form24,slopeInterior13Form25,slopeInterior13Form26,slopeInterior13Form27,slopeInterior13Form28,slopeInterior13Form29,slopeInterior13Form30,slopeInterior13Form31,slopeInterior13Form32,slopeInterior13Form33,slopeInterior13Form34,slopeInterior13Form35,slopeInterior13Form36,slopeInterior13Form37,slopeInterior13Form38,slopeInterior13Form39,slopeInterior13Form40,slopeInterior13Form41,slopeInterior13Form42,
      Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
      Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem slopeInterior13TensorCoefficient_9_0_pos :
    0 < slopeInterior13TensorCoefficient 9 0 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_1_pos :
    0 < slopeInterior13TensorCoefficient 9 1 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_2_pos :
    0 < slopeInterior13TensorCoefficient 9 2 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_3_pos :
    0 < slopeInterior13TensorCoefficient 9 3 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_4_pos :
    0 < slopeInterior13TensorCoefficient 9 4 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_5_pos :
    0 < slopeInterior13TensorCoefficient 9 5 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_6_pos :
    0 < slopeInterior13TensorCoefficient 9 6 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_7_pos :
    0 < slopeInterior13TensorCoefficient 9 7 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_8_pos :
    0 < slopeInterior13TensorCoefficient 9 8 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem slopeInterior13TensorCoefficient_9_9_pos :
    0 < slopeInterior13TensorCoefficient 9 9 := by
  rw [slopeInterior13TensorCoefficient,(slopeInterior13ClockForm9Norm _).property]
  norm_num [slopeInterior13ClockForm9Norm,Nat.rawCast,Int.rawCast,degreeElevationCoefficient,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

end
end HTGeometry.ThetaRatioKineticContraction

