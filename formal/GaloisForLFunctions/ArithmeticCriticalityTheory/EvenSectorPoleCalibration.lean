import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSourceEquation

/-!
# Even-sector calibration: the constant profile is a strict subsolution

In Doob coordinates the even ground state of the Weil form is the constant profile `1`, the test
`Φ` itself. Both generators annihilate constants, so the constant profile is a strict subsolution of
the arithmetic Schrödinger form everywhere: `𝓛 1 = 0 < Φ(x) cosh(x/2)`. Its potential mass is the
pole mass `∫ Φ(x) cosh(x/2) dx = 1/2`. This is the even-sector negative direction in the language of
criticality theory, and it is the reason a positive supersolution must vanish at the origin: an even
positive supersolution on the whole line would make the even sector nonnegative.
-/

open MeasureTheory Set Filter Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem twoSidedShiftGenerator_const (c t x : ℝ) :
    twoSidedShiftGenerator (fun _ => c) t x = 0 := by
  unfold twoSidedShiftGenerator
  ring

theorem foldedShiftGenerator_const (c t x : ℝ) :
    foldedShiftGenerator (fun _ => c) t x = 0 := by
  unfold foldedShiftGenerator
  ring

theorem twoSidedGenerator_const (c x : ℝ) : twoSidedGenerator (fun _ => c) x = 0 := by
  unfold twoSidedGenerator
  simp [twoSidedShiftGenerator_const]

theorem foldedGenerator_const (c x : ℝ) : foldedGenerator (fun _ => c) x = 0 := by
  unfold foldedGenerator
  simp [foldedShiftGenerator_const]

/-- The constant profile is a strict subsolution of both generators at every point. -/
theorem foldedGenerator_const_lt_potential (x : ℝ) :
    foldedGenerator (fun _ => (1 : ℝ)) x < riemannKernelReal x * Real.cosh (x / 2) * 1 := by
  rw [foldedGenerator_const]
  have h1 := riemannKernelReal_pos x
  have h2 := Real.cosh_pos (x / 2)
  positivity

theorem twoSidedGenerator_const_lt_potential (x : ℝ) :
    twoSidedGenerator (fun _ => (1 : ℝ)) x < riemannKernelReal x * Real.cosh (x / 2) * 1 := by
  rw [twoSidedGenerator_const]
  have h1 := riemannKernelReal_pos x
  have h2 := Real.cosh_pos (x / 2)
  positivity

/-- The pole mass of the constant profile: `∫ Φ(x) cosh(x/2) dx = 1/2`. -/
theorem phiDoobCoshMass_const_one : phiDoobCoshMass (fun _ => (1 : ℝ)) = 1 / 2 := by
  unfold phiDoobCoshMass phiDoobTest
  simpa using integral_riemannKernelReal_cosh_half

/-- No even positive function on the whole line is a folded supersolution with the constant profile
as test coordinate: the source equation of the shifted ground state degenerates to the pole at
`a = 0`, where the shift difference vanishes identically. -/
theorem shiftDifference_zero (x : ℝ) : shiftDifference 0 x = 0 := by
  unfold shiftDifference
  simp

theorem shiftedGroundState_zero (x : ℝ) : shiftedGroundState 0 x = 0 := by
  unfold shiftedGroundState
  rw [shiftDifference_zero, zero_div]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
