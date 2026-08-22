import GaloisForLFunctions.HTGeometry.LinearExponentialSum

/-!
# Abe damping along a real period coordinate

In Abe's toroidal coordinates, the complementary shift of the damping coordinate is real.  Its
additive character therefore has unit modulus: this gives an index-uniform compact bound for the
literal exponential multiplier, while allowing the real part of the phase to approach zero.  This
is precisely the modulus control needed by the normalized-tail route, and is distinct from the
false uniform damping-gap assertion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Abe's complex coordinate character `z ↦ exp (2π i z)`. -/
def abeRealCoordinateCharacter (z : ℂ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)

/-- A real period shift multiplies Abe's coordinate character by the unit additive character. -/
theorem abeRealCoordinateCharacter_translate (z : ℂ) (r : ℝ) :
    abeRealCoordinateCharacter (z + (r : ℂ)) =
      abeRealCoordinateCharacter z * HTGeometry.ee r := by
  unfold abeRealCoordinateCharacter HTGeometry.ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Real period shifts preserve the modulus of Abe's coordinate character exactly. -/
theorem norm_abeRealCoordinateCharacter_translate (z : ℂ) (r : ℝ) :
    ‖abeRealCoordinateCharacter (z + (r : ℂ))‖ =
      ‖abeRealCoordinateCharacter z‖ := by
  rw [abeRealCoordinateCharacter_translate, norm_mul, HTGeometry.norm_ee, mul_one]

/-- The literal exponential damping factor in Abe's real-period coordinate. -/
def abeRealCoordinateDamping (t z ω : ℂ) : ℂ :=
  Complex.exp (t * (abeRealCoordinateCharacter z - ω))

/-- A real lattice shift admits a bound independent of its index.  This controls the multiplier's
modulus, not its damping phase. -/
theorem norm_abeRealCoordinateDamping_translate_le (t z ω : ℂ) (r : ℝ) :
    ‖abeRealCoordinateDamping t (z + (r : ℂ)) ω‖ ≤
      Real.exp (‖t‖ * (‖abeRealCoordinateCharacter z‖ + ‖ω‖)) := by
  rw [abeRealCoordinateDamping, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc (t * (abeRealCoordinateCharacter (z + (r : ℂ)) - ω)).re
      ≤ ‖t * (abeRealCoordinateCharacter (z + (r : ℂ)) - ω)‖ :=
        le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    _ = ‖t‖ * ‖abeRealCoordinateCharacter (z + (r : ℂ)) - ω‖ := norm_mul _ _
    _ ≤ ‖t‖ * (‖abeRealCoordinateCharacter (z + (r : ℂ))‖ + ‖ω‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖t‖ * (‖abeRealCoordinateCharacter z‖ + ‖ω‖) := by
      rw [norm_abeRealCoordinateCharacter_translate]

end

end GaloisForLFunctions.HTGeometry
