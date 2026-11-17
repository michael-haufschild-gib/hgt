import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbePhaseGeometry

/-!
# Scalar pairings of the Weil reflection sectors

Pairing a vector with its negative-sector projection gives the negative
mass. Pairing it with reflection gives the real signed Weil energy.
These identities connect operator, projective, and quantum-metric formulas.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

private theorem inner_self_real_cast (x : ZeroSpace) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  change (‖x‖ : ℂ) ^ 2 = ((‖x‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.ofReal_pow]

/-- The negative-sector projection has expectation equal to its Hilbert mass. -/
theorem inner_negativePart_eq_mass (x : ZeroSpace) :
    inner ℂ x (negativePart x) = (negativeMass x : ℂ) := by
  have h : inner ℂ (positivePart x + negativePart x) (negativePart x) =
      (negativeMass x : ℂ) := by
    rw [inner_add_left, sector_inner_orthogonal, zero_add, inner_self_real_cast]
    rfl
  rwa [positivePart_add_negativePart] at h

/-- The reflection expectation is real and equals the signed Weil energy. -/
theorem inner_reflection_eq_energy (x : ZeroSpace) :
    inner ℂ x (zeroReflection x) = (reflectionEnergy x : ℂ) := by
  rw [← zeroReflection_inner_left, ← sector_inner_difference x x,
    inner_self_real_cast, inner_self_real_cast, reflectionEnergy_eq_mass_difference]
  simp only [positiveMass, negativeMass, Complex.ofReal_sub]

#print axioms inner_negativePart_eq_mass
#print axioms inner_reflection_eq_energy
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
