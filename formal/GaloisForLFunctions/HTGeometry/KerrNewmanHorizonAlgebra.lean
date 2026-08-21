import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Kerr--Newman horizon polynomial algebra

The Boyer--Lindquist metric and stationary Killing block use the standard radial polynomial
`Delta = r² - 2 M r + a² + Q²`.  This file gives closed complete-square, zero-locus, and
extremality laws and transports the extremality factor to the existing cleared Killing-block
determinant identity.

These are algebraic horizon diagnostics.  They do not establish global causal properties or a
curved Einstein--Maxwell solution.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The Kerr--Newman radial polynomial is centered at the mass parameter. -/
theorem kerrNewmanDelta_completeSquare
    (mass spin charge radius : ℝ) :
    kerrNewmanDelta mass spin charge radius =
      (radius - mass) ^ 2 - (mass ^ 2 - spin ^ 2 - charge ^ 2) := by
  simp [kerrNewmanDelta]
  ring

/-- A radial coordinate lies on the algebraic horizon locus exactly when its mass-centered
square is the Kerr--Newman discriminant. -/
theorem kerrNewmanDelta_zero_iff
    (mass spin charge radius : ℝ) :
    kerrNewmanDelta mass spin charge radius = 0 ↔
      (radius - mass) ^ 2 = mass ^ 2 - spin ^ 2 - charge ^ 2 := by
  rw [kerrNewmanDelta_completeSquare]
  exact sub_eq_zero

/-- The mass-centered radius is an algebraic horizon exactly at Kerr--Newman extremality. -/
theorem kerrNewmanDelta_at_mass_zero_iff_extremal
    (mass spin charge : ℝ) :
    kerrNewmanDelta mass spin charge mass = 0 ↔ mass ^ 2 = spin ^ 2 + charge ^ 2 := by
  rw [kerrNewmanDelta_completeSquare]
  constructor <;> intro h <;> nlinarith

/-- Extremality is exactly the condition that the whole radial polynomial becomes a perfect
square, so its algebraic horizon has multiplicity two at `r = M`. -/
theorem kerrNewmanDelta_extremal_iff_perfectSquare
    (mass spin charge : ℝ) :
    (∀ radius, kerrNewmanDelta mass spin charge radius = (radius - mass) ^ 2) ↔
      mass ^ 2 = spin ^ 2 + charge ^ 2 := by
  constructor
  · intro h
    have hmass := h mass
    rw [kerrNewmanDelta] at hmass
    norm_num at hmass
    nlinarith
  · intro h radius
    rw [kerrNewmanDelta_completeSquare]
    nlinarith

/-- At `r = M`, the existing denominator-cleared Killing-block determinant displays the same
extremality factor.  This remains valid at coordinate-singular values because the identity is
cleared. -/
theorem kerrNewmanKillingBlock_det_cleared_at_mass
    (mass spin charge polar : ℝ) :
    kerrNewmanSigma spin mass polar ^ 2 *
        (kerrNewmanKillingBlock mass spin charge mass polar).det =
      -(spin ^ 2 + charge ^ 2 - mass ^ 2) * Real.sin polar ^ 2 *
        kerrNewmanSigma spin mass polar ^ 2 := by
  rw [kerrNewmanKillingBlock_det_cleared]
  have hdelta : kerrNewmanDelta mass spin charge mass =
      spin ^ 2 + charge ^ 2 - mass ^ 2 := by
    simp [kerrNewmanDelta]
    ring
  rw [hdelta]

/-- A one-pole unipotent BZ dressing preserves the exact Kerr--Newman extremality factor in the
cleared stationary-block determinant. -/
theorem belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det_cleared_at_mass
    (spectral pole residue mass spin charge polar : ℝ) :
    kerrNewmanSigma spin mass polar ^ 2 *
        (belinskiZakharovDressing (belinskiZakharovOnePoleDressing spectral pole residue)
          (kerrNewmanKillingBlock mass spin charge mass polar)).det =
      -(spin ^ 2 + charge ^ 2 - mass ^ 2) * Real.sin polar ^ 2 *
        kerrNewmanSigma spin mass polar ^ 2 := by
  rw [belinskiZakharovOnePoleDressedKerrNewmanKillingBlock_det_cleared]
  have hdelta : kerrNewmanDelta mass spin charge mass =
      spin ^ 2 + charge ^ 2 - mass ^ 2 := by
    simp [kerrNewmanDelta]
    ring
  rw [hdelta]

/-- The same extremality factor is preserved by every constant unipotent BZ dressing. -/
theorem belinskiZakharovDressedKerrNewmanKillingBlock_det_cleared_at_mass
    (parameter mass spin charge polar : ℝ) :
    kerrNewmanSigma spin mass polar ^ 2 *
        (belinskiZakharovDressing (belinskiZakharovUnipotentDressing parameter)
          (kerrNewmanKillingBlock mass spin charge mass polar)).det =
      -(spin ^ 2 + charge ^ 2 - mass ^ 2) * Real.sin polar ^ 2 *
        kerrNewmanSigma spin mass polar ^ 2 := by
  rw [belinskiZakharovDressedKerrNewmanKillingBlock_det_cleared]
  have hdelta : kerrNewmanDelta mass spin charge mass =
      spin ^ 2 + charge ^ 2 - mass ^ 2 := by
    simp [kerrNewmanDelta]
    ring
  rw [hdelta]

end GaloisForLFunctions.HTGeometry
