import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleBoundaryPrimitives
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit

/-!
# Eventual positive trace of the literal CCM pole matrix

The actual CCM pole diagonal has the same one-sided Gamma boundary primitive as the
exponential-pole diagonal whose sharp asymptotic is already formalized.  This transfers its
positive genus limit to the literal CCM matrix.  Consequently the large-aperture two-pole
compression cannot have two negative parity energies: once its determinant wall is crossed,
exactly one parity is negative.

This is a trace law only.  It neither controls the off-diagonal entry nor proves the
RH-equivalent determinant inequality.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The actual CCM and exponential-pole self-boundary primitives are definitionally the same
one-sided Gamma integral. -/
theorem ccmGammaPoleSelfBoundaryPrimitive_eq_poleSelfBoundaryPrimitive (s : ℝ) :
    ccmGammaPoleSelfBoundaryPrimitive s = poleSelfBoundaryPrimitive s := by
  rfl

/-- The literal CCM pole diagonal is the sharp exponential-pole diagonal at the same aperture. -/
theorem ccmWeilPoleDiagonal_eq_poleDiagonalExplicit (a : SuzukiPositiveAperture) :
    ccmWeilPoleDiagonal a = poleDiagonalExplicit a.1 := by
  rw [ccmWeilPoleDiagonal_eq_error,
    ccmGammaPoleSelfBoundaryMass_eq_primitive,
    ccmGammaPoleSelfBoundaryPrimitive_eq_poleSelfBoundaryPrimitive]
  rfl

/-- **Eventual positive trace.**  The trace coordinate of the literal CCM two-pole matrix is
strictly positive beyond one unconditional aperture threshold. -/
theorem exists_eventually_ccmWeilPoleDiagonal_pos :
    ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      0 < ccmWeilPoleDiagonal a := by
  obtain ⟨A, hA⟩ := eventually_atTop.1 eventually_poleDiagonalExplicit_pos
  refine ⟨A, fun a ha => ?_⟩
  rw [ccmWeilPoleDiagonal_eq_poleDiagonalExplicit]
  exact hA a.1 ha

/-- Above the positive-trace threshold, a strict pole-compression wall crossing has one and only
one negative parity energy.  The other parity remains strictly positive. -/
theorem ccmWeilPoleCompression_parity_opposite_sign_of_diagonal_pos_of_cross_exceeds
    (a : SuzukiPositiveAperture)
    (hdiag : 0 < ccmWeilPoleDiagonal a)
    (hcross : ccmWeilPoleDiagonal a < |ccmWeilPoleCross a|) :
    (ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) < 0 ∧
      0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ∨
    (0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) < 0) := by
  rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl),
    ccmWeilPoleCompression_parity_energy a (Or.inr rfl)]
  rcases le_total 0 (ccmWeilPoleCross a) with hnonneg | hnonpos
  · right
    rw [abs_of_nonneg hnonneg] at hcross
    constructor <;> nlinarith
  · left
    rw [abs_of_nonpos hnonpos] at hcross
    constructor <;> nlinarith

end

end RHTower
