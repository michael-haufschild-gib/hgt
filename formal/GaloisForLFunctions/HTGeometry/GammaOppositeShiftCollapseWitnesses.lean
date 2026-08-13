import GaloisForLFunctions.HTGeometry.GammaPhaseTimeIntensityFieldSeparationUniversalityLaw

/-!
# Unconditional witnesses for opposite-shift Gamma intensity collapse

The exact collapse locus is already classified by
`differentialAlgebraicOver_gammaOppositeShiftIntensityMero_iff_collapse`.  These constructors expose
both components of that universal law directly through the `GammaOppositeShiftIntensityCollapse`
interface, including pointwise families used by atlas theorems.
-/

namespace GaloisForLFunctions

/-- Integer-separated shifts lie on the relative-diagonal collapse component. -/
theorem gammaOppositeShiftIntensityCollapse_add_int (a : ℂ) (n : ℤ) :
    GammaOppositeShiftIntensityCollapse a (a + (n : ℂ)) := by
  left
  exact ⟨n, by ring⟩

/-- Equal shifts are an unconditional collapse witness. -/
theorem gammaOppositeShiftIntensityCollapse_self (a : ℂ) :
    GammaOppositeShiftIntensityCollapse a a := by
  simpa using gammaOppositeShiftIntensityCollapse_add_int a 0

/-- Two thermal half-lattice shifts lie on the absolute collapse component. -/
theorem gammaOppositeShiftIntensityCollapse_halfIntegerWeights (m n : ℤ) :
    GammaOppositeShiftIntensityCollapse
      ((1 - (m : ℂ)) / 2) ((1 - (n : ℂ)) / 2) := by
  right
  constructor
  · exact ⟨m, by ring⟩
  · exact ⟨n, by ring⟩

/-- Every pointwise integer translate family satisfies the atlas collapse premise. -/
theorem gammaOppositeShiftIntensityCollapse_family_add_int
    {ι : Type*} (a : ι → ℂ) (n : ι → ℤ) :
    ∀ i, GammaOppositeShiftIntensityCollapse (a i) (a i + (n i : ℂ)) :=
  fun i => gammaOppositeShiftIntensityCollapse_add_int (a i) (n i)

/-- Every equal-shift family satisfies the atlas collapse premise. -/
theorem gammaOppositeShiftIntensityCollapse_family_self
    {ι : Type*} (a : ι → ℂ) :
    ∀ i, GammaOppositeShiftIntensityCollapse (a i) (a i) :=
  fun i => gammaOppositeShiftIntensityCollapse_self (a i)

end GaloisForLFunctions
