import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTailContractive

/-!
# Cuspidal tail estimate on literal source forms

The completed tail estimate specializes definitionally to each cusp-zero
pre-domain field, retaining the exact horizontal derivative coordinate.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The cusp-tail Poincaré estimate for a literal cuspidal form source. -/
theorem cuspidalPreDomain_tail_projection_bound {N : ℕ} {Y : ℝ} (hY : 1 ≤ Y)
    (F : cuspidalFormPreDomain N) :
    ‖cuspTailProjection N Y
        (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ^ (2 : ℕ) ≤
      (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * Y⁻¹ ^ (2 : ℕ) *
        ‖cuspTailProjection N Y
          (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradX F))‖ ^ (2 : ℕ) := by
  have h := cuspidalFormDomain_tail_projection_bound hY
    (toCuspidalFormDomain N F)
  change ‖cuspTailProjection N Y
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ^ (2 : ℕ) ≤
    (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) * Y⁻¹ ^ (2 : ℕ) *
      ‖cuspTailProjection N Y
        (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F))‖ ^ (2 : ℕ) at h
  exact h

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
