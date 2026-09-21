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
        (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ^ 2 ≤
      (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) * Y⁻¹ ^ 2 *
        ‖cuspTailProjection N Y
          (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
            (cuspidalFormPreDomain.memLp_gradX F))‖ ^ 2 := by
  have h := cuspidalFormDomain_tail_projection_bound hY
    (toCuspidalFormDomain N F)
  change ‖cuspTailProjection N Y
      (toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F))‖ ^ 2 ≤
    (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) * Y⁻¹ ^ 2 *
      ‖cuspTailProjection N Y
        (toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (cuspidalFormPreDomain.memLp_gradX F))‖ ^ 2 at h
  exact h

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
