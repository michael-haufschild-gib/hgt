import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGridRelative

/-!
# Closed finite-grid approximation cones

A homogeneous distance-to-grid estimate is stable under completion of the
three-coordinate cuspidal form domain.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The relative distance to a fixed finite grid space is a closed condition on
completed form triples. -/
theorem isClosed_infDist_le_sqrt_formBudget {N : ℕ} (V : Set (DeckL2 N))
    (A B : ℝ) :
    IsClosed {w : FormTriple N |
      Metric.infDist (w.ofLp 0) V ≤
        Real.sqrt (A * ‖w‖ ^ (2 : ℕ)) + Real.sqrt (B * ‖w‖ ^ (2 : ℕ))} := by
  apply isClosed_le
  · exact (Metric.continuous_infDist_pt V).comp
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => DeckL2 N) 0).continuous
  · exact (Real.continuous_sqrt.comp
      (continuous_const.mul (continuous_norm.pow 2))).add
        (Real.continuous_sqrt.comp
          (continuous_const.mul (continuous_norm.pow 2)))

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
