import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreChartError

/-!
# Literal core energy bridge for finite-deck Maass fields

Above the positive-height retraction cutoff, the Euclidean grid energies are
exactly the two literal chart derivatives.  This is the local bridge from the
finite-grid Poincaré witness to the invariant modular-strip Dirichlet energy.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Above the retraction cutoff, the finite-deck horizontal coordinate energy
is the literal squared chart derivative. -/
theorem retractedDeckEnergyX_eq_chartDeriv_normSq {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) :
    retractedDeckEnergyX ε F (x, y) =
      ‖chartDeriv (F : ℍ → DeckSpace N) 1
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 := by
  exact sum_retractedDeckComponentX_normSq_eq hε hy F

/-- Above the retraction cutoff, the finite-deck vertical coordinate energy
is the literal squared chart derivative. -/
theorem retractedDeckEnergyY_eq_chartDeriv_normSq {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) :
    retractedDeckEnergyY ε F (x, y) =
      ‖chartDeriv (F : ℍ → DeckSpace N) Complex.I
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 := by
  exact sum_retractedDeckComponentY_normSq_eq hε hy F

/-- The two retracted coordinate energies reconstruct the full chart-gradient
norm square above the cutoff. -/
theorem retractedDeckEnergy_sum_eq_chartGradientNormSq {N : ℕ} {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) (F : formPreDomain N) :
    retractedDeckEnergyX ε F (x, y) + retractedDeckEnergyY ε F (x, y) =
      chartGradientNormSq (F : ℍ → DeckSpace N)
        (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [retractedDeckEnergyX_eq_chartDeriv_normSq hε hy F,
    retractedDeckEnergyY_eq_chartDeriv_normSq hε hy F]
  rfl

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
