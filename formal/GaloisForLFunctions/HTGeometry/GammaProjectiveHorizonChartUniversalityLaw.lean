import GaloisForLFunctions.HTGeometry.GammaProjectiveLawDiscriminant
import GaloisForLFunctions.HTGeometry.GammaUniversalProjectiveHorizon

/-!
# Actual-Gamma charts of the universal projective horizon

The actual Gamma observation has one projective differential-dependence hyperplane.  The universal
Gamma shift field has a countable pole arrangement.  An explicit shear chart identifies every
component of that arrangement with the actual Gamma hyperplane, so the complete universal
independence phase is exactly simultaneous avoidance of all actual-Gamma chart pullbacks.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- The `m`-th pole chart: its longitudinal coordinate is the `m`-th Gamma projective character. -/
def gammaProjectiveHorizonChart (m : ℕ) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun A := (gammaProjectiveCharacter m A, A.1)
  map_add' A B := by
    ext
    all_goals simp [gammaProjectiveCharacter]
    all_goals ring
  map_smul' c A := by
    ext <;> simp [gammaProjectiveCharacter]

@[simp]
theorem gammaProjectiveHorizonChart_fst (m : ℕ) (A : ℂ × ℂ) :
    (gammaProjectiveHorizonChart m A).1 = gammaProjectiveCharacter m A := rfl

/-- Every universal pole component is the pullback of the actual Gamma differential horizon in
its corresponding shear chart. -/
theorem gammaProjectiveHorizonChart_mem_directionalDependence_iff
    (m : ℕ) (A : ℂ × ℂ) :
    gammaProjectiveHorizonChart m A ∈ gammaDirectionalDependenceSet ↔
      gammaProjectiveCharacter m A = 0 := by
  rw [gammaDirectionalDependenceSet_eq_longitudinalKernel]
  rfl

/-- A homogeneous reciprocal-Gamma pole law enters exactly its matching actual-Gamma chart
horizon and no other one. -/
theorem gammaPoleLaw_chart_directionalDependence_iff (m n : ℕ) :
    gammaProjectiveHorizonChart m (gammaPoleLaw n) ∈ gammaDirectionalDependenceSet ↔
      m = n := by
  rw [gammaProjectiveHorizonChart_mem_directionalDependence_iff,
    gammaProjectiveCharacter_gammaPoleLaw_eq_zero_iff]

/-- The complete countable Gamma arrangement is the union of explicit pullbacks of the one actual
Gamma dependence horizon. -/
theorem gammaProjectiveHorizon_eq_actualGammaChartPullbacks :
    gammaProjectiveHorizon =
      {A : ℂ × ℂ | ∃ m : ℕ,
        gammaProjectiveHorizonChart m A ∈ gammaDirectionalDependenceSet} := by
  ext A
  simp only [gammaProjectiveHorizon, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (gammaProjectiveHorizonChart_mem_directionalDependence_iff m A).2 hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (gammaProjectiveHorizonChart_mem_directionalDependence_iff m A).1 hm⟩

/-- **Actual-to-universal Gamma horizon law.**  The complete universal Gamma-sector jet is
algebraically independent exactly when every explicit pole chart lies in the hypertranscendental
phase of the actual Gamma observation. -/
theorem universalGammaShift_completeJet_algebraicIndependent_iff_all_actualGammaCharts
    (A : ℂ × ℂ) :
    AlgebraicIndependent ℂ
        (fun p : ℕ × ℕ ↦
          selectedDerivationJet
              (universalWeightedShiftDerivation gammaProjectiveCharacter A) p.2
            (universalShiftAncestor (K := ℂ) 0 p.1)) ↔
      ∀ m : ℕ,
        gammaProjectiveHorizonChart m A ∉ gammaDirectionalDependenceSet := by
  rw [universalGammaShift_completeJet_algebraicIndependent_iff]
  rw [gammaProjectiveHorizon_eq_actualGammaChartPullbacks]
  simp

end

end GaloisForLFunctions.HTGeometry
