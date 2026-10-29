import GaloisForLFunctions.TransMetzlerWeilPositivity.OptimizedTransMetzlerFloor
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates

/-!
# Complete Weil positivity in polynomial length and spectral height

Inverse width is a coordinate of the actual normalized complete matrix, including
its prime, Gamma, and polar terms. Every fixed overlap `0<c<1+δ_*` gives eventual
positivity along `T=N/c`. The horizon in this statement may depend on `c`.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis
  SpacingScaleHarmonicAnalysis.LengthHeight RenormalizedArithmeticPotentialTheory

/-- The literal complete Weil matrix, with width specified by inverse spectral height. -/
def completeWeilMatrixAtHeight (φ : ℝ → ℝ) (N : ℕ) (T : ℝ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  normalizedFullWeilHorizonMatrix (atomDilate φ T⁻¹) N

theorem completeWeilMatrixAtHeight_height (φ : ℝ → ℝ) (N : ℕ) (c : ℝ) :
    completeWeilMatrixAtHeight φ N (height N c) = completeWeilMatrix φ c N := by
  rw [completeWeilMatrixAtHeight, inv_height]
  rfl

/-- The full certified range, including separated overlaps, retains the actual complete form. -/
theorem eventually_completeWeilMatrixAtHeight_posDef {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 + certifiedOverlapIncrement) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilMatrixAtHeight transMetzlerProfile N (height N c)).PosDef := by
  simp only [completeWeilMatrixAtHeight_height]
  by_cases hc1 : c ≤ 1
  · exact eventually_completeWeilMatrix_posDef_of_mem_Ioc
      ⟨hc0, hc1.trans one_lt_cZero.le⟩
  · have hδ0 : 0 ≤ c - 1 := sub_nonneg.mpr (not_le.mp hc1).le
    have hδ : c - 1 < certifiedOverlapIncrement := by linarith only [hc]
    have h := eventually_completeWeilMatrix_posDef_certified (c - 1) hδ0 hδ
    simpa only [show 1 + (c - 1) = c by ring] using h

/-- The certified mass floor transports unchanged to length-height coordinates. -/
theorem eventually_completeWeilMatrixAtHeight_floor (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ certifiedOverlapIncrement) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (certifiedOverlapFloor δ - ε) * ‖x‖ ^ 2 ≤
        ⟪Matrix.toEuclideanLin
          (completeWeilMatrixAtHeight transMetzlerProfile N (height N (1 + δ))) x, x⟫ := by
  simpa only [completeWeilMatrixAtHeight_height] using
    eventually_completeWeilMatrix_certified_floor δ hδ0 hδ ε hε

/-- The certified excess is a linear length excess, not a fixed excess bandwidth. -/
theorem certified_overlap_iff_length_bound {X T : ℝ} (hT : 0 < T) :
    overlap X T < 1 + certifiedOverlapIncrement ↔
      X < (1 + certifiedOverlapIncrement) * T :=
  div_lt_iff₀ hT

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrixAtHeight_posDef
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrixAtHeight_floor
