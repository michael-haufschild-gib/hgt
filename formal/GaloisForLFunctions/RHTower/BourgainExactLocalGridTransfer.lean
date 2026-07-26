/-
# Exact local moment transfer over an explicit phase-space grid

The uniform translated local sixth-moment estimate sums over the explicit
four-dimensional grid with the exact covering loss `(m + 1)^4`.
-/
import GaloisForLFunctions.RHTower.BourgainExplicitCubeGrid

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Summing the uniform translated local estimate over the explicit product
grid gives a bound on every enlarged physical phase cube, with the exact
four-dimensional covering loss `(m + 1)^4`. -/
theorem setLIntegral_bourgainSquareRootExactLocalSum_bilinear_grid
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a₀ b₀ N D : ℝ},
        (ha₀ : 1 / 2 ≤ a₀) → (ha₀b₀ : a₀ < b₀) →
        (hb₀ : b₀ ≤ 1) → (hN : 0 ≤ N) → (hD : 0 < D) →
      ∀ (H : ℕ), (hH : 0 < H) →
      (hHD : (H : ℝ) ≤ D) → ∀ (c₁ c₂ : Fin H → ℂ)
        (m : ℕ),
      12 * N ≤ (H : ℝ) ^ (2 : ℕ) →
      (∫⁻ x in
        {x : BourgainPhaseSpace |
          ‖x‖ ≤ ((m + 1 : ℕ) : ℝ) * N},
        ENNReal.ofReal
          (‖bourgainSquareRootExactLocalSum H D a₀ c₁ x‖ ^
                (6 : ℕ) *
            ‖bourgainSquareRootExactLocalSum H D b₀ c₂ x‖ ^
              (6 : ℕ))) ≤
        (((m + 1 : ℕ) ^ (4 : ℕ) : ℕ) : ENNReal) *
          ((1024 : ENNReal) *
            (ENNReal.ofReal
                |(3 * (b₀ - a₀) ^ (4 : ℕ) /
                  (32 * a₀ ^ (3 : ℕ) * b₀ ^ (3 : ℕ)))⁻¹| *
              ENNReal.ofReal |(((H : ℝ) / D) ^ (6 : ℕ))⁻¹| *
              ENNReal.ofReal
                ((H : ℝ) ^ (8 : ℕ) *
                  (C * (H : ℝ) ^ ε *
                    (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
                    (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ))) +
              ENNReal.ofReal
                  (bourgainSquareRootBilinearTaylorError
                    N a₀ b₀ ((H : ℝ) / D) c₁ c₂) *
                ENNReal.ofReal ((2 * N) ^ (4 : ℕ)))) := by
  obtain ⟨C, hC, htranslate⟩ :=
    setLIntegral_bourgainSquareRootExactLocalSum_bilinear_translate hε
  refine ⟨C, hC, ?_⟩
  intro a₀ b₀ N D ha₀ ha₀b₀ hb₀ hN hD H hH hHD c₁ c₂ m hphysical
  apply setLIntegral_normCube_le_grid_sum m hN
  intro k
  rw [setLIntegral_bourgainTranslatedNormCube]
  exact
    htranslate ha₀ ha₀b₀ hb₀ hN hD H hH hHD c₁ c₂
      (bourgainGridCenter (m + 1) N k) hphysical

end

end RHTower
