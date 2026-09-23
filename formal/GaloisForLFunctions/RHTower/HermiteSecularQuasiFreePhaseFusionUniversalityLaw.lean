import GaloisForLFunctions.RHTower.HermiteContrastQuasiFreeIncrementUniversalityLaw
import GaloisForLFunctions.RHTower.HermiteContrastSecularEnergyUniversalityLaw

/-!
# Hermite secular/quasi-free phase fusion

The normalized Hilbert contrast energy separately appears as the unique secular coordinate and as
the occupation coordinate controlling quasi-free rank increments.  Identifying those literal
expressions produces one scalar phase variable that governs the secular root, every aperture
adjacent-rung limit, and the mean, variance, and Fano responses of the next Hermite mode.
-/

open Filter

namespace RHTower

noncomputable section

/-- **Hermite secular/quasi-free phase-fusion law.**  One interior contrast coordinate is
simultaneously the unique limiting secular root, the coordinate entering every rescaled
adjacent-rung limit, and the occupation complement determining all three next-rank quasi-free
increments. -/
theorem hermiteContrastSecularEnergy_quasiFreePhaseFusionUniversality (k : ℕ) :
    let E := hermiteContrastSecularEnergyCoordinate k
    let Q := constrainedProlateHermiteWeightSum (k + 1)
    let d : ℝ := 4 * (k + 1)
    E ∈ Set.Ioo (0 : ℝ) 1 ∧
      (∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
        (ladderLimitSecular (constrainedProlateHermiteWeightSum k)
          (constrainedProlateHermiteWeight (k + 1)) x = 0 ↔ x = E)) ∧
      (∀ (A : ℕ → ℝ), (∀ j, 0 < A j) →
        Tendsto (fun lam : ℝ =>
            (ladderTwoModeRoot A (k + 1) lam / ladderTwoModeRoot A k lam) / lam ^ (8 : ℕ))
          atTop (nhds
            ((hermiteContrastSecularEnergyCoordinate (k + 1) / E) *
              (A (k + 2) / A (k + 1))))) ∧
      constrainedProlateHermiteQuasiFreeMean (k + 2) -
          constrainedProlateHermiteQuasiFreeMean (k + 1) = Q * (1 - E) * d ∧
      constrainedProlateHermiteQuasiFreeVariance (k + 2) -
          constrainedProlateHermiteQuasiFreeVariance (k + 1) =
        Q * (1 - E) * (1 - Q * (1 - E)) * d ^ (2 : ℕ) ∧
      constrainedProlateHermiteQuasiFreeFanoMargin (k + 2) -
          constrainedProlateHermiteQuasiFreeFanoMargin (k + 1) =
        Q * (1 - E) * (d - (1 - Q * (1 - E)) * d ^ (2 : ℕ)) := by
  dsimp only
  have hsecular := hermiteContrastSecularEnergyUniversality k
  have hquasi := hermiteContrastSecularEnergy_quasiFreeIncrementUniversality k
  dsimp only at hquasi
  refine ⟨hsecular.1, hsecular.2.1, hsecular.2.2, ?_⟩
  simpa only [hermiteContrastSecularEnergyCoordinate] using hquasi

end

end RHTower
