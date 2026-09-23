/-
# Explicit grid summation of the local `A₆` power bound

The uniform translated radius-`M² / 12` estimate sums over the explicit
four-dimensional product grid with exactly `(m+1)^(4 : ℕ)` cells.
-/
import GaloisForLFunctions.RHTower.BourgainA6LocalBallPowerBound
import GaloisForLFunctions.RHTower.BourgainExplicitCubeGrid

open MeasureTheory

namespace RHTower

noncomputable section

/-- Coarse but unconditional grid sum of the clean local-ball estimate. -/
theorem setLIntegral_bourgainA6PhysicalBlockSum_localBall_grid_power
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M q₁ q₂ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₁ : 0 < q₁) → (hq : q₁ + M ≤ q₂) →
        (hq₂N : q₂ ≤ N) →
        (ha : (1 / 2 : ℝ) ≤ Real.sqrt ((q₁ : ℝ) / (N : ℝ))) →
      ∀ m : ℕ,
      let R : ℝ := (M : ℝ) ^ (2 : ℕ) / 12
      (∫⁻ x in
        {x : BourgainPhaseSpace |
          ‖x‖ ≤ ((m + 1 : ℕ) : ℝ) * R},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) x‖ ^
                (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) x‖ ^
              (6 : ℕ))) ≤
        (((m + 1 : ℕ) ^ (4 : ℕ) : ℕ) : ENNReal) *
          ENNReal.ofReal
            (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  obtain ⟨C, hC, hlocal⟩ :=
    setLIntegral_bourgainA6PhysicalBlockSum_localBall_power hε
  refine ⟨C, hC, ?_⟩
  intro N M q₁ q₂ hN hM hMN hM2N hq₁ hq hq₂N ha m
  dsimp only
  let R : ℝ := (M : ℝ) ^ (2 : ℕ) / 12
  let f : BourgainPhaseSpace → ENNReal := fun x =>
    ENNReal.ofReal
      (‖bourgainA6PhysicalBlockSum N M q₁ (fun _ => 1) x‖ ^
            (6 : ℕ) *
        ‖bourgainA6PhysicalBlockSum N M q₂ (fun _ => 1) x‖ ^
          (6 : ℕ))
  apply setLIntegral_normCube_le_grid_sum m (by positivity : 0 ≤ R)
  intro k
  rw [setLIntegral_bourgainTranslatedNormCube]
  exact hlocal N M q₁ q₂ hN hM hMN hM2N hq₁ hq hq₂N ha
    (bourgainGridCenter (m + 1) R k)

end

end RHTower
