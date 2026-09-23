import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceRemainderLiteralJet

/-! The actual source remainder inherits the literal three-counterterm jet. -/

namespace RHTower.D4BMLaplaceRadial
open Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The true source remainder has all three literal endpoint counterterms on
one frequency ball.  This is F390 transported through `α = 2s - w`. -/
theorem exists_sourceRemainder_uniformJet3 (s w a J K T : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasUniformJet3 (closedBall w 1) (1 / 2)
        (fun u z => sourceRemainder s u a J K T z)
        (fun u => literalSourceHorizonPower (2 * s - u) 0 *
          (((5 * s ^ (2 : ℕ) + 15 * s + 4) / 4) * J +
            s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) * (a ^ (2 : ℕ) * T))
        (fun u => literalSourceHorizonPower (2 * s - u) 0 *
          (-((2 * s - u) *
            (((5 * s ^ (2 : ℕ) + 15 * s + 4) / 4) * J +
              s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) / 4) -
            s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) * (a ^ (2 : ℕ) * T))
        (fun u => literalSourceHorizonPower (2 * s - u) 0 *
          ((2 * s - u) * ((2 * s - u) - 3) *
              (((5 * s ^ (2 : ℕ) + 15 * s + 4) / 4) * J +
                s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) / 32 +
            (2 * s - u) * (s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)) / 4) *
            (a ^ (2 : ℕ) * T)) C := by
  let B₀ : ℂ := ((5 * s ^ (2 : ℕ) + 15 * s + 4) / 4) * J +
    s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)
  let B₁ : ℂ := s * (s - 1) / 4 * ((s + 2) ^ (2 : ℕ) * J - K)
  obtain ⟨C, hC, hsource⟩ := exists_literalSourceAffinePower_uniformJet3 (2 * s - w) B₀ B₁
  have hscaled := hsource.const_mul (a ^ (2 : ℕ) * T)
  refine ⟨‖a ^ (2 : ℕ) * T‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro u hu z hz
  have hu' : 2 * s - u ∈ closedBall (2 * s - w) 1 := by
    rw [mem_closedBall] at hu ⊢
    calc
      dist (2 * s - u) (2 * s - w) = ‖w - u‖ := by
        rw [dist_eq_norm]
        congr 1
        ring
      _ = ‖-(u - w)‖ := by
        congr 1
        ring
      _ = ‖u - w‖ := norm_neg _
      _ = dist u w := by rw [dist_eq_norm]
      _ ≤ 1 := hu
  have h := hscaled (2 * s - u) hu' z hz
  change ‖sourceRemainder s u a J K T z -
      literalSourceHorizonPower (2 * s - u) 0 * B₀ * (a ^ (2 : ℕ) * T) -
      (literalSourceHorizonPower (2 * s - u) 0 *
        (-((2 * s - u) * B₀ / 4) - B₁) * (a ^ (2 : ℕ) * T)) * z -
      (literalSourceHorizonPower (2 * s - u) 0 *
        ((2 * s - u) * ((2 * s - u) - 3) * B₀ / 32 +
          (2 * s - u) * B₁ / 4) * (a ^ (2 : ℕ) * T)) * z ^ (2 : ℕ)‖ ≤
        ‖a ^ (2 : ℕ) * T‖ * C * z ^ (3 : ℕ)
  rw [sourceRemainder_eq_literalSourceAffinePower]
  dsimp only [B₀, B₁] at h ⊢
  convert h using 1
  all_goals ring_nf

end
end RHTower.D4BMLaplaceRadial
