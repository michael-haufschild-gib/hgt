/-
# Local moments for separated pairs from the three-color decomposition

Every off-diagonal pair produced by the pointwise three-color majorant has
ordered starts separated by one block.  If the family begins at a fixed
multiplicative distance from zero, the arbitrary-base local theorem applies
uniformly to every such pair.
-/
import GaloisForLFunctions.RHTower.BourgainA6LocalBallGeneral
import GaloisForLFunctions.RHTower.BourgainA6PointwiseBilinear

open MeasureTheory

namespace RHTower

noncomputable section

theorem bourgainA6PairLowStart_pos
    {K M q₀ : ℕ} (hq₀ : 0 < q₀) (i j : Fin K) :
    0 < bourgainA6PairLowStart M q₀ i j := by
  unfold bourgainA6PairLowStart
  omega

theorem bourgainA6PairLowStart_ge
    {K M q₀ : ℕ} (i j : Fin K) :
    q₀ ≤ bourgainA6PairLowStart M q₀ i j := by
  unfold bourgainA6PairLowStart
  omega

theorem bourgainA6PairLowStart_mul_lower
    {Λ N K M q₀ : ℕ} (hstart : N ≤ Λ * q₀)
    (i j : Fin K) :
    N ≤ Λ * bourgainA6PairLowStart M q₀ i j := by
  exact hstart.trans
    (Nat.mul_le_mul_left Λ (bourgainA6PairLowStart_ge i j))

/-- Uniform clean local moment for every off-diagonal color pair. -/
theorem setLIntegral_bourgainA6PairLowHigh_localBall_power_of_color
    {ε : ℝ} (hε : 0 < ε) :
    ∀ Λ : ℕ, 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K M q₀ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₀ : 0 < q₀) → (hinside : q₀ + M * K ≤ N) →
        (hstart : N ≤ Λ * q₀) →
      ∀ {c : Fin 3} {i j : Fin K},
        i ∈ bourgainColorBlockFinset K c →
        j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i) →
      ∀ y : BourgainPhaseSpace,
      (∫⁻ x in
        {x : BourgainPhaseSpace |
          ‖x‖ ≤
            bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N M
                (bourgainA6PairLowStart M q₀ i j)
                (fun _ => 1) (x + y)‖ ^ (6 : ℕ) *
            ‖bourgainA6PhysicalBlockSum N M
                (bourgainA6PairHighStart M q₀ i j)
                (fun _ => 1) (x + y)‖ ^ (6 : ℕ))) ≤
        ENNReal.ofReal
          (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  intro Λ hΛ
  obtain ⟨C, hC, hlocal⟩ :=
    setLIntegral_bourgainA6PhysicalBlockSum_localBall_power_of_start
      hε Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro N K M q₀ hN hM hMN hM2N hq₀ hinside hstart
    c i j hi hj y
  have hsep : BourgainSeparatedBlocks i j :=
    separated_of_mem_colorBlock_filter_ne hi hj
  exact hlocal N M
    (bourgainA6PairLowStart M q₀ i j)
    (bourgainA6PairHighStart M q₀ i j)
    hN hM hMN hM2N
    (bourgainA6PairLowStart_pos hq₀ i j)
    (bourgainA6PairLowStart_add_le_highStart hsep)
    (bourgainA6PairHighStart_le hinside)
    (bourgainA6PairLowStart_mul_lower hstart i j) y

end

end RHTower
