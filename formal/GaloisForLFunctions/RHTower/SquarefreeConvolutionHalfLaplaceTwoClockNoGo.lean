import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceScheduledNoGo

/-!
# Two-clock Laplace local-boundedness no-go

Pole degree and heat time may be scheduled independently.  Once the pole degree is eventually at
least `24`, local boundedness of the normalized family already bounds the canonical boundary heat
samples.  The arithmetic weighted-mesh escape law then rules out every positive heat clock tending
to zero whose adjacent gaps are eventually `O(τ_(N+1)^(16/11))`.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- One literal convolution-half term damped at an independently chosen heat time. -/
def squarefreeHalfLaplaceTimeTerm (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(((n : ℝ) * t : ℝ) : ℂ)) *
    LSeries.term squarefreeConvolutionHalf s n

/-- Infinite convolution-half heat sum at an independently chosen time. -/
def squarefreeHalfLaplaceTimeSum (t : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, squarefreeHalfLaplaceTimeTerm t s n

/-- The time-scheduled sum at `6/11` is exactly the canonical boundary heat profile. -/
theorem squarefreeHalfLaplaceTimeSum_boundaryExteriorPoint (t : ℝ) :
    squarefreeHalfLaplaceTimeSum t boundaryExteriorPoint =
      squarefreeHalfBoundaryLaplaceProfile t := by
  unfold squarefreeHalfLaplaceTimeSum squarefreeHalfLaplaceTimeTerm
    squarefreeHalfBoundaryLaplaceProfile
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile
    squarefreeHalfBoundaryLaplaceCoeff
  apply tsum_congr
  intro n
  ring

/-- Pole-cleared approximation with independent pole-degree and heat-time clocks. -/
def poleClearedFirstTraceLaplaceTwoClockApprox
    (κ : ℕ → ℕ) (τ : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  poleFactorSqrtApprox (κ N) s * squarefreeHalfLaplaceTimeSum (τ N) s /
    squarefreeCarlemanHalfDet s

/-- Local boundedness interface for the explicit two-clock family. -/
def PoleClearedFirstTraceLaplaceTwoClockLocallyBounded
    (κ : ℕ → ℕ) (τ : ℕ → ℝ) : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R,
      ‖poleClearedFirstTraceLaplaceTwoClockApprox κ τ N w‖ ≤ C

/-- Once the pole clock reaches degree `24`, local boundedness of the normalized two-clock family
forces a uniform bound on all corresponding canonical boundary heat samples. -/
theorem exists_uniform_bound_squarefreeHalfBoundaryLaplaceProfile_twoClockSamples_of_locallyBounded
    {κ : ℕ → ℕ} {τ : ℕ → ℝ}
    (hκ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 24 ≤ κ N)
    (hloc : PoleClearedFirstTraceLaplaceTwoClockLocallyBounded κ τ) :
    ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfBoundaryLaplaceProfile (τ N)‖ ≤ K := by
  obtain ⟨N₀, hκ⟩ := hκ
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceLaplaceTwoClockApprox κ τ N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (poleClearedFirstTraceLaplaceTwoClockApprox κ τ 0 boundaryExteriorPoint)).trans
      (hbound 0)
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨N₀, K, hKnonneg, ?_⟩
  intro N hN
  have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow (hκ N hN)
  have hfactorOne : (1 : ℝ) ≤ ‖poleFactorSqrtApprox (κ N) boundaryExteriorPoint‖ := by
    have hpow : (1 : ℝ) ≤ 5 ^ (κ N - 24) := one_le_pow₀ (by norm_num)
    exact hpow.trans hfactor
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox (κ N) boundaryExteriorPoint‖ *
          ‖squarefreeHalfLaplaceTimeSum (τ N) boundaryExteriorPoint‖ ≤ K := by
    rw [poleClearedFirstTraceLaplaceTwoClockApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  rw [← squarefreeHalfLaplaceTimeSum_boundaryExteriorPoint]
  calc
    ‖squarefreeHalfLaplaceTimeSum (τ N) boundaryExteriorPoint‖ =
        1 * ‖squarefreeHalfLaplaceTimeSum (τ N) boundaryExteriorPoint‖ := by ring
    _ ≤ ‖poleFactorSqrtApprox (κ N) boundaryExteriorPoint‖ *
        ‖squarefreeHalfLaplaceTimeSum (τ N) boundaryExteriorPoint‖ :=
      mul_le_mul_of_nonneg_right hfactorOne (norm_nonneg _)
    _ ≤ K := hprod

/-- **Two-clock dense-schedule no-go.** Independent pole scheduling cannot rescue any positive
heat clock tending to zero with eventually `16/11`-dense adjacent gaps. -/
theorem not_poleClearedFirstTraceLaplaceTwoClockLocallyBounded_of_weightedDense
    (κ : ℕ → ℕ) (τ : ℕ → ℝ)
    (hκ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 24 ≤ κ N)
    (hpos : ∀ N : ℕ, 0 < τ N)
    (htend : Tendsto τ atTop (𝓝 0))
    (hdense : ∃ N₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, N₀ ≤ N →
      |τ N - τ (N + 1)| ≤ C * (τ (N + 1)) ^ (16 / 11 : ℝ)) :
    ¬ PoleClearedFirstTraceLaplaceTwoClockLocallyBounded κ τ := by
  intro hloc
  obtain ⟨N₁, K, hK, hsamples⟩ :=
    exists_uniform_bound_squarefreeHalfBoundaryLaplaceProfile_twoClockSamples_of_locallyBounded
      hκ hloc
  obtain ⟨N₂, C, hC, hgaps⟩ := hdense
  apply not_exists_bounded_samples_and_weighted_dense_gaps_of_tendsto_zero τ hpos htend
  refine ⟨max N₁ N₂, C, K, hC, hK, ?_, ?_⟩
  · intro N hN
    exact hsamples N ((le_max_left N₁ N₂).trans hN)
  · intro N hN
    exact hgaps N ((le_max_right N₁ N₂).trans hN)

end

end RHTower
