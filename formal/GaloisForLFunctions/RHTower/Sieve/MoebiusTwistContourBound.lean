import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistConcreteEdges

/-!
# The twisted contour bound at the concrete rectangle

Substituting the concrete geometry into the twisted four-edge inequality gives an unconditional
bound for the twisted smoothed Möbius sum in which every quantity is an explicit function of the
arithmetic parameter `K`, with the same constants as the untwisted bound.  The truncation height is
`twistHeight K τ = truncHeight K - |τ|`, so the twisted contour occupies the same band, and the side
condition `5 + 4|τ| ≤ K` keeps the horizontal edges away from the real axis.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- **The twisted contour bound.**  Unconditional: for all large `K`, and every twist with
`5 + 4|τ| ≤ K`, the twisted smoothed Möbius sum is bounded by the three edge contributions at the
concrete rectangle, with the same constants as the untwisted bound. -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le_concrete {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (j : ℕ) :
    ∃ (C M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K → 5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K * C) / twistHeight K τ
            + invZetaEdgeBound K * C / (twistHeight K τ) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * C / (twistHeight K τ) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) + 2 * C) := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_tsum_moebiusTwist_smoothWeight_le hN hH j 2
  obtain ⟨δ₁, hδ₁, hzfbox⟩ := exists_zero_free_box 1
  obtain ⟨δ₂, hδ₂, M₀, hM₀, hbdbox⟩ := exists_bound_invZeta_low_box 2 (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log n) ^ (9 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 3
  have h2 : ∀ᶠ n : ℕ in atTop,
      zeroFreeConst / (16 * min δ₁ δ₂) ≤ (Real.log n) ^ (9 : ℕ) := hpow.eventually_ge_atTop _
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨C, M₀, max K₁ 5, hC, hM₀, fun τ K hKle hKτ => ?_⟩
  obtain ⟨hlogK, hfitpow⟩ := hK₁ K (le_trans (le_max_left _ _) hKle)
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hK2 : 2 ≤ K := by omega
  have hδ0 : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hL9 := twentySeven_le_log_pow hlogK
  have hfit : zeroFreeConst / (16 * (Real.log K) ^ (9 : ℕ)) ≤ min δ₁ δ₂ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hfitpow
    linarith
  have hT1 : 1 ≤ twistHeight K τ := one_le_twistHeight hKτ
  have hzf := zero_free_twist_rect (τ := τ) hlogK hK2
    (fun s h1' h2' h3' h4' => hzfbox s (by linarith [min_le_left δ₁ δ₂]) h2' h3' h4')
    (le_trans hfit (min_le_left _ _)) hKτ
  exact hmain τ (leftAbscissa K) (rightAbscissa K) (twistHeight K τ) (invZetaRightBound K)
    (invZetaEdgeBound K) (max M₀ (invZetaEdgeBound K))
    (one_lt_rightAbscissa hlogK) (rightAbscissa_le_two hlogK) (leftAbscissa_pos hlogK)
    (leftAbscissa_le_rightAbscissa hlogK) hT1
    (invZetaRightBound_nonneg K) (invZetaEdgeBound_nonneg K)
    (le_trans hM₀ (le_max_left _ _)) hzf
    (norm_invZetaTwist_right_le hlogK τ)
    (norm_invZetaTwist_top_le hlogK hK2 hKτ)
    (norm_invZetaTwist_bot_le hlogK hK2 hKτ)
    (norm_invZetaTwist_left_le hlogK hK2
      (fun s h1' h2' h3' => hbdbox s (by linarith [min_le_right δ₁ δ₂]) h2' h3') hfit)
    (continuousOn_invZetaTwist_left_line τ (by linarith) (leftAbscissa_le_one hlogK)
      (le_of_lt (one_lt_rightAbscissa hlogK)) hzf)

end RHTower.Sieve
