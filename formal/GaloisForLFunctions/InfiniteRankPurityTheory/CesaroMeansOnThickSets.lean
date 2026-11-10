import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansReadTheModesOfASummableTower

/-!
# Cesàro means on thick sets

The weight of a summable tower at a point `w` of the unit circle is read on any set of levels that
contains arbitrarily long runs arbitrarily far out. The mean of `S(ν) w^{−ν}` over a window
`N < ν ≤ N + L` differs from the weight at `w` by

* a term from the other modes on the circle, small when the window is long, uniformly in its
  position (the mean of a geometric sequence of ratio `r ≠ 1`, `‖r‖ = 1`, is `O(1/L)`);
* a term from the modes inside the disc, small when the window is far out, uniformly in its length

(`norm_windowMean_sub_le`). Hence level sums that tend to zero along a thick set carry no weight on
the unit circle (`merged_eq_zero_of_small_on_runs`).
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-- The mean of the geometric sequence `1, r, …, r^{L−1}`. -/
noncomputable def geomMean (r : ℂ) (L : ℕ) : ℂ := (∑ j ∈ range L, r ^ j) / (L : ℂ)

/-- The mean of `S(ν) w^{−ν}` over the window `N < ν ≤ N + L`. -/
noncomputable def windowMean (c z : ι → ℂ) (w : ℂ) (N L : ℕ) : ℂ :=
  (∑ j ∈ range L, towerSum c z (N + 1 + j) * w⁻¹ ^ (N + 1 + j)) / (L : ℂ)

/-- The contribution of the modes on the circle other than `w`. -/
noncomputable def circleError (c z : ι → ℂ) (w : ℂ) (L : ℕ) (i : ι) : ℝ :=
  ‖c i‖ * (if z i = w then 0 else if ‖z i‖ = 1 then ‖geomMean (z i * w⁻¹) L‖ else 0)

/-- The contribution of the modes inside the disc. -/
noncomputable def innerError (c z : ι → ℂ) (N : ℕ) (i : ι) : ℝ :=
  ‖c i‖ * (if ‖z i‖ = 1 then 0 else ‖z i‖ ^ (N + 1))

theorem norm_geomMean_le_one' {r : ℂ} (hr : ‖r‖ ≤ 1) (L : ℕ) : ‖geomMean r L‖ ≤ 1 :=
  norm_geomMean_le_one hr L

theorem windowMean_eq {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) (hz : ∀ i, ‖z i‖ ≤ 1)
    {w : ℂ} (hw : ‖w‖ = 1) (N L : ℕ) :
    windowMean c z w N L =
      ∑' i, c i * (z i * w⁻¹) ^ (N + 1) * geomMean (z i * w⁻¹) L := by
  have hzw : ∀ i, ‖z i * w⁻¹‖ ≤ 1 := by
    intro i
    rw [norm_mul, norm_inv, hw, inv_one, mul_one]
    exact hz i
  have h1 : ∀ j ∈ range L, towerSum c z (N + 1 + j) * w⁻¹ ^ (N + 1 + j) =
      ∑' i, c i * (z i * w⁻¹) ^ (N + 1) * (z i * w⁻¹) ^ j := by
    intro j _
    rw [towerSum, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [mul_pow, mul_pow, pow_add, pow_add]
    ring
  have hsum : ∀ j ∈ range L,
      Summable fun i => c i * (z i * w⁻¹) ^ (N + 1) * (z i * w⁻¹) ^ j := by
    intro j _
    refine Summable.of_norm_bounded hc fun i => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖c i‖ * ‖z i * w⁻¹‖ ^ (N + 1) * ‖z i * w⁻¹‖ ^ j ≤ ‖c i‖ * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) (hzw i)
          · exact pow_le_one₀ (norm_nonneg _) (hzw i)
      _ = ‖c i‖ := by ring
  rw [windowMean, Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum hsum, ← tsum_div_const]
  refine tsum_congr fun i => ?_
  rw [geomMean, ← Finset.mul_sum, mul_div_assoc]

/-- **The window mean reads the weight at `w`** up to the two error terms. -/
theorem norm_windowMean_sub_le {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) {w : ℂ} (hw : ‖w‖ = 1) (N : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ‖windowMean c z w N L - ∑' i, (if z i = w then c i else 0)‖ ≤
      (∑' i, circleError c z w L i) + ∑' i, innerError c z N i := by
  classical
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hL)
  have hzw : ∀ i, ‖z i * w⁻¹‖ ≤ 1 := by
    intro i
    rw [norm_mul, norm_inv, hw, inv_one, mul_one]
    exact hz i
  have hzwn : ∀ i, ‖z i * w⁻¹‖ = ‖z i‖ := by
    intro i
    rw [norm_mul, norm_inv, hw, inv_one, mul_one]
  -- summability of the pieces
  have hT : Summable fun i => c i * (z i * w⁻¹) ^ (N + 1) * geomMean (z i * w⁻¹) L := by
    refine Summable.of_norm_bounded hc fun i => ?_
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖c i‖ * ‖z i * w⁻¹‖ ^ (N + 1) * ‖geomMean (z i * w⁻¹) L‖ ≤ ‖c i‖ * 1 * 1 := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg _) (hzw i)
          · exact norm_geomMean_le_one (hzw i) L
      _ = ‖c i‖ := by ring
  have hm : Summable fun i => (if z i = w then c i else 0 : ℂ) :=
    Summable.of_norm_bounded hc fun i => by split_ifs <;> simp
  have hA : Summable fun i => circleError c z w L i := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hc
    · unfold circleError
      split_ifs <;> positivity
    · unfold circleError
      split_ifs
      · simp
      · exact mul_le_of_le_one_right (norm_nonneg _) (norm_geomMean_le_one (hzw i) L)
      · simp
  have hB : Summable fun i => innerError c z N i := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hc
    · unfold innerError
      split_ifs <;> positivity
    · unfold innerError
      split_ifs
      · simp
      · exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz i))
  rw [windowMean_eq hc hz hw, ← hT.tsum_sub hm, ← hA.tsum_add hB]
  refine tsum_of_norm_bounded (hA.add hB).hasSum fun i => ?_
  unfold circleError innerError
  by_cases h1 : z i = w
  · -- the mode `w` itself contributes exactly its weight
    have hr : z i * w⁻¹ = 1 := by rw [h1, mul_inv_cancel₀ hw0]
    have hg : geomMean (1 : ℂ) L = 1 := by
      rw [geomMean]
      simp [div_self hL0]
    have hn : ‖z i‖ = 1 := by rw [h1, hw]
    rw [if_pos h1, if_pos h1, if_pos hn, hr, hg]
    simp
  · rw [if_neg h1, if_neg h1, sub_zero, norm_mul, norm_mul, norm_pow, hzwn i]
    by_cases h2 : ‖z i‖ = 1
    · rw [if_pos h2, if_pos h2, h2, one_pow, mul_one, mul_zero, add_zero]
    · rw [if_neg h2, if_neg h2, mul_zero, zero_add]
      calc ‖c i‖ * ‖z i‖ ^ (N + 1) * ‖geomMean (z i * w⁻¹) L‖
          ≤ ‖c i‖ * ‖z i‖ ^ (N + 1) * 1 :=
            mul_le_mul_of_nonneg_left (norm_geomMean_le_one (hzw i) L)
              (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
        _ = ‖c i‖ * ‖z i‖ ^ (N + 1) := mul_one _

/-- The circle error is small for long windows. -/
theorem tendsto_tsum_circleError {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) {w : ℂ} (hw : ‖w‖ = 1) :
    Tendsto (fun L : ℕ => ∑' i, circleError c z w L i) atTop (𝓝 0) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  have hzw : ∀ i, ‖z i * w⁻¹‖ ≤ 1 := by
    intro i
    rw [norm_mul, norm_inv, hw, inv_one, mul_one]
    exact hz i
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (L : ℕ) (i : ι) => circleError c z w L i) (g := fun _ => (0 : ℝ))
    (bound := fun i => ‖c i‖) hc ?_ ?_
  · simpa using h
  · intro i
    unfold circleError
    by_cases h1 : z i = w
    · simp [h1]
    · by_cases h2 : ‖z i‖ = 1
      · simp only [h1, h2, if_false, if_true]
        have hr1 : z i * w⁻¹ ≠ 1 := by
          intro h
          apply h1
          calc z i = z i * w⁻¹ * w := by rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one]
            _ = w := by rw [h, one_mul]
        have := (tendsto_geomMean_zero (hzw i) hr1).norm.const_mul ‖c i‖
        simpa [geomMean] using this
      · simp [h1, h2]
  · refine Eventually.of_forall fun L i => ?_
    unfold circleError
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    split_ifs
    · simp
    · exact mul_le_of_le_one_right (norm_nonneg _) (norm_geomMean_le_one (hzw i) L)
    · simp

/-- The inner error is small for windows far out. -/
theorem tendsto_tsum_innerError {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    Tendsto (fun N : ℕ => ∑' i, innerError c z N i) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (i : ι) => innerError c z N i) (g := fun _ => (0 : ℝ))
    (bound := fun i => ‖c i‖) hc ?_ ?_
  · simpa using h
  · intro i
    unfold innerError
    by_cases h2 : ‖z i‖ = 1
    · simp [h2]
    · simp only [h2, if_false]
      have hlt : ‖z i‖ < 1 := lt_of_le_of_ne (hz i) h2
      have h1 : Tendsto (fun N : ℕ => ‖z i‖ ^ (N + 1)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt).comp (tendsto_add_atTop_nat 1)
      simpa using h1.const_mul ‖c i‖
  · refine Eventually.of_forall fun N i => ?_
    unfold innerError
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    split_ifs
    · simp
    · exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz i))

/-- **Thick sets read the unit circle.** If the level sums of a summable tower in the closed unit
disc tend to zero along a set of levels containing arbitrarily long runs arbitrarily far out, no point
of the unit circle carries weight. -/
theorem merged_eq_zero_of_small_on_runs {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) {G : Set ℕ}
    (hG : ∀ L N : ℕ, ∃ M, N ≤ M ∧ ∀ ν, M + 1 ≤ ν → ν ≤ M + L → ν ∈ G)
    (hsmall : ∀ δ > 0, ∃ ν₀ : ℕ, ∀ ν ∈ G, ν₀ ≤ ν → ‖towerSum c z ν‖ ≤ δ) {w : ℂ}
    (hw : ‖w‖ = 1) : (∑' i, if z i = w then c i else 0) = 0 := by
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / 3 := by positivity
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    ((tendsto_tsum_circleError hc hz hw).eventually (ge_mem_nhds hδ))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((tendsto_tsum_innerError hc hz).eventually (ge_mem_nhds hδ))
  obtain ⟨ν₀, hν₀⟩ := hsmall (ε / 3) hδ
  set L : ℕ := max L₁ 1 with hLdef
  have hL1 : 1 ≤ L := le_max_right _ _
  obtain ⟨M, hM, hrun⟩ := hG L (max N₁ ν₀)
  have hMN : N₁ ≤ M := le_trans (le_max_left _ _) hM
  have hMν : ν₀ ≤ M := le_trans (le_max_right _ _) hM
  -- the window mean is small
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hwin : ‖windowMean c z w M L‖ ≤ ε / 3 := by
    rw [windowMean, norm_div, Complex.norm_natCast, div_le_iff₀ hLpos]
    calc ‖∑ j ∈ range L, towerSum c z (M + 1 + j) * w⁻¹ ^ (M + 1 + j)‖
        ≤ ∑ j ∈ range L, ‖towerSum c z (M + 1 + j) * w⁻¹ ^ (M + 1 + j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range L, ε / 3 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjL : j < L := Finset.mem_range.mp hj
          rw [norm_mul, norm_pow, norm_inv, hw, inv_one, one_pow, mul_one]
          exact hν₀ _ (hrun _ (by omega) (by omega)) (by omega)
      _ = ε / 3 * L := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have herr := norm_windowMean_sub_le hc hz hw M hL1
  have hA := hL₁ L (le_max_left _ _)
  have hB := hN₁ M hMN
  calc ‖∑' i, if z i = w then c i else 0‖
      ≤ ‖windowMean c z w M L‖ +
          ‖windowMean c z w M L - ∑' i, (if z i = w then c i else 0)‖ := by
        have := norm_sub_le (windowMean c z w M L)
          (windowMean c z w M L - ∑' i, (if z i = w then c i else 0))
        simpa using this
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := add_le_add hwin (herr.trans (add_le_add hA hB))
    _ = 0 + ε := by ring

end GaloisForLFunctions.InfiniteRankPurityTheory
