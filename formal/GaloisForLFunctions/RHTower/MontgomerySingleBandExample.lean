import GaloisForLFunctions.RHTower.MontgomerySingleBandIsolation

/-!
# The single-band isolation law with explicit constants

Window `[3/5, 9/10]`, separation `50` mean gaps, band width `(1/20)/log T`: the
Montgomery–Vaughan band constant is at least `1/20` for every cardinality, so every band of
isolated off-line zeros at distance `≥ 4δ₀` from the line, when all other zeros are within
`δ₀` of the line, has at most `(6e³/π) T^{1 − (6/5)(σ−1/2)} log T` elements.
-/

open Filter Topology Set

namespace RHTower

/-- The layer sum is at most the geometric tail `τ²/(1−τ²)`. -/
theorem sum_Ico_rpow_div_factorial_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (K : ℕ) :
    ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ) ≤ τ ^ 2 / (1 - τ ^ 2) := by
  have hτ2 : τ ^ 2 < 1 := by nlinarith
  have hτ20 : 0 ≤ τ ^ 2 := by positivity
  calc ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)
      ≤ ∑ m ∈ Finset.Ico 1 K, (τ ^ 2) ^ m := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [pow_mul]
        have h1 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
        calc (τ ^ 2) ^ m / (m.factorial : ℝ) ≤ (τ ^ 2) ^ m / 1 := by
              gcongr
          _ = (τ ^ 2) ^ m := div_one _
    _ ≤ (τ ^ 2) ^ 1 / (1 - τ ^ 2) := geom_sum_Ico_le_of_lt_one hτ20 hτ2
    _ = τ ^ 2 / (1 - τ ^ 2) := by rw [pow_one]

/-- The remainder factor `N ρ_{N+1}²` is at most `2 τ^2` for `τ ≤ 1/2`. -/
theorem card_mul_remainder_sq_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) (N : ℕ) :
    (N : ℝ) * (τ ^ (N + 1) * (((N + 1).succ : ℝ) / (((N + 1).factorial : ℝ) * (N + 1)))) ^ 2
      ≤ τ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
    positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfac : ((N + 1).succ : ℝ) / (((N + 1).factorial : ℝ) * (N + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : ((N + 1 : ℕ) : ℝ) ≤ ((N + 1).factorial : ℝ) := by
      exact_mod_cast Nat.self_le_factorial (N + 1)
    have h2 : ((N + 1).succ : ℝ) = (N + 1 : ℝ) + 1 := by push_cast; ring
    rw [h2]
    push_cast at h1
    nlinarith [h1, hN1]
  have hfac0 : 0 ≤ ((N + 1).succ : ℝ) / (((N + 1).factorial : ℝ) * (N + 1)) := by positivity
  have hpow : (N : ℝ) * (τ ^ (N + 1)) ^ 2 ≤ τ ^ 2 := by
    have h4 : (N : ℝ) ≤ 4 ^ N := by
      have := Nat.lt_pow_self (by norm_num : 1 < 4) (n := N)
      exact_mod_cast this.le
    have hτ4 : τ ^ 2 ≤ 1 / 4 := by nlinarith
    have hτ2N : (τ ^ 2) ^ N ≤ (1 / 4) ^ N := pow_le_pow_left₀ (by positivity) hτ4 N
    calc (N : ℝ) * (τ ^ (N + 1)) ^ 2 = (N : ℝ) * (τ ^ 2) ^ N * τ ^ 2 := by ring
      _ ≤ (4 : ℝ) ^ N * (1 / 4) ^ N * τ ^ 2 := by gcongr
      _ = τ ^ 2 := by rw [← mul_pow]; norm_num
  calc (N : ℝ) * (τ ^ (N + 1) * (((N + 1).succ : ℝ) / (((N + 1).factorial : ℝ) * (N + 1)))) ^ 2
      = (N : ℝ) * (τ ^ (N + 1)) ^ 2 * (((N + 1).succ : ℝ) / (((N + 1).factorial : ℝ) * (N + 1))) ^ 2 := by
        ring
    _ ≤ (N : ℝ) * (τ ^ (N + 1)) ^ 2 * 1 := by
        gcongr
        exact pow_le_one₀ hfac0 hfac
    _ ≤ τ ^ 2 := by rw [mul_one]; exact hpow

/-- The band constant for the window `3/10`, separation `50`, band width parameter `1/20`. -/
theorem mvBandConstant_example (N : ℕ) :
    (1 / 20 : ℝ) ≤ mvBandConstant (3 / 10) 50 (1 / 20) (N + 1) N := by
  unfold mvBandConstant
  have hπ := Real.pi_gt_three
  have hc : 26 / (Real.pi * 50) ≤ 26 / 150 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have hc0 : 0 ≤ 26 / (Real.pi * 50) := by positivity
  have hsum := sum_Ico_rpow_div_factorial_le (τ := 1 / 20) (by norm_num) (by norm_num) (N + 1)
  have hsum0 : 0 ≤ ∑ m ∈ Finset.Ico 1 (N + 1), (1 / 20 : ℝ) ^ (2 * m) / (m.factorial : ℝ) :=
    Finset.sum_nonneg fun m _ => by positivity
  have hrem := card_mul_remainder_sq_le (τ := 1 / 20) (by norm_num) (by norm_num) N
  have h1 : 4 * (3 / 10 + 26 / (Real.pi * 50)) *
      ∑ m ∈ Finset.Ico 1 (N + 1), (1 / 20 : ℝ) ^ (2 * m) / (m.factorial : ℝ)
      ≤ 4 * (3 / 10 + 26 / 150) * ((1 / 20 : ℝ) ^ 2 / (1 - (1 / 20 : ℝ) ^ 2)) := by
    gcongr
  have h2 : 2 * (3 / 10) * (N : ℝ) *
      ((1 / 20 : ℝ) ^ (N + 1) * (((N + 1).succ : ℝ) / (((N + 1).factorial : ℝ) * (N + 1)))) ^ 2
      ≤ 2 * (3 / 10) * (1 / 20 : ℝ) ^ 2 := by
    have := hrem
    nlinarith [this]
  norm_num at h1 h2 hc ⊢
  linarith

/-- **Single-band isolation law, explicit form.**  For `T` large, every set `A` of zero copies in
the window whose real parts lie in `[σ, σ + (1/20)/log T]` with `σ ≥ 1/2 + 4δ₀`, such that all
other zero copies have real part at most `1/2 + δ₀` and whose ordinates are `50`-separated in
mean-spacing units, satisfies `|A| ≤ (6e³/π) T^{1 − (6/5)(σ − 1/2)} log T`. -/
theorem eventually_card_singleBand_le_example {σ δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hσ : 1 / 2 + 4 * δ₀ ≤ σ) :
    ∀ᶠ T : ℝ in atTop, ∀ A : Finset XiZeroCopy, A ⊆ zeroWindow T →
      (∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + (1 / 20) / Real.log T) →
      (∀ k ∈ zeroWindow T \ A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ A, ∀ k ∈ A, j ≠ k → 50 ≤ |bandFreq T j - bandFreq T k|) →
      (A.card : ℝ) ≤ (6 * Real.exp 3 / Real.pi) * T ^ (1 - 6 / 5 * (σ - 1 / 2)) * Real.log T := by
  have h := eventually_card_singleBand_le (a := 3 / 5) (ℓ := 3 / 10) (σ := σ) (δ₀ := δ₀)
    (D := 50) (τ := 1 / 20) (κ := 1 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hδ₀ hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num) mvBandConstant_example
  filter_upwards [h] with T hT
  intro A hA hband hR hsep
  have := hT A hA hband hR hsep
  have hconst : (3 / 10 : ℝ) * Real.exp 3 / (Real.pi * (1 / 20)) = 6 * Real.exp 3 / Real.pi := by
    field_simp
    ring
  have hexp : (1 : ℝ) - 2 * (3 / 5) * (σ - 1 / 2) = 1 - 6 / 5 * (σ - 1 / 2) := by ring
  rw [hconst, hexp] at this
  exact this

end RHTower
