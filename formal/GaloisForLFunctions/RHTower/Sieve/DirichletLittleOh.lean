import GaloisForLFunctions.RHTower.Sieve.DirichletThreshold

/-!
# The partial sum is `o (log t)`

The constant in the threshold form is `2/(K - 4/3)`, which the order can make arbitrarily small.
Choosing the order from the target accuracy rather than from `t` therefore gives, for every `ε > 0`,
a threshold past which the partial sum on the line `Re s = 1` is at most
`1 + log 2 + ε log (t / 2π)`.

This is the qualitative half of Littlewood's estimate.  The quantitative exponent needs the order to
grow with `t`; here it is fixed once `ε` is chosen.
-/

namespace RHTower.Sieve

open Finset

/-- An order making the threshold constant at most `ε`. -/
noncomputable def orderForAccuracy (ε : ℝ) : ℕ := max 2 ⌈4 / 3 + 2 / ε⌉₊

theorem two_le_orderForAccuracy (ε : ℝ) : 2 ≤ orderForAccuracy ε := le_max_left _ _

theorem orderForAccuracy_spec {ε : ℝ} (hε : 0 < ε) :
    2 / ((orderForAccuracy ε : ℝ) - 4 / 3) ≤ ε := by
  have hceil : (4 / 3 + 2 / ε) ≤ ((⌈4 / 3 + 2 / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hle : ((⌈4 / 3 + 2 / ε⌉₊ : ℕ) : ℝ) ≤ ((orderForAccuracy ε : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 2 ⌈4 / 3 + 2 / ε⌉₊
  have hK : 4 / 3 + 2 / ε ≤ ((orderForAccuracy ε : ℕ) : ℝ) := le_trans hceil hle
  have hpos : (0 : ℝ) < 2 / ε := by positivity
  have hden : (0 : ℝ) < ((orderForAccuracy ε : ℕ) : ℝ) - 4 / 3 := by linarith
  rw [div_le_iff₀ hden]
  have hstep : 2 / ε ≤ ((orderForAccuracy ε : ℕ) : ℝ) - 4 / 3 := by linarith
  have := mul_le_mul_of_nonneg_left hstep hε.le
  rw [mul_div_cancel₀ _ hε.ne'] at this
  linarith

/-- **`o (log t)`.**  For every accuracy there is a threshold past which the partial sum on the line
`Re s = 1` is below `1 + log 2 + ε log (t / 2π)`. -/
theorem littlewood_littleOh {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
        ≤ 1 + Real.log 2 + ε * Real.log (t / (2 * Real.pi)) := by
  classical
  set K : ℕ := orderForAccuracy ε with hKdef
  have hK : 2 ≤ K := two_le_orderForAccuracy ε
  have hKeps : 2 / ((K : ℝ) - 4 / 3) ≤ ε := orderForAccuracy_spec hε
  refine ⟨max (16 * Real.pi)
      (2 * Real.pi * Real.exp (max (largenessBound K) (balanceBound K) + 1)), fun t hT => ?_⟩
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have ht16 : 16 * Real.pi ≤ t := le_trans (le_max_left _ _) hT
  have hLnn : 0 ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith
  have hmain := littlewood_threshold K hK t hT
  refine le_trans hmain ?_
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by
    have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hrw : 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
      = Real.log (t / (2 * Real.pi)) * (2 / ((K : ℝ) - 4 / 3)) := by
    field_simp
  rw [hrw]
  have := mul_le_mul_of_nonneg_left hKeps hLnn
  linarith

end RHTower.Sieve
