import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistRate
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The sharp twisted sum, with a rate

Comparing the smoothed sum with the sharp one costs `H + 1`, so the rate of `MoebiusTwistRate`
transfers:

    ‖∑_{n ≤ N} μ(n)n^{-iτ}‖ ≤ 3N·exp(-κ(log N)^{1/10}/2)/π + H + 1 ,

uniformly over the admissible twists, with `H = N/exp((log N)^{1/20})`.  Both terms are `N` times an
explicit saving, so this is the quantitative form of `MoebiusTwistSharpLittleO`.
-/

namespace RHTower.Sieve

open Filter Topology Finset GaloisForLFunctions.HTGeometry

/-- **The sharp twisted Möbius sum, with an explicit saving.** -/
theorem exists_norm_sum_moebiusTwist_rate :
    ∃ K₀ : ℕ, ∀ᶠ N : ℝ in atTop, ∀ τ : ℝ,
      K₀ ≤ contourParam (N + smoothWidth N) →
      5 + 4 * |τ| ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖
        ≤ 3 * N
            * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2))
            / Real.pi
          + (smoothWidth N + 1) := by
  obtain ⟨K₀, hev⟩ := exists_norm_tsum_moebiusTwist_smoothWeight_rate
  refine ⟨K₀, ?_⟩
  have hev2 : ∀ᶠ N : ℝ in atTop, (1 : ℝ) ≤ Real.log N :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ), hev2] with N hN hN1 hlogN
  intro τ hK hτ
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith
  have hH1 : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
  have hH0 : (0 : ℝ) < smoothWidth N := by linarith
  have hHN : smoothWidth N ≤ N := smoothWidth_le hN0 hlog0
  set S : ℂ := ∑' n : ℕ, moebiusTwist τ n
      * ((smoothWeight N (smoothWidth N) (n : ℝ) : ℝ) : ℂ) with hSdef
  have hbase := hN τ hK hτ
  have hsmul : ‖(2 * Real.pi : ℝ) • S‖ = 2 * Real.pi * ‖S‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hsmul] at hbase
  -- the smoothed sum, with the rate
  have hS : ‖S‖
      ≤ (N + smoothWidth N + 1)
        * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2))
        / Real.pi := by
    rw [le_div_iff₀ hpi]
    linarith [hbase]
  -- the comparison with the sharp sum
  have hcmp := norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
    (a := moebiusTwist τ) (norm_moebiusTwist_le_one τ) (N := N) (H := smoothWidth N) hN0 hH0
  have htri : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖
      ≤ ‖S‖ + (smoothWidth N + 1) := by
    have h := norm_sub_le S (S - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n)
    have h2 : ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖
        ≤ ‖S‖ + ‖S - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖ := by
      simpa using h
    linarith [hcmp]
  -- the trivial size
  have hsize : N + smoothWidth N + 1 ≤ 3 * N := by linarith
  have hexp0 : (0 : ℝ)
      < Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2)) :=
    Real.exp_pos _
  have hmono : (N + smoothWidth N + 1)
        * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2))
        / Real.pi
      ≤ 3 * N
        * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) / 2))
        / Real.pi := by
    refine div_le_div_of_nonneg_right ?_ hpi.le
    exact mul_le_mul_of_nonneg_right hsize hexp0.le
  linarith [htri, hS, hmono]

end RHTower.Sieve
