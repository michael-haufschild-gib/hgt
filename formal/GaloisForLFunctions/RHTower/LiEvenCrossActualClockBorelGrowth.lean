import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Escape of the actual Borel kernel to arbitrarily high degree

Every finite low-degree prefix is negligible relative to the complete kernel.
Strict positivity of every actual raw theta moment then forces its weighted
degree, equivalently its logarithmic degree, to tend to infinity.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

/-- The finite low-degree prefix of the actual Borel kernel. -/
def liEvenCrossActualClockBorelPrefix (K : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, liEvenCrossActualClockBorelTerm t j

theorem liEvenCrossActualClockBorelTerm_le_kernel (t : ℝ) (j : ℕ) :
    liEvenCrossActualClockBorelTerm t j ≤ liEvenCrossActualClockBorelKernel t :=
  (summable_liEvenCrossActualClockBorelTerm t).le_tsum j
    (fun i _ => liEvenCrossActualClockBorelTerm_nonneg t i)

theorem liEvenCrossActualClockBorelPrefix_nonneg (K : ℕ) (t : ℝ) :
    0 ≤ liEvenCrossActualClockBorelPrefix K t := by
  exact Finset.sum_nonneg (fun j _ => liEvenCrossActualClockBorelTerm_nonneg t j)

private theorem borelPrefix_le_power (K : ℕ) (hK : 0 < K) {t : ℝ} (ht : 1 ≤ t) :
    liEvenCrossActualClockBorelPrefix K t ≤
      (∑ j ∈ Finset.range K, liEvenCrossActualClockBorelCoefficient j) *
        t ^ (2 * (K - 1)) := by
  rw [liEvenCrossActualClockBorelPrefix, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [liEvenCrossActualClockBorelTerm_eq_coefficient_mul]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (by have := Finset.mem_range.mp hj; omega))
    (liEvenCrossActualClockBorelCoefficient_pos j).le

/-- Every finite degree prefix is negligible relative to the complete actual kernel. -/
theorem liEvenCrossActualClockBorelPrefix_div_kernel_tendsto (K : ℕ) :
    Tendsto (fun t : ℝ => liEvenCrossActualClockBorelPrefix K t /
      liEvenCrossActualClockBorelKernel t) atTop (𝓝 0) := by
  by_cases hK : K = 0
  · simp [hK, liEvenCrossActualClockBorelPrefix]
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  let A : ℝ := ∑ j ∈ Finset.range K, liEvenCrossActualClockBorelCoefficient j
  let b : ℝ := liEvenCrossActualClockBorelCoefficient K
  have hb : 0 < b := liEvenCrossActualClockBorelCoefficient_pos K
  have hlim : Tendsto (fun t : ℝ => (A / b) / t ^ 2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_div_atTop (A / b)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Filter.Eventually.of_forall (fun t => div_nonneg
      (liEvenCrossActualClockBorelPrefix_nonneg K t)
      (liEvenCrossActualClockBorelKernel_pos t).le)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hlower : b * t ^ (2 * K) ≤ liEvenCrossActualClockBorelKernel t := by
      simpa only [liEvenCrossActualClockBorelTerm_eq_coefficient_mul, b]
        using liEvenCrossActualClockBorelTerm_le_kernel t K
    calc
      liEvenCrossActualClockBorelPrefix K t / liEvenCrossActualClockBorelKernel t ≤
          liEvenCrossActualClockBorelPrefix K t / (b * t ^ (2 * K)) :=
        div_le_div_of_nonneg_left (liEvenCrossActualClockBorelPrefix_nonneg K t)
          (by positivity) hlower
      _ ≤ (A * t ^ (2 * (K - 1))) / (b * t ^ (2 * K)) :=
        div_le_div_of_nonneg_right (borelPrefix_le_power K hKpos ht) (by positivity)
      _ = (A / b) / t ^ 2 := by
        rw [show 2 * K = 2 * (K - 1) + 2 by omega, pow_add]
        have hp : t ^ (2 * (K - 1)) ≠ 0 := pow_ne_zero _ htpos.ne'
        field_simp

/-- Exact finite-prefix lower bound for the weighted degree. -/
theorem liEvenCrossActualClockBorelWeighted_prefix_lower (K : ℕ) (t : ℝ) :
    (2 * K : ℝ) * (liEvenCrossActualClockBorelKernel t -
      liEvenCrossActualClockBorelPrefix K t) ≤
      liEvenCrossActualClockBorelWeighted t := by
  have hf := summable_liEvenCrossActualClockBorelTerm t
  have hg := summable_liEvenCrossActualClockBorelWeightedTerm t
  have htail : (2 * K : ℝ) * (∑' j, liEvenCrossActualClockBorelTerm t (j + K)) ≤
      ∑' j : ℕ, (2 * (j + K) : ℝ) * liEvenCrossActualClockBorelTerm t (j + K) := by
    rw [← tsum_mul_left]
    have hgs := (summable_nat_add_iff K).2 hg
    simp only [Nat.cast_add] at hgs
    apply Summable.tsum_le_tsum _
      (((summable_nat_add_iff K).2 hf).mul_left (2 * K : ℝ)) hgs
    intro j
    exact mul_le_mul_of_nonneg_right (by linarith)
      (liEvenCrossActualClockBorelTerm_nonneg t (j + K))
  have hhead : 0 ≤ ∑ j ∈ Finset.range K,
      (2 * j : ℝ) * liEvenCrossActualClockBorelTerm t j := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by positivity) (liEvenCrossActualClockBorelTerm_nonneg t j)
  have heqf := hf.sum_add_tsum_nat_add K
  have heqg := hg.sum_add_tsum_nat_add K
  simp only [Nat.cast_add] at heqg
  change (2 * K : ℝ) * ((∑' j, liEvenCrossActualClockBorelTerm t j) -
    (∑ j ∈ Finset.range K, liEvenCrossActualClockBorelTerm t j)) ≤
      ∑' j : ℕ, (2 * j : ℝ) * liEvenCrossActualClockBorelTerm t j
  rw [← heqf]
  simp only [add_sub_cancel_left]
  linarith

theorem liEvenCrossActualClockBorelWeighted_div_kernel_prefix_lower (K : ℕ) (t : ℝ) :
    (2 * K : ℝ) * (1 - liEvenCrossActualClockBorelPrefix K t /
      liEvenCrossActualClockBorelKernel t) ≤
      liEvenCrossActualClockBorelWeighted t / liEvenCrossActualClockBorelKernel t := by
  have hp := liEvenCrossActualClockBorelKernel_pos t
  calc
    (2 * K : ℝ) * (1 - liEvenCrossActualClockBorelPrefix K t /
        liEvenCrossActualClockBorelKernel t) =
        ((2 * K : ℝ) * (liEvenCrossActualClockBorelKernel t -
          liEvenCrossActualClockBorelPrefix K t)) / liEvenCrossActualClockBorelKernel t := by
      field_simp
    _ ≤ liEvenCrossActualClockBorelWeighted t / liEvenCrossActualClockBorelKernel t :=
      div_le_div_of_nonneg_right (liEvenCrossActualClockBorelWeighted_prefix_lower K t) hp.le

/-- Complete actual raw-source mass escapes every bounded degree prefix. -/
theorem liEvenCrossActualClockBorelWeighted_div_kernel_tendsto_atTop :
    Tendsto (fun t : ℝ => liEvenCrossActualClockBorelWeighted t /
      liEvenCrossActualClockBorelKernel t) atTop atTop := by
  apply tendsto_atTop.2
  intro L
  obtain ⟨K, hK⟩ := exists_nat_gt (max L 0)
  have hKL : L < (K : ℝ) := lt_of_le_of_lt (le_max_left _ _) hK
  have hKpos : 0 < (K : ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
  have hsmall : ∀ᶠ t : ℝ in atTop,
      liEvenCrossActualClockBorelPrefix K t / liEvenCrossActualClockBorelKernel t < 1 / 2 :=
    (liEvenCrossActualClockBorelPrefix_div_kernel_tendsto K).eventually_lt_const (by norm_num)
  filter_upwards [hsmall] with t ht
  have hlower := liEvenCrossActualClockBorelWeighted_div_kernel_prefix_lower K t
  nlinarith

/-- Literal logarithmic derivative form of the weighted-degree divergence. -/
theorem liEvenCrossActualClockBorel_logarithmicDegree_tendsto_atTop :
    Tendsto (fun t : ℝ => t * deriv liEvenCrossActualClockBorelKernel t /
      liEvenCrossActualClockBorelKernel t) atTop atTop := by
  simpa only [liEvenCrossActualClockBorel_mul_deriv]
    using liEvenCrossActualClockBorelWeighted_div_kernel_tendsto_atTop

end
end RHTower
