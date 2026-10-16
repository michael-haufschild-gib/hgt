import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaBoundaryCancellation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Vanishing Jacobi tails for the Suzuki Gamma graph core

The Jacobi normalization makes ordinary backward shifts noncontractive.
Its exact central-binomial recurrence nevertheless controls their averaged
energy. This is the approximation mechanism used to identify the actual
minimal and maximal Gamma source graphs.
-/

open Filter Topology
open scoped BigOperators
set_option autoImplicit false

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

private theorem centralBinom_pos (n : ℕ) : 0 < normalizedCentralBinom n := by
  rw [← semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]
  exact sq_pos_of_pos (semilocalArchimedeanJacobiNormalization_pos n)

private theorem centralBinom_antitone : Antitone normalizedCentralBinom := by
  apply antitone_nat_of_succ_le
  intro n
  rw [normalizedCentralBinom_succ]
  apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ) + 2)).2
  nlinarith [centralBinom_pos n]

private theorem centralBinom_primitive_step (n : ℕ) :
    2 * ((n + 1 : ℕ) : ℝ) * normalizedCentralBinom (n + 1) -
      2 * (n : ℝ) * normalizedCentralBinom n = normalizedCentralBinom n := by
  rw [normalizedCentralBinom_succ]
  push_cast
  field_simp
  ring

private theorem centralBinom_block (m N : ℕ) :
    (∑ k ∈ Finset.range N, normalizedCentralBinom (k + m)) =
      2 * ((N + m : ℕ) : ℝ) * normalizedCentralBinom (N + m) -
        2 * (m : ℝ) * normalizedCentralBinom m := by
  calc
    _ = ∑ k ∈ Finset.range N,
        (2 * ((k + 1 + m : ℕ) : ℝ) * normalizedCentralBinom (k + 1 + m) -
          2 * ((k + m : ℕ) : ℝ) * normalizedCentralBinom (k + m)) := by
      apply Finset.sum_congr rfl
      intro k _
      simpa [Nat.add_right_comm] using (centralBinom_primitive_step (k + m)).symm
    _ = _ := by
      simpa using Finset.sum_range_sub
        (fun k => 2 * ((k + m : ℕ) : ℝ) * normalizedCentralBinom (k + m)) N

private theorem centralBinom_block_le (m N : ℕ) :
    (∑ k ∈ Finset.range N, normalizedCentralBinom (k + m)) ≤
      2 * (N : ℝ) * normalizedCentralBinom (N + m) := by
  rw [centralBinom_block]
  have ha := centralBinom_antitone (Nat.le_add_left m N)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α := ℝ) m)]

private theorem centralBinom_backward_block_le (j L : ℕ) (hL : L ≤ j + 1) :
    (∑ n ∈ Finset.range L, normalizedCentralBinom (j - n + 3)) ≤
      2 * (L : ℝ) * normalizedCentralBinom (j + 3) := by
  have heq : (∑ n ∈ Finset.range L, normalizedCentralBinom (j - n + 3)) =
      ∑ k ∈ Finset.range L, normalizedCentralBinom (k + (j + 4 - L)) := by
    rw [← Finset.sum_range_reflect (fun n => normalizedCentralBinom (j - n + 3)) L]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    have hk' := Finset.mem_range.mp hk
    omega
  rw [heq]
  have he : L + (j + 4 - L) = j + 4 := by omega
  calc
    _ ≤ 2 * (L : ℝ) * normalizedCentralBinom (L + (j + 4 - L)) :=
      centralBinom_block_le _ _
    _ ≤ 2 * (L : ℝ) * normalizedCentralBinom (j + 3) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left (centralBinom_antitone (by omega)) (by positivity)

/-- A translated Jacobi tail coefficient. The cutoff is on the original degree. -/
def suzukiGammaJacobiTailWeight (n j : ℕ) : ℝ :=
  if n ≤ j then normalizedCentralBinom (j - n + 3) /
    normalizedCentralBinom (j + 3) else 0

theorem suzukiGammaJacobiTailWeight_nonneg (n j : ℕ) :
    0 ≤ suzukiGammaJacobiTailWeight n j := by
  unfold suzukiGammaJacobiTailWeight
  split_ifs
  · exact div_nonneg (centralBinom_pos _).le (centralBinom_pos _).le
  · exact le_rfl

theorem sum_suzukiGammaJacobiTailWeight_le (N j : ℕ) :
    (∑ n ∈ Finset.range N, suzukiGammaJacobiTailWeight n j) ≤ 2 * (N : ℝ) := by
  let L := min N (j + 1)
  have hL : L ≤ j + 1 := min_le_right _ _
  have hLN : L ≤ N := min_le_left _ _
  have heq : (∑ n ∈ Finset.range N, suzukiGammaJacobiTailWeight n j) =
      (∑ n ∈ Finset.range L, normalizedCentralBinom (j - n + 3)) /
        normalizedCentralBinom (j + 3) := by
    rw [Finset.sum_div]
    calc
      _ = ∑ n ∈ Finset.range L, suzukiGammaJacobiTailWeight n j := by
        apply (Finset.sum_subset (Finset.range_mono hLN) ?_).symm
        intro n hn hnL
        have hn' := Finset.mem_range.mp hn
        have hnL' : L ≤ n := by simpa using hnL
        have hj : j < n := by dsimp [L] at hnL'; omega
        simp [suzukiGammaJacobiTailWeight, not_le.mpr hj]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := Finset.mem_range.mp hn
        simp [suzukiGammaJacobiTailWeight, show n ≤ j by omega]
  rw [heq]
  apply (div_le_iff₀ (centralBinom_pos _)).2
  calc
    _ ≤ 2 * (L : ℝ) * normalizedCentralBinom (j + 3) :=
      centralBinom_backward_block_le j L hL
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hLN) (by norm_num))
      (centralBinom_pos _).le

theorem suzukiGammaJacobiTailWeight_le (n j : ℕ) :
    suzukiGammaJacobiTailWeight n j ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), suzukiGammaJacobiTailWeight k j :=
      Finset.single_le_sum (fun k _ => suzukiGammaJacobiTailWeight_nonneg k j)
        (Finset.mem_range.mpr (by omega))
    _ ≤ _ := sum_suzukiGammaJacobiTailWeight_le _ _

/-- Squared energy of a backward shift in the actual surviving Jacobi tail. -/
def suzukiGammaJacobiTailEnergy (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' j, suzukiGammaJacobiTailWeight n j * b j

theorem summable_suzukiGammaJacobiTailWeight_mul
    {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ j, 0 ≤ b j) (n : ℕ) :
    Summable (fun j => suzukiGammaJacobiTailWeight n j * b j) := by
  exact Summable.of_nonneg_of_le
    (fun j => mul_nonneg (suzukiGammaJacobiTailWeight_nonneg n j) (hb0 j))
    (fun j => mul_le_mul_of_nonneg_right (suzukiGammaJacobiTailWeight_le n j) (hb0 j))
    (hb.mul_left _)

theorem suzukiGammaJacobiTailEnergy_nonneg
    {b : ℕ → ℝ} (hb0 : ∀ j, 0 ≤ b j) (n : ℕ) :
    0 ≤ suzukiGammaJacobiTailEnergy b n :=
  tsum_nonneg fun j => mul_nonneg (suzukiGammaJacobiTailWeight_nonneg n j) (hb0 j)

/-- The averaged normalized tail energy vanishes for every summable source energy. -/
theorem tendsto_suzukiGammaJacobiTailEnergy_mean_zero
    {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ j, 0 ≤ b j) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, suzukiGammaJacobiTailEnergy b n) atTop (𝓝 0) := by
  have hpoint (j : ℕ) :
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, suzukiGammaJacobiTailWeight n j * b j)
        atTop (𝓝 0) := by
    have hz : Tendsto (fun n => suzukiGammaJacobiTailWeight n j * b j) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (j + 1)] with n hn
      simp [suzukiGammaJacobiTailWeight, show ¬ n ≤ j by omega]
    exact hz.cesaro
  have hbound : ∀ N j : ℕ,
      ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, suzukiGammaJacobiTailWeight n j * b j‖ ≤
        2 * b j := by
    intro N j
    have hs0 : 0 ≤ ∑ n ∈ Finset.range N, suzukiGammaJacobiTailWeight n j :=
      Finset.sum_nonneg (fun n _ => suzukiGammaJacobiTailWeight_nonneg n j)
    rw [← Finset.sum_mul, Real.norm_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (mul_nonneg hs0 (hb0 j)))]
    by_cases hN : N = 0
    · simp [hN, hb0 j]
    · have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      calc
        _ ≤ (N : ℝ)⁻¹ * (2 * (N : ℝ) * b j) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (sum_suzukiGammaJacobiTailWeight_le N j) (hb0 j))
            (inv_nonneg.mpr (Nat.cast_nonneg N))
        _ = _ := by field_simp
  have ht := tendsto_tsum_of_dominated_convergence (hb.mul_left 2) hpoint
    (Filter.Eventually.of_forall hbound)
  simp only [tsum_zero] at ht
  apply ht.congr'
  filter_upwards with N
  rw [tsum_mul_left]
  congr 1
  exact Summable.tsum_finsetSum fun n _ =>
    summable_suzukiGammaJacobiTailWeight_mul hb hb0 n

/-- Arbitrarily late Jacobi shifts have arbitrarily small energy. This is the
graph-core approximation, with no regularity assumption on the output vector. -/
theorem exists_suzukiGammaJacobiTailEnergy_lt
    {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ j, 0 ≤ b j)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n ≥ N, suzukiGammaJacobiTailEnergy b n < ε := by
  by_contra hn
  push Not at hn
  let lower : ℕ → ℝ := fun n => if N ≤ n then ε else 0
  have hlower : Tendsto lower atTop (𝓝 ε) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hN
    simp [lower, hN]
  have hle (n : ℕ) : lower n ≤ suzukiGammaJacobiTailEnergy b n := by
    dsimp only [lower]
    split_ifs with h
    · exact hn n h
    · exact suzukiGammaJacobiTailEnergy_nonneg hb0 n
  have havg (M : ℕ) :
      (M : ℝ)⁻¹ * (∑ n ∈ Finset.range M, lower n) ≤
        (M : ℝ)⁻¹ * (∑ n ∈ Finset.range M, suzukiGammaJacobiTailEnergy b n) := by
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => hle n))
    positivity
  have he : ε ≤ 0 := le_of_tendsto_of_tendsto hlower.cesaro
    (tendsto_suzukiGammaJacobiTailEnergy_mean_zero hb hb0)
    (Filter.Eventually.of_forall havg)
  exact (not_le_of_gt hε) he

end RHTower
