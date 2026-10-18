import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound

/-!
# Finite power windows from a summable amplitude budget

If `‖b i‖ ≤ A ‖w i‖`, the modes above level `L` have cardinality at most
`A (∑' i, ‖w i‖) / L`. Sector weights prevent cancellation in radial subsets.
Weighted Turán then detects a mode above `2L` in a finite consecutive power window;
the entire complementary series is bounded directly by its absolute weight mass.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The loss in the separation-free weighted Turán bound. -/
def weightedTuranLoss (M n : ℕ) : ℝ :=
  2 * (Real.exp 1 * n * (6 * (n + 1) * ((M : ℝ) + 2 * n + 2)) ^ n)

theorem weightedTuranLoss_pos (M : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    0 < weightedTuranLoss M n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold weightedTuranLoss
  positivity

/-- Absolute weight domination makes every positive loud set finite. -/
theorem finite_loud_of_weight_domination {ι : Type*} (b w : ι → ℂ)
    (hw : Summable fun i => ‖w i‖) {A L : ℝ}
    (hdom : ∀ i, ‖b i‖ ≤ A * ‖w i‖) (hL : 0 < L) :
    {i | L < ‖b i‖}.Finite := by
  have hb : Summable b := Summable.of_norm_bounded (hw.mul_left A) hdom
  have hfinite := Filter.eventually_cofinite.mp
    (hb.norm.tendsto_cofinite_zero.eventually (gt_mem_nhds hL))
  exact hfinite.subset fun i hi => not_lt_of_ge hi.le

/-- Loud cardinality is paid for by the actual absolute weight mass. -/
theorem loud_card_mul_le_weight_mass {ι : Type*} (b w : ι → ℂ)
    (hw : Summable fun i => ‖w i‖) {A L : ℝ} (hA : 0 ≤ A)
    (hdom : ∀ i, ‖b i‖ ≤ A * ‖w i‖) (G : Finset ι)
    (hG : ∀ i ∈ G, L ≤ ‖b i‖) :
    (G.card : ℝ) * L ≤ A * ∑' i, ‖w i‖ := by
  calc
    (G.card : ℝ) * L = ∑ _i ∈ G, L := by simp
    _ ≤ ∑ i ∈ G, ‖b i‖ := Finset.sum_le_sum hG
    _ ≤ ∑ i ∈ G, A * ‖w i‖ := Finset.sum_le_sum fun i _ => hdom i
    _ = A * ∑ i ∈ G, ‖w i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ A * ∑' i, ‖w i‖ := mul_le_mul_of_nonneg_left
      (hw.sum_le_tsum G fun i _ => norm_nonneg _) hA

/-- Every weighted power is absolutely summable under the same domination. -/
theorem summable_weighted_pow_of_domination {ι : Type*} (b w : ι → ℂ)
    (hw : Summable fun i => ‖w i‖) {A : ℝ} (hA : 0 ≤ A)
    (hdom : ∀ i, ‖b i‖ ≤ A * ‖w i‖) (k : ℕ) :
    Summable fun i => w i * b i ^ k := by
  have hb : ∀ i, ‖b i‖ ≤ A * ∑' j, ‖w j‖ := fun i =>
    (hdom i).trans (mul_le_mul_of_nonneg_left
      (hw.le_tsum i fun j _ => norm_nonneg _) hA)
  refine Summable.of_norm_bounded
    (hw.mul_right ((A * ∑' i, ‖w i‖) ^ k)) fun i => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hb i) k) (norm_nonneg _)

/-- A quantitative finite-window certificate. The cost condition is only a scalar inequality;
the infinite tail is discharged from the amplitude/weight domination. -/
theorem exists_weighted_power_window_of_budget {ι : Type*} (b w : ι → ℂ)
    (hw : Summable fun i => ‖w i‖)
    (hcone : ∀ i, ‖w i‖ / 2 ≤ (w i).re)
    {A L : ℝ} (hA : 0 < A) (hL : 1 ≤ L)
    (hdom : ∀ i, ‖b i‖ ≤ A * ‖w i‖)
    (hbig : ∃ i, 2 * L ≤ ‖b i‖) (M : ℕ)
    (hbudget : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * L ≤ A * ∑' i, ‖w i‖ →
      8 * (∑' i, ‖w i‖) * A * weightedTuranLoss M n ≤ (2 : ℝ) ^ (M + 1)) :
    ∃ n k : ℕ, 1 ≤ n ∧ (n : ℝ) * L ≤ A * ∑' i, ‖w i‖ ∧
      M < k ∧ k ≤ M + n ∧
      2 * (∑' i, ‖w i‖) * L ^ k ≤ ‖∑' i, w i * b i ^ k‖ := by
  classical
  let W : ℝ := ∑' i, ‖w i‖
  have hW : 0 ≤ W := tsum_nonneg fun i => norm_nonneg _
  have hL0 : 0 < L := by linarith
  have hfinite := finite_loud_of_weight_domination b w hw hdom hL0
  let G := hfinite.toFinset
  have hG : ∀ i, i ∈ G ↔ L < ‖b i‖ := by
    intro i
    exact Set.Finite.mem_toFinset hfinite
  obtain ⟨q, hq⟩ := hbig
  have hqG : q ∈ G := (hG q).2 (by linarith)
  have hn : 1 ≤ G.card := Finset.card_pos.2 ⟨q, hqG⟩
  have hcard : (G.card : ℝ) * L ≤ A * W :=
    loud_card_mul_le_weight_mass b w hw hA.le hdom G
      fun i hi => ((hG i).1 hi).le
  have hweight : 1 / A ≤ ‖w q‖ := by
    rw [div_le_iff₀ hA]
    nlinarith [hdom q]
  have hβ : 0 < 1 / (2 * A) := by positivity
  obtain ⟨k, hk0, hk1, hk2⟩ := exists_norm_weightedPowerSum_ge_scaled G b w
    (show 0 < 2 * L by positivity) ⟨q, hqG, hq⟩ M hβ (by
      intro t _ ht
      let S := G.filter (fun i => t * (2 * L) ≤ ‖b i‖)
      have hqS : q ∈ S := Finset.mem_filter.2 ⟨hqG,
        (mul_le_mul_of_nonneg_right ht (by positivity)).trans (by simpa using hq)⟩
      have hmass : 1 / A ≤ ∑ i ∈ S, ‖w i‖ := hweight.trans
        (Finset.single_le_sum (fun i _ => norm_nonneg (w i)) hqS)
      calc
        1 / (2 * A) = (1 / A) / 2 := by ring
        _ ≤ (∑ i ∈ S, ‖w i‖) / 2 := by linarith
        _ ≤ (∑ i ∈ S, w i).re := by
          rw [Complex.re_sum, Finset.sum_div]
          exact Finset.sum_le_sum fun i _ => hcone i
        _ ≤ ‖∑ i ∈ S, w i‖ := Complex.re_le_norm _)
  have hcost := hbudget G.card hn hcard
  have hD : 0 < weightedTuranLoss M G.card := weightedTuranLoss_pos M hn
  change 1 / (2 * A) * (2 * L) ^ k / weightedTuranLoss M G.card ≤ _ at hk2
  have hexp : (2 : ℝ) ^ (M + 1) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) hk0
  have hcoef : 4 * W ≤ (1 / (2 * A)) * 2 ^ k / weightedTuranLoss M G.card := by
    rw [le_div_iff₀ hD]
    have hcost' : 8 * W * A * weightedTuranLoss M G.card ≤ 2 ^ k := hcost.trans hexp
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * A by positivity)).mp
    calc
      (2 * A) * (4 * W * weightedTuranLoss M G.card) =
          8 * W * A * weightedTuranLoss M G.card := by ring
      _ ≤ 2 ^ k := hcost'
      _ = (2 * A) * (1 / (2 * A) * 2 ^ k) := by field_simp [hA.ne']
  have hhead : 4 * W * L ^ k ≤ ‖∑ i ∈ G, w i * b i ^ k‖ := by
    calc
      4 * W * L ^ k ≤
          (1 / (2 * A) * 2 ^ k / weightedTuranLoss M G.card) * L ^ k :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg hL0.le _)
      _ = 1 / (2 * A) * (2 * L) ^ k / weightedTuranLoss M G.card := by
        rw [mul_pow]; ring
      _ ≤ _ := hk2
  have hs := summable_weighted_pow_of_domination b w hw hA.le hdom k
  have htail : ‖∑' i : {i // i ∉ G}, w i * b i ^ k‖ ≤ W * L ^ k := by
    have hquiet : ∀ i : {i // i ∉ G}, ‖b i‖ ≤ L := by
      intro i
      exact le_of_not_gt fun hi => i.2 ((hG i).2 hi)
    calc
      ‖∑' i : {i // i ∉ G}, w i * b i ^ k‖ ≤
          ∑' i : {i // i ∉ G}, ‖w i * b i ^ k‖ :=
        norm_tsum_le_tsum_norm (hs.norm.subtype _)
      _ ≤ ∑' i : {i // i ∉ G}, ‖w i‖ * L ^ k := by
        refine Summable.tsum_le_tsum (fun i => ?_) (hs.norm.subtype _)
          ((hw.subtype _).mul_right _)
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hquiet i) k) (norm_nonneg _)
      _ = (∑' i : {i // i ∉ G}, ‖w i‖) * L ^ k := tsum_mul_right
      _ ≤ W * L ^ k := mul_le_mul_of_nonneg_right
        (Summable.tsum_subtype_le (fun i => ‖w i‖) {i | i ∉ G}
          (fun i => norm_nonneg _) hw) (pow_nonneg hL0.le _)
  refine ⟨G.card, k, hn, hcard, by omega, hk1, ?_⟩
  rw [← hs.sum_add_tsum_subtype_compl G]
  have htriangle := norm_sub_norm_le (∑ i ∈ G, w i * b i ^ k)
    (-(∑' i : {i // i ∉ G}, w i * b i ^ k))
  rw [norm_neg, sub_neg_eq_add] at htriangle
  nlinarith [mul_nonneg hW (pow_nonneg hL0.le k)]

end

end GaloisForLFunctions.HTGeometry
