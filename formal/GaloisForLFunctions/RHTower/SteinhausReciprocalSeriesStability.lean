import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCells
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open Filter Topology Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- A single character prefix controls every reciprocal series in an arbitrary
family with one summable coefficient envelope. -/
theorem exists_steinhaus_reciprocalSeries_character_tolerance {ι : Type*}
    (a : ι → ℕ → ℂ) {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu : Summable u)
    (hb : ∀ i n, ‖a i n‖ ≤ u n) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ i : ι, ∀ ω η : Omega,
      η ∈ steinhausCharacterCell B ω δ →
        ‖(∑' n : ℕ, a i n * starRingEnd ℂ (X (n + 1) η)) -
          ∑' n : ℕ, a i n * starRingEnd ℂ (X (n + 1) ω)‖ < ε := by
  have hlim := tendsto_sum_nat_add u
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp (hlim.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4)))
  let B : ℕ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have ht : (∑' n : ℕ, u (n + B)) < ε / 4 := hB₀ B (le_max_right _ _)
  let K : ℝ := 1 + ∑ n ∈ range B, u n
  have hK : 0 < K := by
    have hsum0 : 0 ≤ ∑ n ∈ range B, u n := sum_nonneg (fun n _ => hu0 n)
    dsimp only [K]
    linarith
  let δ : ℝ := ε / (4 * K)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let F : ι → Omega → ℕ → ℂ := fun i ξ n => a i n * starRingEnd ℂ (X (n + 1) ξ)
  let head : ι → Omega → ℂ := fun i ξ => ∑ n ∈ range B, F i ξ n
  have hFnorm (i : ι) (ξ : Omega) (n : ℕ) : ‖F i ξ n‖ ≤ u n := by
    simpa only [F, norm_mul, RCLike.norm_conj, norm_X, mul_one] using hb i n
  have hsum (i : ι) (ξ : Omega) : Summable (fun n => ‖F i ξ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hFnorm i ξ) hu
  have htail (i : ι) (ξ : Omega) : ‖(∑' n, F i ξ n) - head i ξ‖ < ε / 4 := by
    have hf : Summable (F i ξ) := (hsum i ξ).of_norm_bounded (fun _ => le_rfl)
    have hsplit := hf.sum_add_tsum_nat_add B
    have heq : (∑' n, F i ξ n) - head i ξ = ∑' n : ℕ, F i ξ (n + B) := by
      dsimp only [head]
      rw [← hsplit]
      abel
    rw [heq]
    have hns : Summable (fun n => ‖F i ξ (n + B)‖) := (summable_nat_add_iff (f := fun n : ℕ => ‖F i ξ n‖) B).2 (hsum i ξ)
    apply lt_of_le_of_lt _ ht
    exact (norm_tsum_le_tsum_norm hns).trans
      (hns.tsum_le_tsum (fun n => hFnorm i ξ (n+B)) ((summable_nat_add_iff (f := u) B).2 hu))
  refine ⟨B, hB, δ, hδ, ?_⟩
  intro i ω η hcell
  have hh : ‖head i η - head i ω‖ ≤ ε / 4 := by
    dsimp only [head, F]
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ range B, ‖a i n * starRingEnd ℂ (X (n+1) η) -
          a i n * starRingEnd ℂ (X (n+1) ω)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range B, u n * δ := by
        apply sum_le_sum
        intro n hn
        rw [← mul_sub, ← map_sub, norm_mul, RCLike.norm_conj]
        have hx := (hcell (n+1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩)).le
        exact mul_le_mul (hb i n) hx (norm_nonneg _) (hu0 n)
      _ = (∑ n ∈ range B, u n) * δ := by rw [sum_mul]
      _ ≤ K * δ := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hδ.le
      _ = ε / 4 := by dsimp only [δ]; field_simp [hK.ne']
  have heq : (∑' n, F i η n) - (∑' n, F i ω n) =
      ((∑' n, F i η n) - head i η) + (head i η - head i ω) +
        (head i ω - (∑' n, F i ω n)) := by ring
  change ‖(∑' n, F i η n) - (∑' n, F i ω n)‖ < ε
  rw [heq]
  have htω : ‖head i ω - (∑' n, F i ω n)‖ < ε / 4 := by
    rw [norm_sub_rev]
    exact htail i ω
  have htri := (norm_add_le
    (((∑' n, F i η n) - head i η) + (head i η - head i ω))
    (head i ω - (∑' n, F i ω n))).trans (add_le_add (norm_add_le _ _) (le_refl _))
  linarith [htail i η]

end RHTower

