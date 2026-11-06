import Mathlib

/-!
# Convergence on a measurable density-one set

If every positive level set of a nonnegative function has density zero,
one measurable density-one set supports ordinary convergence to zero.
Truncating successively smaller level sets gives summable uniform density
bounds. A measurable hull preserves all bounded prefix measures.
-/

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

noncomputable section

private theorem geometric_prefix_tail (N : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (∑' m : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (N + m) * H)) =
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N * H) := by
  calc
    _ = ∑' m : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ N * H) * (2⁻¹ : ℝ≥0∞) ^ m := by
      apply tsum_congr
      intro m
      rw [pow_add, show (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ m * H =
        ((1 / 2 : ℝ) ^ N * H) * (1 / 2 : ℝ) ^ m by ring]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ) ^ N * H),
        ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
      norm_num
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ N * H) * 2 := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    _ = _ := by
      rw [show 2 * (1 / 2 : ℝ) ^ N * H = ((1 / 2 : ℝ) ^ N * H) * 2 by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ) ^ N * H)]
      norm_num

/-- Density-zero positive level sets give convergence on one measurable density-one set. -/
theorem exists_measurable_densityOne_tendsto_zero_of_density_zero
    {f : ℝ → ℝ} (hnonneg : ∀ X : ℝ, 1 ≤ X → 0 ≤ f X)
    (hlevel : ∀ ε > 0, ∀ δ > 0, ∀ᶠ H : ℝ in atTop,
      volume ({X | ε < f X} ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H)) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      (∀ δ > 0, ∀ᶠ H : ℝ in atTop,
        volume (Sᶜ ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H)) ∧
      Tendsto f (atTop ⊓ 𝓟 S) (𝓝 0) := by
  classical
  have hcut : ∀ n : ℕ, ∃ R : ℝ, ∀ H ≥ R,
      volume ({X | 1 / ((n : ℝ) + 1) < f X} ∩ Icc 0 H) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n * H) := by
    intro n
    exact eventually_atTop.mp (hlevel (1 / ((n : ℝ) + 1)) (by positivity)
      ((1 / 2 : ℝ) ^ n) (by positivity))
  choose R hR using hcut
  let C : ℕ → Set ℝ := fun n => {X | R n < X ∧ 1 / ((n : ℝ) + 1) < f X}
  let E : Set ℝ := ⋃ n : ℕ, C n
  have hC : ∀ n : ℕ, ∀ H : ℝ, 0 ≤ H →
      volume (C n ∩ Icc 0 H) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n * H) := by
    intro n H hH
    by_cases hHR : H ≤ R n
    · have he : C n ∩ Icc 0 H = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro X hX
        exact (not_lt_of_ge (hX.2.2.trans hHR)) hX.1.1
      rw [he, measure_empty]
      positivity
    · have hsub : C n ∩ Icc 0 H ⊆ {X | 1 / ((n : ℝ) + 1) < f X} ∩ Icc 0 H :=
        fun _ hX => ⟨hX.1.2, hX.2⟩
      exact (measure_mono hsub).trans (hR n H (le_of_not_ge hHR))
  have hE : ∀ δ > 0, ∀ᶠ H : ℝ in atTop,
      volume (E ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H) := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hfront := hlevel (1 / ((N : ℝ) + 1)) (by positivity) (δ / 2) (by positivity)
    filter_upwards [hfront, eventually_ge_atTop (0 : ℝ)] with H hfront hH
    have hsub : E ∩ Icc 0 H ⊆ ({X | 1 / ((N : ℝ) + 1) < f X} ∩ Icc 0 H) ∪
        ⋃ m : ℕ, C (N + m) ∩ Icc 0 H := by
      intro X hX
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hX.1
      by_cases hnN : n < N
      · left
        refine ⟨lt_of_le_of_lt ?_ hn.2, hX.2⟩
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hnN.le 1
      · right
        refine Set.mem_iUnion.mpr ⟨n - N, ?_⟩
        rw [Nat.add_sub_of_le (Nat.le_of_not_gt hnN)]
        exact ⟨hn, hX.2⟩
    have htail : volume (⋃ m : ℕ, C (N + m) ∩ Icc 0 H) ≤
        ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N * H) := by
      calc
        _ ≤ ∑' m : ℕ, volume (C (N + m) ∩ Icc 0 H) := measure_iUnion_le _
        _ ≤ ∑' m : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (N + m) * H) :=
          ENNReal.tsum_le_tsum fun m => hC (N + m) H hH
        _ = _ := geometric_prefix_tail N hH
    calc
      _ ≤ volume ({X | 1 / ((N : ℝ) + 1) < f X} ∩ Icc 0 H) +
          volume (⋃ m : ℕ, C (N + m) ∩ Icc 0 H) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (δ / 2 * H) + ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N * H) :=
        add_le_add hfront htail
      _ = ENNReal.ofReal (δ / 2 * H + 2 * (1 / 2 : ℝ) ^ N * H) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right hN.le hH
        linarith only [hh]
  let S : Set ℝ := (toMeasurable volume E)ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable volume E).compl
  have hSd : ∀ δ > 0, ∀ᶠ H : ℝ in atTop,
      volume (Sᶜ ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H) := by
    intro δ hδ
    filter_upwards [hE δ hδ] with H hH
    simpa only [S, compl_compl,
      Measure.measure_toMeasurable_inter_of_sFinite measurableSet_Icc E] using hH
  have hSf : ∀ n : ℕ, ∀ X : ℝ, X ∈ S → R n < X → f X ≤ 1 / ((n : ℝ) + 1) := by
    intro n X hXS hXR
    by_contra h
    have hXE : X ∈ E := Set.mem_iUnion.mpr ⟨n, hXR, lt_of_not_ge h⟩
    exact hXS (subset_toMeasurable volume E hXE)
  refine ⟨S, hSm, hSd, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro a ha
    have hlarge : ∀ᶠ X : ℝ in atTop ⊓ 𝓟 S, 1 ≤ X :=
      (eventually_ge_atTop (1 : ℝ)).filter_mono inf_le_left
    exact hlarge.mono fun X hX => ha.trans_le (hnonneg X hX)
  · intro b hb
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hb
    have hlarge : ∀ᶠ X : ℝ in atTop ⊓ 𝓟 S, R n < X :=
      (eventually_gt_atTop (R n)).filter_mono inf_le_left
    have hmem : ∀ᶠ X : ℝ in atTop ⊓ 𝓟 S, X ∈ S :=
      (show ∀ᶠ X : ℝ in 𝓟 S, X ∈ S by simp).filter_mono inf_le_right
    filter_upwards [hlarge, hmem] with X hX hXS
    exact (hSf n X hXS hX).trans_lt hn

#print axioms exists_measurable_densityOne_tendsto_zero_of_density_zero

end

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
