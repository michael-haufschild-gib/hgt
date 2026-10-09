import GaloisForLFunctions.RHTower.Sieve.UnitBlockFrequencyComparison
import GaloisForLFunctions.RHTower.Sieve.UnitBlockFrequencyDecay

/-!
# Poisson summation for the unit block, and the lattice sums it produces

**Poisson.**  For `1 ≤ N < N' ≤ 2N` and `t ≥ 0`,
`∑_{N < n ≤ N'} n^{-1-it} = ∑_{k ∈ ℤ} ubFreq N N' t k`, the series converging absolutely
(`mtWattUnitBlock_eq_tsum_ubFreq`).  The smoothed summand is continuous with compact support and
its Fourier coefficients decay like `k^{-2}` (`exists_norm_ubFreq_le_decay`), so Mathlib's Poisson
formula applies at the origin.

**Lattice sums.**  The frequency bounds of `UnitBlockFrequencyBounds` and
`UnitBlockFrequencyComparison` are harmonic in the distance from a few real edges.  Over integers
`k` at distance between `1` and `L` from an edge `κ`, `∑ 1/|κ − k| ≤ 1 + log L` on each side
(`sum_one_div_sub_le`, `sum_one_div_sub_le'`): `k ↦ ⌊κ − k⌋` is injective and dominated by the
reciprocal.  An open interval of length `3` contains at most three integers
(`card_le_three_of_mem_Ioo`), and `∑_{|k| > V} k^{-2} ≤ 4/(V + 1)` over every finite set of such `k`
(`sum_inv_sq_le_of_lt_abs`).
-/

open Complex Set MeasureTheory Filter
open GaloisForLFunctions.HTGeometry
open scoped Real FourierTransform

namespace RHTower.Sieve

noncomputable section

variable {N N' : ℕ}

/-- The Fourier coefficients of the smoothed unit block are absolutely summable. -/
theorem summable_norm_ubFreq (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {t : ℝ}
    (ht : 0 ≤ t) : Summable fun k : ℤ => ‖ubFreq N N' t k‖ := by
  obtain ⟨K, _, hK⟩ := exists_norm_ubFreq_le_decay
  have hg : Summable fun k : ℤ => K * (1 + t) ^ 2 * (1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow.2 one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [eventually_cofinite_ne 0] with k hk
  rw [norm_norm, mul_one_div]
  exact hK N N' t k hN hNN' hN' ht hk

/-- **Poisson summation for the unit block.** -/
theorem mtWattUnitBlock_eq_tsum_ubFreq (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {t : ℝ}
    (ht : 0 ≤ t) : mtWattUnitBlock N N' t = ∑' k : ℤ, ubFreq N N' t k := by
  have hF : ∀ n : ℤ, 𝓕 (ubKernel N N' t) n = ubFreq N N' t (-n) := by
    intro n
    rw [← fourier_ubKernel_neg hNN'.le t (-n)]
    have e : (-(((-n : ℤ) : ℝ))) = (n : ℝ) := by push_cast; ring
    rw [e]
  have hFsum : Summable fun n : ℤ => 𝓕 (ubKernel N N' t) n := by
    simp_rw [hF]
    exact (Summable.of_norm (summable_norm_ubFreq hN hNN' hN' ht)).comp_injective neg_injective
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_ubKernel t)
    one_lt_two (ubKernel_isBigO_cocompact t 2) hFsum 0
  simp only [zero_add, AddCircle.coe_zero, fourier_eval_zero, mul_one] at hP
  rw [← tsum_ubKernel_eq hN t, hP]
  simp_rw [hF]
  exact (Equiv.neg ℤ).tsum_eq (fun k => ubFreq N N' t k)

/-! ## Lattice sums -/

/-- **Harmonic sum to the left of an edge.**  If `1 ≤ κ − k ≤ L` for all `k ∈ S`, then
`∑_{k ∈ S} 1/(κ − k) ≤ 1 + log L`. -/
theorem sum_one_div_sub_le {κ L : ℝ} (hL : 1 ≤ L) (S : Finset ℤ)
    (hS : ∀ k ∈ S, 1 ≤ κ - k ∧ κ - k ≤ L) :
    ∑ k ∈ S, 1 / (κ - k) ≤ 1 + Real.log L := by
  classical
  set j : ℤ → ℕ := fun k => ⌊κ - k⌋₊ with hj
  have hj1 : ∀ k ∈ S, 1 ≤ j k := fun k hk => Nat.le_floor (by exact_mod_cast (hS k hk).1)
  have hjL : ∀ k ∈ S, j k ≤ ⌊L⌋₊ := fun k hk => Nat.floor_le_floor (hS k hk).2
  have hjle : ∀ k ∈ S, (j k : ℝ) ≤ κ - k := fun k hk => Nat.floor_le (by linarith [(hS k hk).1])
  have hinj : Set.InjOn j S := by
    intro k hk k' hk' hkk'
    have h1 : (⌊κ - k⌋₊ : ℤ) = ⌊κ - k⌋ := Int.natCast_floor_eq_floor (by linarith [(hS k hk).1])
    have h2 : (⌊κ - k'⌋₊ : ℤ) = ⌊κ - k'⌋ := Int.natCast_floor_eq_floor (by linarith [(hS k' hk').1])
    have : ⌊κ - k⌋ = ⌊κ - k'⌋ := by rw [← h1, ← h2]; exact_mod_cast hkk'
    rw [Int.floor_sub_intCast, Int.floor_sub_intCast] at this
    linarith
  calc ∑ k ∈ S, 1 / (κ - k) ≤ ∑ k ∈ S, 1 / (j k : ℝ) := by
        refine Finset.sum_le_sum fun k hk => one_div_le_one_div_of_le ?_ (hjle k hk)
        exact_mod_cast (hj1 k hk)
    _ = ∑ m ∈ S.image j, 1 / (m : ℝ) :=
        (Finset.sum_image (f := fun m : ℕ => 1 / (m : ℝ)) hinj).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊L⌋₊, 1 / (m : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => by positivity
        intro m hm
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_Icc.2 ⟨hj1 k hk, hjL k hk⟩
    _ = (harmonic ⌊L⌋₊ : ℝ) := by rw [harmonic_eq_sum_Icc]
    _ ≤ 1 + Real.log ⌊L⌋₊ := harmonic_le_one_add_log _
    _ ≤ 1 + Real.log L := by
        have h1 : (0 : ℝ) < ⌊L⌋₊ := by exact_mod_cast Nat.floor_pos.2 hL
        gcongr
        exact Nat.floor_le (by linarith)

/-- **Harmonic sum to the right of an edge.**  If `1 ≤ k − κ ≤ L` for all `k ∈ S`, then
`∑_{k ∈ S} 1/(k − κ) ≤ 1 + log L`. -/
theorem sum_one_div_sub_le' {κ L : ℝ} (hL : 1 ≤ L) (S : Finset ℤ)
    (hS : ∀ k ∈ S, 1 ≤ k - κ ∧ k - κ ≤ L) :
    ∑ k ∈ S, 1 / (k - κ) ≤ 1 + Real.log L := by
  classical
  have h := sum_one_div_sub_le (κ := -κ) hL (S.map (Equiv.neg ℤ).toEmbedding) fun k hk => by
    obtain ⟨k', hk', rfl⟩ := Finset.mem_map.1 hk
    have := hS k' hk'
    simp only [Equiv.toEmbedding_apply, Equiv.neg_apply, Int.cast_neg]
    constructor <;> linarith [this.1, this.2]
  rw [Finset.sum_map] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) h
  simp only [Equiv.toEmbedding_apply, Equiv.neg_apply, Int.cast_neg]
  ring

/-- An open interval of length `3` contains at most three integers. -/
theorem card_le_three_of_mem_Ioo {α : ℝ} (S : Finset ℤ) (hS : ∀ k ∈ S, α < k ∧ (k : ℝ) < α + 3) :
    S.card ≤ 3 := by
  have hsub : S ⊆ Finset.Icc (⌊α⌋ + 1) (⌊α⌋ + 3) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hS k hk
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · have := Int.floor_lt.2 h1; omega
    · have : k - 3 ≤ ⌊α⌋ := Int.le_floor.2 (by push_cast; linarith)
      omega
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Int.card_Icc]; omega

/-- **The inverse-square tail.**  Over any finite set of integers `k` with `|k| > V`,
`∑ k^{-2} ≤ 4/(V + 1)`. -/
theorem sum_inv_sq_le_of_lt_abs (V : ℕ) (s : Finset ℤ) (hs : ∀ k ∈ s, (V : ℤ) < |k|) :
    ∑ k ∈ s, 1 / (k : ℝ) ^ 2 ≤ 4 / ((V : ℝ) + 1) := by
  set M : ℕ := s.sup Int.natAbs + 1 with hM
  have hpart : ∀ (σ : ℤ → Prop) [DecidablePred σ], (∀ k ∈ s, σ k → 0 < k ∨ k < 0) →
      (∀ k ∈ s, ∀ k' ∈ s, σ k → σ k' → k.natAbs = k'.natAbs → k = k') →
      ∑ k ∈ s.filter σ, 1 / (k : ℝ) ^ 2 ≤ 2 / ((V : ℝ) + 1) := by
    intro σ _ _ hinj
    have hinj' : Set.InjOn Int.natAbs ↑(s.filter σ) := by
      intro k hk k' hk' h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hk hk'
      exact hinj k hk.1 k' hk'.1 hk.2 hk'.2 h
    calc ∑ k ∈ s.filter σ, 1 / (k : ℝ) ^ 2
        = ∑ k ∈ s.filter σ, ((k.natAbs : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [one_div, Nat.cast_natAbs, Int.cast_abs, sq_abs]
      _ = ∑ n ∈ (s.filter σ).image Int.natAbs, ((n : ℝ) ^ 2)⁻¹ :=
          (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj').symm
      _ ≤ ∑ n ∈ Finset.Ioo V M, ((n : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => by positivity
          intro n hn
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hn
          have hks := (Finset.mem_filter.1 hk).1
          refine Finset.mem_Ioo.2 ⟨?_, ?_⟩
          · have := hs k hks
            have h2 : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
            omega
          · have : k.natAbs ≤ s.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hks
            omega
      _ ≤ 2 / ((V : ℝ) + 1) := sum_Ioo_inv_sq_le V M
  have hpos := hpart (fun k => 0 < k) (fun k _ h => Or.inl h) fun k _ k' _ h h' e => by omega
  have hneg := hpart (fun k => ¬ 0 < k) (fun k hk h => Or.inr (by
    have := hs k hk; push Not at h
    rcases lt_or_eq_of_le h with h | h
    · exact h
    · subst h; exfalso; simp at this; omega)) fun k _ k' _ h h' e => by omega
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => 0 < k)]
  have e : (4 : ℝ) / ((V : ℝ) + 1) = 2 / ((V : ℝ) + 1) + 2 / ((V : ℝ) + 1) := by ring
  linarith

end

end RHTower.Sieve
