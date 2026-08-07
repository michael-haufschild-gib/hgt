import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Measure of a set that is thin in every cell

A set of reals whose points are pairwise within `w` lies in an interval of length `2w`, so its measure
is at most `2w`; no measurability is needed, since only monotonicity of the outer measure is used.

If instead the set is only thin *cell by cell* — its intersection with every interval of length `h`
has pairwise distances at most `w` — then covering `[-T, T]` by `⌈2T/h⌉` such cells bounds its measure
there by `(2T/h + 1)·2w`.

This is the device that turns a pointwise separation statement, valid only within one window, into a
measure bound over a long range.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **A pairwise-close set of reals is thin.** -/
theorem volume_le_of_pairwise_dist_le {A : Set ℝ} {w : ℝ} (_hw : 0 ≤ w)
    (h : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ w) :
    volume A ≤ ENNReal.ofReal (2 * w) := by
  rcases Set.eq_empty_or_nonempty A with rfl | ⟨a, ha⟩
  · simp
  · have hsub : A ⊆ Set.Icc (a - w) (a + w) := by
      intro x hx
      have hxa := abs_le.mp (h x hx a ha)
      exact ⟨by linarith [hxa.1], by linarith [hxa.2]⟩
    refine le_trans (measure_mono hsub) ?_
    rw [Real.volume_Icc]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith

/-- **A set thin in every cell of length `h` is thin on `[-T, T]`.**  Covering the range by `⌈2T/h⌉`
cells and adding the per-cell bounds. -/
theorem volume_inter_Icc_le_of_cells {A : Set ℝ} {T h w : ℝ} (hT : 0 ≤ T) (hh : 0 < h)
    (hw : 0 ≤ w)
    (hcell : ∀ a : ℝ, ∀ x ∈ A ∩ Set.Icc a (a + h), ∀ y ∈ A ∩ Set.Icc a (a + h),
      |x - y| ≤ w) :
    volume (A ∩ Set.Icc (-T) T) ≤ ENNReal.ofReal ((2 * T / h + 1) * (2 * w)) := by
  classical
  set N : ℕ := ⌊2 * T / h⌋₊ + 1 with hN
  have hcover : A ∩ Set.Icc (-T) T ⊆
      ⋃ k ∈ Finset.range N, (A ∩ Set.Icc (-T + (k : ℝ) * h) (-T + (k : ℝ) * h + h)) := by
    intro t ht
    obtain ⟨htA, htI⟩ := ht
    have htT : -T ≤ t := htI.1
    have htT' : t ≤ T := htI.2
    set k : ℕ := ⌊(t + T) / h⌋₊ with hk
    have hnn : (0 : ℝ) ≤ (t + T) / h := by
      have : (0 : ℝ) ≤ t + T := by linarith
      positivity
    have hk1 : ((k : ℝ)) ≤ (t + T) / h := Nat.floor_le hnn
    have hk2 : (t + T) / h < ((k : ℝ)) + 1 := Nat.lt_floor_add_one _
    have hkh1 : ((k : ℝ)) * h ≤ t + T := by
      rw [← le_div_iff₀ hh]
      exact hk1
    have hkh2 : t + T ≤ ((k : ℝ)) * h + h := by
      have := (div_lt_iff₀ hh).mp hk2
      linarith
    have h2T : (t + T) / h ≤ 2 * T / h := by
      have hinv : (0 : ℝ) ≤ h⁻¹ := (inv_pos.mpr hh).le
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) hinv
    have hkN : k < N := by
      rw [hN, hk]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor h2T)
    refine Set.mem_biUnion (Finset.mem_range.mpr hkN) ⟨htA, ?_⟩
    exact ⟨by linarith, by linarith⟩
  refine le_trans (measure_mono hcover) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hterm : ∀ k ∈ Finset.range N,
      volume (A ∩ Set.Icc (-T + (k : ℝ) * h) (-T + (k : ℝ) * h + h)) ≤
        ENNReal.ofReal (2 * w) := by
    intro k _
    exact volume_le_of_pairwise_dist_le hw (hcell (-T + (k : ℝ) * h))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast N,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hNle : ((N : ℝ)) ≤ 2 * T / h + 1 := by
    rw [hN]
    push_cast
    have h2 : (0 : ℝ) ≤ 2 * T / h := by positivity
    have hfl := Nat.floor_le h2
    linarith
  have hw2 : (0 : ℝ) ≤ 2 * w := by linarith
  exact mul_le_mul_of_nonneg_right hNle hw2

end GaloisForLFunctions.HTGeometry
