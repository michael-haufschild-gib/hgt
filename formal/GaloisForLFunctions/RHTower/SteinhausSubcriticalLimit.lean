import GaloisForLFunctions.RHTower.SteinhausSubcriticalUpper

/-!
# The sub-critical regime of the rate function

Combining the two halves gives the first line of the card's `(6)`:

`I_α(q)/q² → (1 − 2α)/(1 − α)²`   as `q → 0⁺`,   for `0 ≤ α < 1/2`.
-/

open Filter Topology Set

namespace HTGeometry

noncomputable section

theorem rvQuadConst_pos {α : ℝ} (hα : α < 1 / 2) :
    0 < (1 - α) ^ (2 : ℕ) / (4 * (1 - 2 * α)) := by
  have h0 : (0 : ℝ) < 1 - α := by linarith
  have h1 : (0 : ℝ) < (1 - α) ^ (2 : ℕ) := pow_pos h0 2
  have h2 : (0 : ℝ) < 4 * (1 - 2 * α) := by linarith
  exact div_pos h1 h2

theorem rvQuadConst_inv {α : ℝ} (hα : α < 1 / 2) :
    1 / (4 * ((1 - α) ^ (2 : ℕ) / (4 * (1 - 2 * α)))) = (1 - 2 * α) / (1 - α) ^ (2 : ℕ) := by
  have h0 : (0 : ℝ) < 1 - α := by linarith
  have h1 : ((1 : ℝ) - α) ^ (2 : ℕ) ≠ 0 := (pow_pos h0 2).ne'
  have h2 : (1 : ℝ) - 2 * α ≠ 0 := by linarith
  field_simp

/-- **The sub-critical regime of the rate function.** -/
theorem tendsto_rvRate_div_sq {α : ℝ} (h0 : 0 ≤ α) (hα : α < 1 / 2) :
    Tendsto (fun q : ℝ => rvRate α q / q ^ (2 : ℕ)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds ((1 - 2 * α) / (1 - α) ^ (2 : ℕ))) := by
  have hα1 : α < 1 := by linarith
  set A : ℝ := (1 - α) ^ (2 : ℕ) / (4 * (1 - 2 * α)) with hA
  have hA0 : 0 < A := rvQuadConst_pos hα
  have hinv : 1 / (4 * A) = (1 - 2 * α) / (1 - α) ^ (2 : ℕ) := rvQuadConst_inv hα
  have hq1ev : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  rw [← hinv]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    rcases le_or_gt c 0 with hcneg | hc0
    · filter_upwards [hq1ev, self_mem_nhdsWithin] with q hq1 hqm
      have hq : 0 < q := hqm
      have hpos : 0 < rvRate α q := rvRate_pos h0 hα1 hq hq1
      have : (0 : ℝ) < rvRate α q / q ^ (2 : ℕ) := by positivity
      linarith
    · obtain ⟨c', hcc', hc'⟩ := exists_between hc
      have hc'0 : 0 < c' := lt_trans hc0 hcc'
      have hA' : A < 1 / (4 * c') := by
        rw [lt_div_iff₀ (by positivity)] at hc'
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have hev := eventually_le_rvRate_quad hα (A' := 1 / (4 * c')) (by rw [← hA]; exact hA')
      filter_upwards [hev, self_mem_nhdsWithin] with q hq hqm
      have hqpos : 0 < q := hqm
      have hid : q ^ (2 : ℕ) / (4 * (1 / (4 * c'))) = c' * q ^ (2 : ℕ) := by field_simp
      rw [hid] at hq
      rw [lt_div_iff₀ (by positivity)]
      have hstrict : c * q ^ (2 : ℕ) < c' * q ^ (2 : ℕ) :=
        mul_lt_mul_of_pos_right hcc' (by positivity)
      linarith
  · intro c hc
    have hc0 : 0 < c := lt_trans (by positivity) hc
    obtain ⟨c', hc'c, hcc'⟩ := exists_between hc
    have hc'0 : 0 < c' := lt_trans (by positivity) hc'c
    have hA'' : 1 / (4 * c') < A := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hc'c
      linarith
    have hev := eventually_rvRate_le_quad hα (A'' := 1 / (4 * c')) (by positivity)
      (by rw [← hA]; exact hA'')
    filter_upwards [hev, self_mem_nhdsWithin] with q hq hqm
    have hqpos : 0 < q := hqm
    have hid : q ^ (2 : ℕ) / (4 * (1 / (4 * c'))) = c' * q ^ (2 : ℕ) := by field_simp
    rw [hid] at hq
    rw [div_lt_iff₀ (by positivity)]
    have hstrict : c' * q ^ (2 : ℕ) < c * q ^ (2 : ℕ) :=
      mul_lt_mul_of_pos_right hcc' (by positivity)
    linarith

end

end HTGeometry
