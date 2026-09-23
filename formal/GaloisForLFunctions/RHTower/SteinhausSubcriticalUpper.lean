import GaloisForLFunctions.RHTower.SteinhausCumulantSlope

/-!
# The sub-critical rate function from above

Below `δ` the cumulant dominates `A''λ²`, which caps every tilt at `q²/(4A'')`; beyond `δ` the
nondecreasing slope makes `Λ_α(λ) ≥ λ·Λ_α(δ)/δ`, so those tilts contribute nothing at all once
`q < Λ_α(δ)/δ`.  Together with the lower bound this is the card's first regime.
-/

open Filter Topology Set

namespace HTGeometry

noncomputable section

/-- **The sub-critical rate function, from above.** -/
theorem eventually_rvRate_le_quad {α : ℝ} (hα : α < 1 / 2) {A'' : ℝ} (hA''0 : 0 < A'')
    (hA'' : A'' < (1 - α) ^ (2 : ℕ) / (4 * (1 - 2 * α))) :
    ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), rvRate α q ≤ q ^ (2 : ℕ) / (4 * A'') := by
  have hα1 : α < 1 := by linarith
  -- the cumulant dominates `A'' λ²` near the origin
  have hquad := tendsto_rvCumulant_div_sq hα
  have hEv : ∀ᶠ lam in nhdsWithin 0 (Set.Ioi (0 : ℝ)), A'' < rvCumulant α lam / lam ^ (2 : ℕ) :=
    hquad.eventually (eventually_gt_nhds hA'')
  obtain ⟨s, hs, hsP⟩ := Filter.eventually_iff_exists_mem.1 hEv
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hs
  have hu0 : (0 : ℝ) < u := hu
  set δ : ℝ := u / 2 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδu : δ < u := by rw [hδdef]; linarith
  have hlow : ∀ lam : ℝ, 0 < lam → lam ≤ δ → A'' * lam ^ (2 : ℕ) ≤ rvCumulant α lam := by
    intro lam hlam0 hlamδ
    have hmem : lam ∈ Set.Ioo (0 : ℝ) u := ⟨hlam0, by linarith⟩
    have h := hsP lam (hsub hmem)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  -- the slope beyond `δ`
  set m : ℝ := rvCumulant α δ / δ with hm
  have hm0 : 0 < m := by
    rw [hm]
    exact div_pos (rvCumulant_pos hα1 hδ0) hδ0
  have hq1ev : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), q < min 1 m :=
    (eventually_lt_nhds (lt_min (by norm_num) hm0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq1ev, self_mem_nhdsWithin] with q hqlt hq0
  have hq : 0 < q := hq0
  have hq1 : q < 1 := lt_of_lt_of_le hqlt (min_le_left _ _)
  have hqm : q < m := lt_of_lt_of_le hqlt (min_le_right _ _)
  refine csSup_le (rvLegendreSet_nonempty α q) ?_
  rintro y ⟨lam, hlam, rfl⟩
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · rw [← hzero, rvCumulant_zero]
    have : (0 : ℝ) ≤ q ^ (2 : ℕ) / (4 * A'') := by positivity
    simpa using this
  · rcases le_or_gt lam δ with hle | hgt
    · have hb := hlow lam hpos hle
      have hkey : lam * q - A'' * lam ^ (2 : ℕ) ≤ q ^ (2 : ℕ) / (4 * A'') := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * A'' * lam - q), hA''0]
      linarith
    · have hslope := rvCumulant_slope_mono hα1 hδ0 hgt.le
      have hid : lam / δ * rvCumulant α δ = lam * m := by
        rw [hm]
        field_simp
      rw [hid] at hslope
      have : lam * q - rvCumulant α lam ≤ lam * q - lam * m := by linarith
      have hneg : lam * q - lam * m ≤ 0 := by nlinarith [hpos, hqm]
      have hnn : (0 : ℝ) ≤ q ^ (2 : ℕ) / (4 * A'') := by positivity
      linarith

end

end HTGeometry
