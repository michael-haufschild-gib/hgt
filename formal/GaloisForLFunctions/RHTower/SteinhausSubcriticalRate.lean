import GaloisForLFunctions.RHTower.SteinhausSubcritical

/-!
# The sub-critical rate function from below

If `Λ_α(λ) ≤ A'λ²` near the origin then the tilt `λ = q/(2A')` already gives
`I_α(q) ≥ q²/(4A')`.  Since `A'` may be taken arbitrarily close to the true constant
`A = (1−α)²/(4(1−2α))`, this is the lower half of the card's first regime.
-/

open Filter Topology Set

namespace HTGeometry

noncomputable section

/-- **The sub-critical rate function, from below.** -/
theorem eventually_le_rvRate_quad {α : ℝ} (hα : α < 1 / 2) {A' : ℝ}
    (hA' : (1 - α) ^ 2 / (4 * (1 - 2 * α)) < A') :
    ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), q ^ 2 / (4 * A') ≤ rvRate α q := by
  have hα1 : α < 1 := by linarith
  have hApos : (0 : ℝ) < A' := by
    have h1 : (0 : ℝ) < (1 - α) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 4 * (1 - 2 * α) := by linarith
    have : (0 : ℝ) < (1 - α) ^ 2 / (4 * (1 - 2 * α)) := by positivity
    linarith
  -- the cumulant is below `A' λ²` near the origin
  have hquad := tendsto_rvCumulant_div_sq hα
  have hEv : ∀ᶠ lam in nhdsWithin 0 (Set.Ioi (0 : ℝ)), rvCumulant α lam / lam ^ 2 < A' :=
    hquad.eventually (eventually_lt_nhds hA')
  have hmap : Tendsto (fun q : ℝ => q / (2 * A')) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun q : ℝ => q / (2 * A')) (nhds 0) (nhds (0 / (2 * A'))) :=
        (continuous_id.div_const _).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      have hq0 : 0 < q := hq
      have : 0 < q / (2 * A') := by positivity
      exact this
  have hpull := hmap.eventually hEv
  have hq1ev : ∀ᶠ q in nhdsWithin 0 (Set.Ioi (0 : ℝ)), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpull, self_mem_nhdsWithin, hq1ev] with q hqc hq0 hq1
  have hq : 0 < q := hq0
  set lam : ℝ := q / (2 * A') with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hbound : rvCumulant α lam ≤ A' * lam ^ 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)] at hqc
    linarith
  have hle := le_rvRate hα1 hq1 hlam0.le
  have hval : lam * q - A' * lam ^ 2 = q ^ 2 / (4 * A') := by
    rw [hlamdef]
    field_simp
    ring
  linarith [hle, hbound, hval]

end

end HTGeometry
