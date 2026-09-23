import GaloisForLFunctions.HTGeometry.ChargedStringTwoSiteThermalLimit

/-! # Exact unattained thermal supremum over actual growing finite wave modes -/
namespace GaloisForLFunctions.HTGeometry.CPV
noncomputable section

/-- All squared growth values realized by nonzero two-site wave states at fixed positive charge and thermal background. -/
def stringTwoSiteGrowthSet (h ell tau : ℝ) : Set ℝ :=
  {r | ∃ k m x : ℝ, ∃ ω : ℂ, ∃ v : ℂ × ℂ,
    v ≠ 0 ∧ stringTwoSitePencil k m (Real.exp h) ell tau x ω v = 0 ∧
      0 < ω.im ∧ r = ω.im ^ (2 : ℕ)}

/-- Every member of the explicit approaching sequence belongs to the actual mode-growth set. -/
theorem stringTwoSiteThermalLimitFrequency_growth_mem (h ell tau : ℝ) (j : ℕ) :
    (stringTwoSiteThermalLimitFrequency h ell tau j).im ^ (2 : ℕ) ∈ stringTwoSiteGrowthSet h ell tau := by
  have hm := stringTwoSiteThermalLimitVector_mode h ell tau j
  exact ⟨stringTwoSiteThermalLimitCoupling h ell tau j, 0, stringTwoSiteOptimalRadiusCoordinate ell,
    stringTwoSiteThermalLimitFrequency h ell tau j, stringTwoSiteThermalLimitVector h ell tau j,
    hm.1, hm.2.1, hm.2.2, rfl⟩

/-- The temperature-calibrated bound is the exact supremum over all actual positive-growth modes, couplings, masses, and doubled-radius samples. -/
theorem stringTwoSiteGrowthSet_isLUB (h ell tau : ℝ) :
    IsLUB (stringTwoSiteGrowthSet h ell tau) (stringTwoSiteThermalGrowthCeiling h ell tau) := by
  have hp : IsLUB (Set.range (fun j : ℕ => (stringTwoSiteThermalLimitFrequency h ell tau j).im ^ (2 : ℕ)))
      (stringTwoSiteThermalGrowthCeiling h ell tau) :=
    IsLUB.range_of_tendsto (fun j => (stringTwoSiteThermalLimitFrequency_growth_lt h ell tau j).le)
      (stringTwoSiteThermalLimitFrequency_growth_limit h ell tau)
  constructor
  · intro r hr
    rcases hr with ⟨k, m, x, ω, v, hv, hvp, hy, rfl⟩
    by_contra hn
    have hb : stringTwoSiteThermalGrowthCeiling h ell tau ≤ ω.im ^ (2 : ℕ) := by linarith
    exact stringTwoSite_no_growth_at_temperature_bound k m (Real.exp h) ell tau x
      ⟨ω, ⟨v, hv, hvp⟩, hy, hb⟩
  · intro b hb
    apply hp.2
    rintro r ⟨j, rfl⟩
    exact hb (stringTwoSiteThermalLimitFrequency_growth_mem h ell tau j)

/-- No finite actual wave mode attains the sharp thermal ceiling. -/
theorem stringTwoSiteGrowthSet_ceiling_not_mem (h ell tau : ℝ) :
    stringTwoSiteThermalGrowthCeiling h ell tau ∉ stringTwoSiteGrowthSet h ell tau := by
  rintro ⟨k, m, x, ω, v, hv, hvp, hy, he⟩
  exact stringTwoSite_no_growth_at_temperature_bound k m (Real.exp h) ell tau x
    ⟨ω, ⟨v, hv, hvp⟩, hy, by change stringTwoSiteThermalGrowthCeiling h ell tau ≤ ω.im ^ (2 : ℕ); linarith⟩

/-- The attainable set is nonempty and contains strictly positive rates below its unattained supremum. -/
theorem stringTwoSiteGrowthSet_positive_member (h ell tau : ℝ) :
    ∃ r ∈ stringTwoSiteGrowthSet h ell tau, 0 < r ∧ r < stringTwoSiteThermalGrowthCeiling h ell tau := by
  refine ⟨(stringTwoSiteThermalLimitFrequency h ell tau 0).im ^ (2 : ℕ),
    stringTwoSiteThermalLimitFrequency_growth_mem h ell tau 0, ?_,
    stringTwoSiteThermalLimitFrequency_growth_lt h ell tau 0⟩
  exact sq_pos_of_pos (stringTwoSiteThermalLimitFrequency_mode h ell tau 0).2

end
end GaloisForLFunctions.HTGeometry.CPV
