import GaloisForLFunctions.HTGeometry.ChargedTwoSiteGrowthWindow

/-! # Exact positive defect in the charged-mode variance bound -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The electrostatic variance deficit factors into explicit positive mass and charge contributions. -/
theorem chargedTwoSiteGrowthSquare_variance_defect (k m d : ℝ) :
    (d ^ (2 : ℕ) - chargedTwoSiteGrowthSquare k m d) *
      (chargedTwoSiteBase k m + 2 * d ^ (2 : ℕ) +
        Real.sqrt ((Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k m * d ^ (2 : ℕ))) =
      m ^ (2 : ℕ) * (2 * Real.exp k + m ^ (2 : ℕ)) + 4 * d ^ (4 : ℕ) := by
  have h := Real.sq_sqrt (chargedTwoSiteDiscriminant_pos k m d).le
  unfold chargedTwoSiteGrowthSquare
  unfold chargedTwoSiteBase at h ⊢
  nlinarith [h]

/-- The signed growth branch never exceeds the two-point electrostatic variance. -/
theorem chargedTwoSiteGrowthSquare_le_variance (k m d : ℝ) :
    chargedTwoSiteGrowthSquare k m d ≤ d ^ (2 : ℕ) := by
  have hd := chargedTwoSiteGrowthSquare_variance_defect k m d
  have hp : 0 < chargedTwoSiteBase k m + 2 * d ^ (2 : ℕ) +
      Real.sqrt ((Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k m * d ^ (2 : ℕ)) := by
    nlinarith [chargedTwoSiteBase_pos k m, sq_nonneg d,
      Real.sqrt_nonneg ((Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k m * d ^ (2 : ℕ))]
  have hm := mul_nonneg (sq_nonneg m) (show 0 ≤ 2 * Real.exp k + m ^ (2 : ℕ) by nlinarith [Real.exp_pos k, sq_nonneg m])
  have h4 : 0 ≤ d ^ (4 : ℕ) := by nlinarith [sq_nonneg (d ^ (2 : ℕ))]
  by_contra hn
  have hg : 0 < chargedTwoSiteGrowthSquare k m d - d ^ (2 : ℕ) := by linarith
  have hh := mul_pos hg hp
  nlinarith [hd]

/-- Equality in the variance bound occurs only at the massless neutral point, where there is no growing mode. -/
theorem chargedTwoSiteGrowthSquare_variance_equality_iff (k m d : ℝ) :
    chargedTwoSiteGrowthSquare k m d = d ^ (2 : ℕ) ↔ m = 0 ∧ d = 0 := by
  constructor
  · intro he
    have hd := chargedTwoSiteGrowthSquare_variance_defect k m d
    rw [he, sub_self, zero_mul] at hd
    have hp : 0 < 2 * Real.exp k + m ^ (2 : ℕ) := by nlinarith [Real.exp_pos k, sq_nonneg m]
    have hm := mul_nonneg (sq_nonneg m) hp.le
    have h4 : 0 ≤ d ^ (4 : ℕ) := by nlinarith [sq_nonneg (d ^ (2 : ℕ))]
    have hm0 : m = 0 := by
      by_contra h
      have hpos := mul_pos (sq_pos_of_ne_zero h) hp
      nlinarith [hd]
    have hd0 : d = 0 := by
      by_contra h
      have hpos : 0 < d ^ (4 : ℕ) := by nlinarith [sq_pos_of_pos (sq_pos_of_ne_zero h)]
      nlinarith [hd]
    exact ⟨hm0, hd0⟩
  · rintro ⟨rfl, rfl⟩
    simp [chargedTwoSiteGrowthSquare, chargedTwoSiteBase, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos k)]

/-- No actual growing mode saturates or exceeds the electrostatic variance budget. -/
theorem chargedTwoSite_no_growth_at_or_above_variance (k m c d : ℝ) :
    ¬ ∃ ω : ℂ, ChargedTwoSiteHasMode k m c d ω ∧ 0 < ω.im ∧ d ^ (2 : ℕ) ≤ ω.im ^ (2 : ℕ) := by
  rintro ⟨ω, hm, hy, hb⟩
  have hc := (chargedTwoSite_growing_frequency_classification k m c d ω).1 ⟨hm, hy⟩
  have hg := chargedTwoSiteGrowthSquare_le_variance k m d
  have he : chargedTwoSiteGrowthSquare k m d = d ^ (2 : ℕ) := by linarith [hc.2.2]
  have hz := (chargedTwoSiteGrowthSquare_variance_equality_iff k m d).1 he
  have hw := (chargedTwoSite_exists_growing_mode_iff k m c d).1 ⟨ω, hm, hy⟩
  rw [hz.1, hz.2] at hw
  norm_num at hw

end
end GaloisForLFunctions.HTGeometry
