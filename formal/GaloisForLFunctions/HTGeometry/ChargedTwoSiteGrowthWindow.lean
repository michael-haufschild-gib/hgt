import GaloisForLFunctions.HTGeometry.ChargedTwoSiteGrowingModes

/-! # Exact instability window and constructed growing frequencies -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Signed squared growth branch of the exact charged wave determinant. -/
def chargedTwoSiteGrowthSquare (k m d : ℝ) : ℝ :=
  Real.sqrt ((Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2) -
    (chargedTwoSiteBase k m + d ^ 2)

/-- The signed branch is positive exactly in an intermediate charge-gap interval. -/
theorem chargedTwoSiteGrowthSquare_pos_iff (k m d : ℝ) :
    0 < chargedTwoSiteGrowthSquare k m d ↔ m ^ 2 < d ^ 2 ∧ d ^ 2 < m ^ 2 + 2 * Real.exp k := by
  have hs : 0 ≤ chargedTwoSiteBase k m + d ^ 2 := by
    nlinarith [chargedTwoSiteBase_pos k m, sq_nonneg d]
  unfold chargedTwoSiteGrowthSquare
  rw [sub_pos, Real.lt_sqrt hs]
  have hid : (Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2 -
      (chargedTwoSiteBase k m + d ^ 2) ^ 2 =
        (Real.exp k) ^ 2 - (chargedTwoSiteBase k m - d ^ 2) ^ 2 := by ring
  constructor
  · intro h
    have hsq : (chargedTwoSiteBase k m - d ^ 2) ^ 2 < (Real.exp k) ^ 2 := by nlinarith [hid]
    have hb := abs_lt_of_sq_lt_sq' hsq (Real.exp_pos k).le
    unfold chargedTwoSiteBase at hb
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hu⟩
    have hb : -Real.exp k < chargedTwoSiteBase k m - d ^ 2 ∧
        chargedTwoSiteBase k m - d ^ 2 < Real.exp k := by
      unfold chargedTwoSiteBase
      constructor <;> linarith
    have hsq := sq_lt_sq' hb.1 hb.2
    nlinarith [hid]

/-- The signed branch satisfies the exact centered determinant equation for all charge values. -/
theorem chargedTwoSiteGrowthSquare_equation (k m d : ℝ) :
    (chargedTwoSiteGrowthSquare k m d + chargedTwoSiteBase k m + d ^ 2) ^ 2 =
      (Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2 := by
  have h := Real.sq_sqrt (chargedTwoSiteDiscriminant_pos k m d).le
  unfold chargedTwoSiteGrowthSquare
  nlinarith [h]

/-- Every actual growing mode has the unique positive squared growth branch. -/
theorem chargedTwoSite_growing_frequency_classification (k m c d : ℝ) (ω : ℂ) :
    (ChargedTwoSiteHasMode k m c d ω ∧ 0 < ω.im) ↔
      ω.re = c ∧ 0 < ω.im ∧ ω.im ^ 2 = chargedTwoSiteGrowthSquare k m d := by
  rw [chargedTwoSite_growing_mode_iff]
  constructor
  · rintro ⟨hx, hy, hg⟩
    refine ⟨hx, hy, ?_⟩
    have hs : 0 < ω.im ^ 2 + chargedTwoSiteBase k m + d ^ 2 := by
      nlinarith [chargedTwoSiteBase_pos k m, sq_nonneg ω.im, sq_nonneg d]
    have hr : Real.sqrt ((Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2) =
        ω.im ^ 2 + chargedTwoSiteBase k m + d ^ 2 := by
      rw [← hg, Real.sqrt_sq_eq_abs, abs_of_pos hs]
    unfold chargedTwoSiteGrowthSquare
    linarith
  · rintro ⟨hx, hy, hg⟩
    refine ⟨hx, hy, ?_⟩
    rw [hg]
    exact chargedTwoSiteGrowthSquare_equation k m d

/-- Canonical upper-half-plane candidate, with zero imaginary part outside the open instability region. -/
def chargedTwoSiteGrowingFrequency (k m c d : ℝ) : ℂ :=
  ⟨c, Real.sqrt (chargedTwoSiteGrowthSquare k m d)⟩

/-- The canonical frequency is an actual growing mode exactly on the predicted open parameter window. -/
theorem chargedTwoSiteGrowingFrequency_mode_iff (k m c d : ℝ) :
    (ChargedTwoSiteHasMode k m c d (chargedTwoSiteGrowingFrequency k m c d) ∧
      0 < (chargedTwoSiteGrowingFrequency k m c d).im) ↔
        m ^ 2 < d ^ 2 ∧ d ^ 2 < m ^ 2 + 2 * Real.exp k := by
  rw [chargedTwoSite_growing_frequency_classification]
  change (c = c ∧ 0 < Real.sqrt (chargedTwoSiteGrowthSquare k m d) ∧
    Real.sqrt (chargedTwoSiteGrowthSquare k m d) ^ 2 = chargedTwoSiteGrowthSquare k m d) ↔ _
  constructor
  · rintro ⟨_, hp, _⟩
    exact (chargedTwoSiteGrowthSquare_pos_iff k m d).1 (Real.sqrt_pos.mp hp)
  · intro hw
    have hp := (chargedTwoSiteGrowthSquare_pos_iff k m d).2 hw
    exact ⟨rfl, Real.sqrt_pos.mpr hp, Real.sq_sqrt hp.le⟩

/-- There are actual nonzero growing modes exactly for intermediate charge, rather than for all sufficiently large charge. -/
theorem chargedTwoSite_exists_growing_mode_iff (k m c d : ℝ) :
    (∃ ω : ℂ, ChargedTwoSiteHasMode k m c d ω ∧ 0 < ω.im) ↔
      m ^ 2 < d ^ 2 ∧ d ^ 2 < m ^ 2 + 2 * Real.exp k := by
  constructor
  · rintro ⟨ω, hω⟩
    have h := (chargedTwoSite_growing_frequency_classification k m c d ω).1 hω
    apply (chargedTwoSiteGrowthSquare_pos_iff k m d).1
    rw [← h.2.2]
    exact sq_pos_of_pos h.2.1
  · intro hw
    exact ⟨chargedTwoSiteGrowingFrequency k m c d,
      (chargedTwoSiteGrowingFrequency_mode_iff k m c d).2 hw⟩

/-- The neutral model has no growing mode of the actual operator, including zero mass. -/
theorem chargedTwoSite_neutral_no_growing_mode (k m c : ℝ) :
    ¬ ∃ ω : ℂ, ChargedTwoSiteHasMode k m c 0 ω ∧ 0 < ω.im := by
  rw [chargedTwoSite_exists_growing_mode_iff]
  rintro ⟨h, _⟩
  nlinarith [sq_nonneg m]

/-- Both boundary faces have a real central-frequency mode, and no other charge gap does. -/
theorem chargedTwoSite_central_mode_iff_threshold (k m c d : ℝ) :
    ChargedTwoSiteHasMode k m c d (c : ℂ) ↔
      d ^ 2 = m ^ 2 ∨ d ^ 2 = m ^ 2 + 2 * Real.exp k := by
  rw [chargedTwoSiteHasMode_iff_determinant]
  have hd : chargedTwoSiteDeterminant k m c d (c : ℂ) =
      (((m ^ 2 - d ^ 2) * (m ^ 2 + 2 * Real.exp k - d ^ 2) : ℝ) : ℂ) := by
    unfold chargedTwoSiteDeterminant chargedTwoSiteBase
    push_cast
    ring
  rw [hd]
  norm_cast
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

end
end GaloisForLFunctions.HTGeometry
