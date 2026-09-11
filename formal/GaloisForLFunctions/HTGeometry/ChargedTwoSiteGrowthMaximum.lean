import GaloisForLFunctions.HTGeometry.ChargedTwoSiteGrowthWindow

/-! # A sharp coupling-controlled maximum of actual charged-mode growth -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Exact completed-square growth budget, valid for the signed branch on every parameter stratum. -/
theorem chargedTwoSiteGrowthSquare_budget (k m d : ℝ) :
    (d ^ 2 - chargedTwoSiteBase k m + chargedTwoSiteGrowthSquare k m d) ^ 2 +
      4 * chargedTwoSiteBase k m * chargedTwoSiteGrowthSquare k m d = (Real.exp k) ^ 2 := by
  have h := chargedTwoSiteGrowthSquare_equation k m d
  nlinarith [h]

/-- Coupling and mass impose a sharp global upper bound on the signed squared growth rate. -/
theorem chargedTwoSiteGrowthSquare_le_maximum (k m d : ℝ) :
    chargedTwoSiteGrowthSquare k m d ≤ (Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m) := by
  rw [le_div_iff₀ (mul_pos (by norm_num) (chargedTwoSiteBase_pos k m))]
  have h := chargedTwoSiteGrowthSquare_budget k m d
  nlinarith [sq_nonneg (d ^ 2 - chargedTwoSiteBase k m + chargedTwoSiteGrowthSquare k m d)]

/-- The unique squared charge-gap location attaining the sharp growth maximum. -/
def chargedTwoSiteOptimalGapSquare (k m : ℝ) : ℝ :=
  chargedTwoSiteBase k m - (Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m)

/-- The maximizing charge gap is a genuine positive parameter for every coupling and mass. -/
theorem chargedTwoSiteOptimalGapSquare_pos (k m : ℝ) :
    0 < chargedTwoSiteOptimalGapSquare k m := by
  have hh := chargedTwoSiteBase_pos k m
  have hk := Real.exp_pos k
  have hle : Real.exp k ≤ chargedTwoSiteBase k m := by unfold chargedTwoSiteBase; nlinarith [sq_nonneg m]
  have hsq := mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ chargedTwoSiteBase k m + Real.exp k by linarith)
  unfold chargedTwoSiteOptimalGapSquare
  rw [sub_pos, div_lt_iff₀ (mul_pos (by norm_num) hh)]
  nlinarith [sq_pos_of_pos hh]

/-- Equality in the growth bound identifies exactly the maximizing squared charge gap. -/
theorem chargedTwoSiteGrowthSquare_maximum_iff (k m d : ℝ) :
    chargedTwoSiteGrowthSquare k m d = (Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m) ↔
      d ^ 2 = chargedTwoSiteOptimalGapSquare k m := by
  have hh := chargedTwoSiteBase_pos k m
  have hc : (4 * chargedTwoSiteBase k m) *
      ((Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m)) = (Real.exp k) ^ 2 := by
    field_simp [hh.ne']
    <;> ring
  constructor
  · intro hg
    have hb := chargedTwoSiteGrowthSquare_budget k m d
    have hz : (d ^ 2 - chargedTwoSiteBase k m + chargedTwoSiteGrowthSquare k m d) ^ 2 = 0 := by
      rw [hg] at hb ⊢
      nlinarith [hc]
    have hl := sq_eq_zero_iff.mp hz
    unfold chargedTwoSiteOptimalGapSquare
    linarith
  · intro hd
    have hD : (Real.exp k) ^ 2 + 4 * chargedTwoSiteBase k m * d ^ 2 =
        (2 * chargedTwoSiteBase k m) ^ 2 := by
      rw [hd]
      unfold chargedTwoSiteOptimalGapSquare
      field_simp [hh.ne']
      <;> ring
    unfold chargedTwoSiteGrowthSquare
    rw [hD, Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (by norm_num) hh), hd]
    unfold chargedTwoSiteOptimalGapSquare
    ring

/-- A positive exact charge-gap maximizer, without a parameter-side hypothesis. -/
def chargedTwoSiteOptimalGap (k m : ℝ) : ℝ := Real.sqrt (chargedTwoSiteOptimalGapSquare k m)

/-- The constructed gap attains the optimal squared parameter exactly. -/
theorem chargedTwoSiteOptimalGap_sq (k m : ℝ) :
    chargedTwoSiteOptimalGap k m ^ 2 = chargedTwoSiteOptimalGapSquare k m :=
  Real.sq_sqrt (chargedTwoSiteOptimalGapSquare_pos k m).le

/-- The constructed parameter attains the sharp growth bound exactly. -/
theorem chargedTwoSiteOptimalGap_growth (k m : ℝ) :
    chargedTwoSiteGrowthSquare k m (chargedTwoSiteOptimalGap k m) =
      (Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m) :=
  (chargedTwoSiteGrowthSquare_maximum_iff k m _).2 (chargedTwoSiteOptimalGap_sq k m)

/-- The sharp bound is achieved by an actual nonzero growing state of the finite wave operator. -/
theorem chargedTwoSite_fastest_mode_exists (k m c : ℝ) :
    ∃ ω : ℂ, ∃ v : ℂ × ℂ, v ≠ 0 ∧
      chargedTwoSitePencil k m c (chargedTwoSiteOptimalGap k m) ω v = 0 ∧
      0 < ω.im ∧ ω.im ^ 2 = (Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m) := by
  have hg : 0 < chargedTwoSiteGrowthSquare k m (chargedTwoSiteOptimalGap k m) := by
    rw [chargedTwoSiteOptimalGap_growth]
    exact div_pos (sq_pos_of_pos (Real.exp_pos k)) (mul_pos (by norm_num) (chargedTwoSiteBase_pos k m))
  have hw := (chargedTwoSiteGrowthSquare_pos_iff k m (chargedTwoSiteOptimalGap k m)).1 hg
  have hm := (chargedTwoSiteGrowingFrequency_mode_iff k m c (chargedTwoSiteOptimalGap k m)).2 hw
  obtain ⟨v, hv, hp⟩ := hm.1
  refine ⟨chargedTwoSiteGrowingFrequency k m c (chargedTwoSiteOptimalGap k m), v, hv, hp, hm.2, ?_⟩
  have hr := (chargedTwoSite_growing_frequency_classification k m c (chargedTwoSiteOptimalGap k m) _).1 hm
  rw [hr.2.2, chargedTwoSiteOptimalGap_growth]

end
end GaloisForLFunctions.HTGeometry
