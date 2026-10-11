import GaloisForLFunctions.RHTower.WeilLogShiftMomentProbabilities

/-! Finite positive normalization retains quantitative l1 control. -/

open scoped BigOperators
noncomputable section
namespace RHTower

/-- Only the first profile needs entrywise nonnegativity; the comparison sum must be positive. -/
theorem finiteWeil_profile_normalization_l1 {ι : Type} [Fintype ι]
    (f q : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hF : 0 < ∑ i, f i) (hG : 0 < ∑ i, q i) :
    (∑ i, |f i / (∑ j, f j) - q i / (∑ j, q j)|) ≤
      2 * (∑ i, |f i - q i|) / (∑ i, q i) := by
  let F := ∑ i, f i
  let G := ∑ i, q i
  let D := ∑ i, |f i - q i|
  change 0 < F at hF
  change 0 < G at hG
  have hd : |G - F| ≤ D := by
    change |(∑ i, q i) - ∑ i, f i| ≤ ∑ i, |f i - q i|
    rw [abs_sub_comm, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hi (i : ι) : |f i / F - q i / G| ≤
      |f i - q i| / G + f i * |G - F| / (F * G) := by
    have heq : f i / F - q i / G =
        (f i - q i) / G + f i * (G - F) / (F * G) := by field_simp; ring
    rw [heq]
    calc
      _ ≤ |(f i - q i) / G| + |f i * (G - F) / (F * G)| := abs_add_le _ _
      _ = _ := by
        rw [abs_div, abs_div, abs_mul, abs_of_nonneg (hf i),
          abs_of_pos hG, abs_of_pos (mul_pos hF hG)]
  change (∑ i, |f i / F - q i / G|) ≤ 2 * D / G
  calc
    _ ≤ ∑ i, (|f i - q i| / G + f i * |G - F| / (F * G)) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = D / G + |G - F| / G := by
      simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul]
      change D * G⁻¹ + F * |G - F| * (F * G)⁻¹ = D * G⁻¹ + |G - F| * G⁻¹
      field_simp
    _ ≤ D / G + D / G := add_le_add le_rfl (div_le_div_of_nonneg_right hd hG.le)
    _ = _ := by ring

end RHTower
