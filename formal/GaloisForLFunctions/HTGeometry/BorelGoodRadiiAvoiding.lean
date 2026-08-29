import GaloisForLFunctions.HTGeometry.BorelGoodRadii

/-!
# Good radii avoiding a null set

The Borel exceptional set has measure at most two, so a window of length four always contains a good
radius — and, since a null set cannot cover the rest of the window, a good radius outside any
prescribed null set.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

/-- **A good radius outside a null set.** -/
theorem exists_good_radius_avoiding {T : ℝ → ℝ} (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r)
    {Z : Set ℝ} (hZ : volume Z = 0) (a : ℝ) :
    ∃ r : ℝ, a ≤ r ∧ r ∉ Z ∧ T (r + (T r)⁻¹) < 2 * T r := by
  by_contra hcon
  push_neg at hcon
  have hsub : Icc a (a + 4) ⊆ Z ∪ {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r)⁻¹)} := by
    intro r hr
    by_cases hrZ : r ∈ Z
    · exact Or.inl hrZ
    · exact Or.inr ⟨hr.1, hcon r hr.1 hrZ⟩
  have hvol := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at hvol
  have hunion : volume (Z ∪ {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r)⁻¹)}) ≤ 2 := by
    refine le_trans (measure_union_le _ _) ?_
    rw [hZ, zero_add]
    exact GaloisForLFunctions.Nevanlinna.borel_growth_monotone hmono hT1 a
  have hfin : ENNReal.ofReal (a + 4 - a) ≤ 2 := le_trans hvol hunion
  have harith : a + 4 - a = 4 := by ring
  rw [harith] at hfin
  have h4 : (4 : ENNReal) ≤ 2 := by
    rw [show ((4 : ENNReal)) = ENNReal.ofReal 4 by simp]
    exact hfin
  norm_num at h4

/-- **A sequence of good radii outside a null set, tending to infinity.** -/
theorem exists_good_radius_seq_avoiding {T : ℝ → ℝ} (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r)
    {Z : Set ℝ} (hZ : volume Z = 0) :
    ∃ rn : ℕ → ℝ, Filter.Tendsto rn Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, (n : ℝ) ≤ rn n ∧ rn n ∉ Z ∧ T (rn n + (T (rn n))⁻¹) < 2 * T (rn n) := by
  choose g hg using fun n : ℕ => exists_good_radius_avoiding hmono hT1 hZ (n : ℝ)
  refine ⟨g, ?_, fun n => hg n⟩
  refine Filter.tendsto_atTop_mono (fun n : ℕ => (hg n).1) ?_
  exact tendsto_natCast_atTop_atTop

end GaloisForLFunctions.HTGeometry
