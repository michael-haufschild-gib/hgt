import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateInfinityFailure

/-!
# Nonnegative combinations of shifted ground states fail the folded test at both ends

A nonnegative nonzero combination `c₁ ω_a + c₂ ω_b` is a folded supersolution at `x` only if one of
its constituents is. Since every shifted ground state is a strict folded subsolution on a right
neighbourhood of `0` and on a half line `[X, ∞)`, so is every such combination, on the intersection
of the two origin windows and beyond the larger of the two thresholds.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- A nonnegative nonzero combination of two shifted ground states is a strict folded subsolution on
a right neighbourhood of the origin. -/
theorem exists_origin_window_combination_foldedGenerator_lt_potential {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ ∨ 0 < c₂) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x, 0 < x → x < x₀ →
      foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x <
        riemannKernelReal x * Real.cosh (x / 2) *
          (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x) := by
  obtain ⟨xa, hxa, hA⟩ := exists_origin_window_foldedGenerator_lt_potential ha
  obtain ⟨xb, hxb, hB⟩ := exists_origin_window_foldedGenerator_lt_potential hb
  refine ⟨min xa xb, lt_min hxa hxb, fun x hx hxm => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  rcases exists_constituent_supersolution_of_combination ha hb hx hc₁ hc₂ hc hcon with h | h
  · exact absurd ((foldedSupersolution_shiftedGroundState_iff ha hx).mpr h)
      (not_le.mpr (hA x hx (lt_of_lt_of_le hxm (min_le_left _ _))))
  · exact absurd ((foldedSupersolution_shiftedGroundState_iff hb hx).mpr h)
      (not_le.mpr (hB x hx (lt_of_lt_of_le hxm (min_le_right _ _))))

/-- A nonnegative nonzero combination of two shifted ground states is a strict folded subsolution on
a half line `[X, ∞)`. -/
theorem exists_infinity_window_combination_foldedGenerator_lt_potential {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ ∨ 0 < c₂) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x →
      foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x <
        riemannKernelReal x * Real.cosh (x / 2) *
          (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x) := by
  obtain ⟨Xa, hXa, hA⟩ := exists_infinity_window_foldedGenerator_lt_potential ha
  obtain ⟨Xb, hXb, hB⟩ := exists_infinity_window_foldedGenerator_lt_potential hb
  refine ⟨max Xa Xb, lt_of_lt_of_le hXa (le_max_left _ _), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le hXa (le_max_left _ _)) hx
  by_contra hcon
  rw [not_lt] at hcon
  rcases exists_constituent_supersolution_of_combination ha hb hx0 hc₁ hc₂ hc hcon with h | h
  · exact absurd ((foldedSupersolution_shiftedGroundState_iff ha hx0).mpr h)
      (not_le.mpr (hA x (le_trans (le_max_left _ _) hx)))
  · exact absurd ((foldedSupersolution_shiftedGroundState_iff hb hx0).mpr h)
      (not_le.mpr (hB x (le_trans (le_max_right _ _) hx)))

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
