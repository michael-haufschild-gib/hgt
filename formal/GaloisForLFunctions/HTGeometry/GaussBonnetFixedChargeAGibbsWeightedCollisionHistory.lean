import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInputSharpExponent

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- An exact input-selected threshold decides convergence of every geometrically weighted collision history. -/
theorem egbFixedChargeAGibbsCollisionExcess_weighted_summable_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m : ℕ => (q ^ 2) ^ m * egbFixedChargeAGibbsCollisionExcess n m β E) ↔
      q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E < 1 := by
  have hr := (egbFixedChargeAGibbsDominantCollisionRate_bounds n β E).1
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  constructor
  · intro hs
    by_contra hlt
    have hp : 1 ≤ q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E := le_of_not_gt hlt
    have hrp : 0 < egbFixedChargeAGibbsDominantCollisionRate n β E :=
      lt_of_le_of_ne hr (by intro h; rw [← h, mul_zero] at hp; norm_num at hp)
    have hW := (egbFixedChargeAGibbsDominantModeEnergy_pos_iff n β E).mpr hrp
    have ht := ((summable_nat_add_iff 1).mpr hs).tendsto_atTop_zero
    have hl (m : ℕ) : egbFixedChargeAGibbsDominantModeEnergy n β E ≤
        (q ^ 2) ^ (m + 1) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
      calc
        _ ≤ (q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E) ^ (m + 1) *
            egbFixedChargeAGibbsDominantModeEnergy n β E := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (one_le_pow₀ hp : (1 : ℝ) ≤
              (q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E) ^ (m + 1)) hW.le
        _ = (q ^ 2) ^ (m + 1) *
            (egbFixedChargeAGibbsDominantCollisionRate n β E ^ (m + 1) *
              egbFixedChargeAGibbsDominantModeEnergy n β E) := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (egbFixedChargeAGibbsCollisionExcess_dominant_bounds n m β E).1 (by positivity)
    have hz : egbFixedChargeAGibbsDominantModeEnergy n β E ≤ 0 :=
      ge_of_tendsto ht (Filter.Eventually.of_forall hl)
    linarith
  · intro hlt
    have hs0 : Summable (fun m : ℕ =>
        (q ^ 2 * egbFixedChargeAGibbsDominantCollisionRate n β E) ^ m *
          (egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E)) :=
      (summable_geometric_of_lt_one (mul_nonneg (sq_nonneg q) hr) hlt).mul_right _
    have hs := (summable_nat_add_iff 1).mpr hs0
    apply (summable_nat_add_iff 1).mp
    apply hs.of_nonneg_of_le
    · intro m
      exact mul_nonneg (by positivity) (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E)
    · intro m
      calc
        _ ≤ (q ^ 2) ^ (m + 1) *
            (egbFixedChargeAGibbsDominantCollisionRate n β E ^ (m + 1) *
              (egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E)) :=
          mul_le_mul_of_nonneg_left
            (egbFixedChargeAGibbsCollisionExcess_dominant_bounds n m β E).2 (by positivity)
        _ = _ := by rw [mul_pow]; ring

end
end GaloisForLFunctions.HTGeometry
