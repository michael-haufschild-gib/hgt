import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Sealing
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Reversal

/-!
# An explicit finite enclosure bound for a reversal-sensitive chord form

The six-endpoint difference has monotone capacity one and coefficient budget 28.
The general sealing estimate therefore proves exact capacity one at every depth
at least 84. This is a certified sufficient depth, not a minimality assertion.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem sixWindows_reversal_value (g : Fin 5 → ℝ) :
    familyValue sixWindows ![27,-1] g = reversalResponse (g 0) (g 1) (g 2) (g 3) (g 4) := by
  rw [sixWindows_value]
  simp only [weightedSixResponse,reversalResponse,neg_one_mul,sub_eq_add_neg]

theorem sixWindows_reversal_monotoneCapacity : monotoneCapacity sixWindows ![27,-1] = 1 := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    dsimp only
    rw [sixWindows_reversal_value]
    have h := monotone_reversal_bound ((normalizeProbe g) 0) ((normalizeProbe g) 1)
      ((normalizeProbe g) 2) ((normalizeProbe g) 3) ((normalizeProbe g) 4)
    have hv := normalizeProbe_budget g
    rw [variation_six] at hv
    have hn : 0 ≤ sixCost ((normalizeProbe g) 0) ((normalizeProbe g) 1)
        ((normalizeProbe g) 2) ((normalizeProbe g) 3) ((normalizeProbe g) 4) := by
      unfold sixCost; positivity
    have hp := pow_le_pow_left₀ hn hv 3
    rw [one_pow] at hp
    exact h.trans hp
  · let g : Fin 5 → ℝ := ![0,0,1,0,0]
    have h := monotoneCapacity_probe_bound sixWindows ![27,-1] g
    rw [sixWindows_reversal_value] at h
    simpa [monotoneProbe,normalizeProbe,variation,Fin.sum_univ_five,g,
      reversalResponse,separatedThree,rainbowThree] using h

theorem sixWindows_reversal_budget : coefficientBudget (![27,-1] : Fin 2 → ℝ) = 28 := by
  simp [coefficientBudget,Fin.sum_univ_two]
  ring

theorem sixWindows_reversal_sealed (k : ℕ) : sealedCapacity sixWindows ![27,-1] (k+84) = 1 := by
  apply le_antisymm
  · have hb := sealedCapacity_upper sixWindows ![27,-1] (k+83)
    rw [sixWindows_reversal_monotoneCapacity,sixWindows_reversal_budget] at hb
    have he : k+83+1 = k+84 := by omega
    rw [he] at hb
    apply hb.trans
    apply max_le le_rfl
    rw [Nat.cast_add]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ)+83+1)).mpr
    have hk : (0 : ℝ) ≤ k := by positivity
    push_cast
    nlinarith
  · simpa only [sixWindows_reversal_monotoneCapacity] using
      monotoneCapacity_le_sealed sixWindows (![27,-1] : Fin 2 → ℝ) (k+84)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
