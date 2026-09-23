import GaloisForLFunctions.RHTower.FiniteTwoLevelThirdMomentCeiling

/-!
# Large-count sixth-moment upper heads

The strict source spectral ceiling gives an upper two-level head beyond
every prescribed count.  This allows its count to dominate a previously
fixed positive lower head, so zero padding can put both in one finite
moment fiber.
-/

namespace RHTower

noncomputable section

theorem exists_twoLevelThirdMoment_gt_above
    {E F G : ℝ} (hE : 0 < E) (hF : 0 < F)
    (hhigh : F ≤ E ^ (2 : ℕ)) (hG : 0 ≤ G)
    (hstrict : G ^ (2 : ℕ) < F ^ (3 : ℕ)) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧ 3 ≤ N ∧ E ^ (2 : ℕ) / N < F ∧
      G < twoLevelLarge E F N ^ (3 : ℕ) +
        ((N : ℝ) - 1) * twoLevelSmall E F N ^ (3 : ℕ) := by
  have hD : 0 < F ^ (3 : ℕ) - G ^ (2 : ℕ) := sub_pos.mpr hstrict
  let T : ℝ := max (3 : ℝ) (max (E ^ (2 : ℕ) / F)
    (3 * F ^ (2 : ℕ) * E ^ (2 : ℕ) /
      (F ^ (3 : ℕ) - G ^ (2 : ℕ))))
  obtain ⟨N, hNbound⟩ := exists_nat_gt (max (Nmin : ℝ) T)
  have hNminReal : (Nmin : ℝ) < N :=
    lt_of_le_of_lt (le_max_left _ _) hNbound
  have hNmin : Nmin ≤ N := by exact_mod_cast hNminReal.le
  have hT : max (3 : ℝ) (max (E ^ (2 : ℕ) / F)
      (3 * F ^ (2 : ℕ) * E ^ (2 : ℕ) /
        (F ^ (3 : ℕ) - G ^ (2 : ℕ)))) < N := by
    change T < (N : ℝ)
    exact lt_of_le_of_lt (le_max_right _ _) hNbound
  have hNthree : (3 : ℝ) < N :=
    lt_of_le_of_lt (le_max_left _ _) hT
  have hN : 3 ≤ N := by exact_mod_cast hNthree.le
  have hNr : (0 : ℝ) < N := by linarith
  have hNfloorRatio : E ^ (2 : ℕ) / F < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hNcostRatio :
      3 * F ^ (2 : ℕ) * E ^ (2 : ℕ) /
        (F ^ (3 : ℕ) - G ^ (2 : ℕ)) < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hlow : E ^ (2 : ℕ) / N < F := by
    have h := (div_lt_iff₀ hF).1 hNfloorRatio
    exact (div_lt_iff₀ hNr).2 (by nlinarith)
  have hcost : 3 * F ^ (2 : ℕ) * (E ^ (2 : ℕ) / N) <
      F ^ (3 : ℕ) - G ^ (2 : ℕ) := by
    have h := (div_lt_iff₀ hD).1 hNcostRatio
    have h' :
        (3 * F ^ (2 : ℕ) * E ^ (2 : ℕ)) / N <
          F ^ (3 : ℕ) - G ^ (2 : ℕ) :=
      (div_lt_iff₀ hNr).2 (by nlinarith)
    calc
      3 * F ^ (2 : ℕ) * (E ^ (2 : ℕ) / N) =
          (3 * F ^ (2 : ℕ) * E ^ (2 : ℕ)) / N := by ring
      _ < F ^ (3 : ℕ) - G ^ (2 : ℕ) := h'
  have ht : 0 ≤ E ^ (2 : ℕ) / N := by positivity
  have hrest : 0 ≤
      (E ^ (2 : ℕ) / N) ^ (2 : ℕ) *
        (3 * F - E ^ (2 : ℕ) / N) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hmargin : G ^ (2 : ℕ) <
      (F - E ^ (2 : ℕ) / N) ^ (3 : ℕ) := by
    nlinarith [hrest, hcost]
  exact ⟨N, hNmin, hN, hlow,
    twoLevelThirdMoment_gt_of_margin hE (by omega) hlow hhigh hG hmargin⟩

end

end RHTower
