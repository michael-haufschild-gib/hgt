import GaloisForLFunctions.RHTower.FiniteTwoLevelMomentCarrier

/-!
# A finite two-level head reaches every strict cubic spectral target

The large atom of an exact first/second moment carrier has square at least
`F - E² / N`.  Thus a strict target inequality `G² < F³` has a finite witness:
the carrier's third power sum eventually exceeds `G`.  This is an explicit
finite-size consequence of the strict sixth spectral ceiling, with no limit
or numerical evaluation.
-/

namespace RHTower

noncomputable section

/-- A quantitative cubic margin for a fixed positive two-level carrier. -/
theorem twoLevelThirdMoment_gt_of_margin
    {E F G : ℝ} {N : ℕ}
    (hE : 0 < E) (hN : 2 ≤ N)
    (hlow : E ^ (2 : ℕ) / N < F)
    (hhigh : F ≤ E ^ (2 : ℕ))
    (hG : 0 ≤ G)
    (hmargin : G ^ (2 : ℕ) < (F - E ^ (2 : ℕ) / N) ^ (3 : ℕ)) :
    G < twoLevelLarge E F N ^ (3 : ℕ) +
      ((N : ℝ) - 1) * twoLevelSmall E F N ^ (3 : ℕ) := by
  let L := twoLevelLarge E F N
  let S := twoLevelSmall E F N
  have hNr : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := twoLevelLarge_pos hE hN
  have hS : 0 ≤ S := twoLevelSmall_nonneg hE hN hlow hhigh
  have hfirst : L + ((N : ℝ) - 1) * S = E :=
    twoLevel_firstMoment hN
  have hsecond : L ^ (2 : ℕ) + ((N : ℝ) - 1) * S ^ (2 : ℕ) = F :=
    twoLevel_secondMoment hN hlow
  have hSupper : S ≤ E / N := by
    dsimp only [S, twoLevelSmall]
    apply (div_le_iff₀ hNr).2
    have hcancel : E / (N : ℝ) * N = E := by field_simp
    rw [hcancel]
    linarith [twoLevelDeviation_nonneg E F N]
  have hsmallMass : ((N : ℝ) - 1) * S ≤ E := by
    linarith
  have hsmallEnergy : ((N : ℝ) - 1) * S ^ (2 : ℕ) ≤
      E ^ (2 : ℕ) / N := by
    calc
      ((N : ℝ) - 1) * S ^ (2 : ℕ) =
          (((N : ℝ) - 1) * S) * S := by ring
      _ ≤ E * S := mul_le_mul_of_nonneg_right hsmallMass hS
      _ ≤ E * (E / N) := mul_le_mul_of_nonneg_left hSupper hE.le
      _ = E ^ (2 : ℕ) / N := by ring
  have hLsq : F - E ^ (2 : ℕ) / N ≤ L ^ (2 : ℕ) := by
    linarith
  have hcube := pow_le_pow_left₀ (sub_pos.mpr hlow).le hLsq 3
  have hLcube : G < L ^ (3 : ℕ) := by
    have hsix : G ^ (2 : ℕ) < (L ^ (3 : ℕ)) ^ (2 : ℕ) := by
      nlinarith [hcube]
    nlinarith [pow_pos hL 3]
  have htail : 0 ≤ ((N : ℝ) - 1) * S ^ (3 : ℕ) := by
    apply mul_nonneg
    · have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      linarith
    · exact pow_nonneg hS 3
  nlinarith

/-- Every target strictly below the cubic spectral ceiling is exceeded by
some finite exact first/second moment carrier. -/
theorem exists_twoLevelThirdMoment_gt_of_strict_ceiling
    {E F G : ℝ} (hE : 0 < E) (hF : 0 < F)
    (hhigh : F ≤ E ^ (2 : ℕ)) (hG : 0 ≤ G)
    (hstrict : G ^ (2 : ℕ) < F ^ (3 : ℕ)) :
    ∃ N : ℕ, 3 ≤ N ∧ E ^ (2 : ℕ) / N < F ∧
      G < twoLevelLarge E F N ^ (3 : ℕ) +
        ((N : ℝ) - 1) * twoLevelSmall E F N ^ (3 : ℕ) := by
  have hD : 0 < F ^ (3 : ℕ) - G ^ (2 : ℕ) := sub_pos.mpr hstrict
  obtain ⟨N, hNbound⟩ := exists_nat_gt
    (max (3 : ℝ) (max (E ^ (2 : ℕ) / F)
      (3 * F ^ (2 : ℕ) * E ^ (2 : ℕ) /
        (F ^ (3 : ℕ) - G ^ (2 : ℕ)))))
  have hNthree : (3 : ℝ) < N :=
    lt_of_le_of_lt (le_max_left _ _) hNbound
  have hN : 3 ≤ N := by exact_mod_cast hNthree.le
  have hNr : (0 : ℝ) < N := by linarith
  have hNfloorRatio : E ^ (2 : ℕ) / F < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hNbound
  have hNcostRatio :
      3 * F ^ (2 : ℕ) * E ^ (2 : ℕ) /
        (F ^ (3 : ℕ) - G ^ (2 : ℕ)) < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hNbound
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
  exact ⟨N, hN, hlow,
    twoLevelThirdMoment_gt_of_margin hE (by omega) hlow hhigh hG hmargin⟩

end

end RHTower
