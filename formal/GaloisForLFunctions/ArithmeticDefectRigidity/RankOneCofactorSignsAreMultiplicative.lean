import GaloisForLFunctions.ArithmeticDefectRigidity.RankOneCofactorMagnitudesArePowers

/-!
# Rank-one cofactor signs are multiplicative

A nonaugmentation actual rank-one character factors as one real power
times a multiplicative sign character. Its source norm law fixes the power.
-/
section

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- An actual rank-one character is augmentation or a multiplicative sign times one
Archimedean power. No choice of the signs is imposed. -/
theorem rankOneCharacter_eq_augmentation_or_signed_rpow {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hL : Module.finrank ℂ (Hilbert L) = 1) :
    (∀ p : ℕ+, p ≠ 1 → rankOneCharacter L hL p = 0) ∨
      ∃ s : ℝ, 1 / 2 ≤ s ∧ ∃ η : ℕ+ →* ℝ,
        (∀ p, η p = 1 ∨ η p = -1) ∧
        ∀ p, rankOneCharacter L hL p = η p * (p : ℝ) ^ (-s) := by
  rcases rankOneCharacter_eq_augmentation_or_abs_rpow L hL with hzero | ⟨s, hs, habs⟩
  · exact Or.inl hzero
  · let χ := rankOneCharacter L hL
    let η : ℕ+ →* ℝ :=
      { toFun := fun p => χ p / |χ p|
        map_one' := by simp
        map_mul' := fun p q => by
          simp only [map_mul, abs_mul]
          exact (div_mul_div_comm _ _ _ _).symm }
    have hne (p : ℕ+) : χ p ≠ 0 := by
      have hpos : 0 < |χ p| := by
        rw [habs p]
        exact Real.rpow_pos_of_pos (by positivity) _
      exact abs_pos.mp hpos
    refine Or.inr ⟨s, hs, η, fun p => ?_, fun p => ?_⟩
    · change χ p / |χ p| = 1 ∨ χ p / |χ p| = -1
      rcases lt_or_gt_of_ne (hne p) with hneg | hpos
      · right
        rw [abs_of_neg hneg, div_neg, div_self (hne p)]
      · left
        rw [abs_of_pos hpos, div_self (hne p)]
    · change χ p = (χ p / |χ p|) * (p : ℝ) ^ (-s)
      rw [← habs p, div_mul_cancel₀ _ (abs_ne_zero.mpr (hne p))]

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.rankOneCharacter_eq_augmentation_or_signed_rpow
end
end

