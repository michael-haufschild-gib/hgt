import GaloisForLFunctions.RHTower.OneInequalitySuffices

/-!
# Order facts about the critical strip

Elementary interval facts about abscissae:

* an abscissa `σ ∈ (½, 1)` lies strictly between `½` and any abscissa `> 1` (`shift_crosses`,
  `no_route_avoiding`);
* the interval `(½, 1)` is nonempty (`interior_nonempty`);
* `1 ≤ N ≤ S` gives `1 ≤ S` (`inside_strip_only_counts`).

These are not statements about `ζ`.  The file does not show that unconditional inputs cannot bound
the prime-counting error, nor that the only unconditional information inside the strip is a count:
the corpus proves interior zero-free regions (`riemannZeta_ne_zero_vinogradovKorobov`), interior size
bounds (`norm_riemannZeta_fiveSevenths_le`) and zero-density estimates.
-/

open Set

noncomputable section

namespace RHTower

/-- `½ < σ < 1` restated. -/
theorem regions_separated {σ : ℝ} (hlow : 1 / 2 < σ) (hhigh : σ < 1) :
    1 / 2 < σ ∧ σ < 1 := ⟨hlow, hhigh⟩

/-- An abscissa in `(½, 1)` lies strictly between `½` and any `σ₁ > 1`. -/
theorem shift_crosses {σ₁ σ₂ σ : ℝ} (h1 : 1 < σ₁) (h2 : σ₂ = 1 / 2)
    (hσ : 1 / 2 < σ ∧ σ < 1) : σ₂ < σ ∧ σ < σ₁ := by
  refine ⟨?_, ?_⟩
  · rw [h2]; exact hσ.1
  · linarith [hσ.2, h1]

/-- An abscissa in `(½, 1)` is neither `≥ σ₁ > 1` nor `≤ ½`. -/
theorem no_route_avoiding {σ₁ σ : ℝ} (h1 : 1 < σ₁) (hσ : 1 / 2 < σ ∧ σ < 1) :
    ¬ (σ₁ ≤ σ ∨ σ ≤ 1 / 2) := by
  intro h
  rcases h with h | h
  · linarith [hσ.2, h1]
  · linarith [hσ.1]

/-- The interval `(½, 1)` is nonempty. -/
theorem interior_nonempty : ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 := ⟨3 / 4, by norm_num, by norm_num⟩

/-- `1 ≤ N ≤ S` gives `1 ≤ S`. -/
theorem inside_strip_only_counts {N S : ℝ} (hN : 1 ≤ N) (hbound : N ≤ S) : 1 ≤ S :=
  le_trans hN hbound

end RHTower
