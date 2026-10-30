import GaloisForLFunctions.CompletedArithmeticForms.TerminalCompletion

/-!
# Free-terminal dual payment for the complete Euler-deletion source

The actual cumulative error controls both its omitted infinite tail and the
terminal mass inserted by finite-source completion. Their difference gives a
two-sided joint cutoff allowance. The resulting mixed-coupling bound retains
local weighted variation and the exact terminal mass discrepancy.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower.DeletionAveragedDivisor _root_.RHTower.DeletionCutoffAverage

/-- Every actual cumulative increment mass has the literal modular-source bound. -/
theorem errorIncrement_prefix_abs_le {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (T : ℕ) :
    |∑ j ∈ Icc 1 T, errorIncrement X M j| ≤ (M : ℝ) + 1 := by
  by_cases hT : T = 0
  · subst T
    simp
  rw [← error_eq_cumulative hXM.le (Nat.pos_of_ne_zero hT)]
  have h := (abs_sub (1 : ℝ) (modular X M T)).trans
    (add_le_add le_rfl (abs_modular_le hX hXM T))
  simpa only [abs_one, add_comm] using h

/-- Completing the truncated actual source has an explicit two-sided error against its full energy. -/
theorem fullErrorEnergy_finiteSource_error_le {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (T : ℕ) :
    |fullErrorEnergy X M - finiteSourceEnergy (errorIncrement X M) T| ≤
      ((M : ℝ) + 1) ^ 2 / ((T : ℝ) + 1) := by
  obtain ⟨hl, hu⟩ := fullErrorEnergy_truncation_bounds hX hXM T
  have hm : (∑ j ∈ Icc 1 T, errorIncrement X M j) ^ 2 / ((T : ℝ) + 1) ≤
      ((M : ℝ) + 1) ^ 2 / ((T : ℝ) + 1) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (errorIncrement_prefix_abs_le hX hXM T) 2
  have hm0 : 0 ≤ (∑ j ∈ Icc 1 T, errorIncrement X M j) ^ 2 / ((T : ℝ) + 1) :=
    div_nonneg (sq_nonneg _) (by positivity)
  rw [abs_le, finiteSourceEnergy]
  constructor <;> linarith only [hl, hu, hm, hm0]

/-- The complete Euler source pays free-terminal variation and retains its mass-discrepancy gain. -/
theorem fullErrorEnergy_freeTerminal_schur_bound_with_mass {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (b : ℕ → ℝ) (T : ℕ) :
    2 * (∑ j ∈ Icc 1 T, errorIncrement X M j * b j) - fullErrorEnergy X M ≤
      finiteSourceDualCost b T -
        ((∑ j ∈ Icc 1 T, errorIncrement X M j) - (T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1) +
          ((M : ℝ) + 1) ^ 2 / ((T : ℝ) + 1) := by
  have hs := finiteSourceEnergy_schur_bound_with_mass (errorIncrement X M) b T
  have he := (abs_le.mp (fullErrorEnergy_finiteSource_error_le hX hXM T)).1
  linarith only [hs, he]

/-- Actual infinite-source coupling has a free-terminal local cost with a joint cutoff allowance. -/
theorem fullErrorEnergy_freeTerminal_schur_bound {X M : ℕ}
    (hX : 1 ≤ X) (hXM : X < M) (b : ℕ → ℝ) (T : ℕ) :
    2 * (∑ j ∈ Icc 1 T, errorIncrement X M j * b j) - fullErrorEnergy X M ≤
      finiteSourceDualCost b T + ((M : ℝ) + 1) ^ 2 / ((T : ℝ) + 1) := by
  have hs := fullErrorEnergy_freeTerminal_schur_bound_with_mass hX hXM b T
  have hn : 0 ≤ ((∑ j ∈ Icc 1 T, errorIncrement X M j) - (T : ℝ) * b T) ^ 2 /
      ((T : ℝ) + 1) := div_nonneg (sq_nonneg _) (by positivity)
  linarith only [hs, hn]

/-- A joint source and coordinate horizon gives any prescribed terminal-completion allowance. -/
theorem fullErrorEnergy_finiteSource_error_le_of_horizon {X M T : ℕ} {δ : ℝ}
    (hX : 1 ≤ X) (hXM : X < M)
    (hT : ((M : ℝ) + 1) ^ 2 ≤ δ * ((T : ℝ) + 1)) :
    |fullErrorEnergy X M - finiteSourceEnergy (errorIncrement X M) T| ≤ δ :=
  (fullErrorEnergy_finiteSource_error_le hX hXM T).trans
    ((div_le_iff₀ (by positivity)).mpr hT)

#print axioms errorIncrement_prefix_abs_le
#print axioms fullErrorEnergy_finiteSource_error_le
#print axioms fullErrorEnergy_freeTerminal_schur_bound_with_mass
#print axioms fullErrorEnergy_freeTerminal_schur_bound

end GaloisForLFunctions.CompletedArithmeticForms
