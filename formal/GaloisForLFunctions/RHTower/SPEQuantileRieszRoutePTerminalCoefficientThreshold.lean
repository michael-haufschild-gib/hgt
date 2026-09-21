import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCenteredShiftSign

/-!
# Exact threshold for Route-P's finite terminal coefficient

The source-fixed centering shift is negative, but its size is not controlled
by the finite-source results.  This file records the exact remaining scalar
condition: at a fixed head, the terminal coefficient is nonpositive precisely
below the square of the source centering shift.  Thus a cofinal negative
terminal mechanism necessarily uses moving heads whose negative shifts have
at least square-root scale.

This is a threshold classification, not a terminal-intertwiner construction.
-/

noncomputable section

open Filter

namespace RHTower

/-- At a fixed source head, terminal nonpositivity is exactly the square
threshold imposed by its canonical negative centering shift. -/
theorem speQuantileRiesz_terminalCoefficient_nonpos_iff (M K : ℕ) :
    Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ 0 ↔
      (M : ℝ) ≤ ccmActualHeadMatchedQuantileParabolicCenteredShift K ^ 2 := by
  let s : ℝ := ccmActualHeadMatchedQuantileParabolicCenteredShift K
  have hs : s < 0 := ccmActualHeadMatchedQuantileParabolicCenteredShift_neg K
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hroot : (Real.sqrt (M : ℝ)) ^ 2 = M := Real.sq_sqrt hM
  change Real.sqrt (M : ℝ) + s ≤ 0 ↔ (M : ℝ) ≤ s ^ 2
  constructor
  · intro h
    nlinarith [Real.sqrt_nonneg (M : ℝ)]
  · intro h
    by_contra hpos
    push Not at hpos
    nlinarith [Real.sqrt_nonneg (M : ℝ)]

/-- No fixed finite source head can keep the terminal coefficient nonpositive
at arbitrarily large terminal scales. -/
theorem speQuantileRiesz_terminalCoefficient_eventually_pos (K : ℕ) :
    ∀ᶠ M : ℕ in atTop,
      0 < Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K := by
  have hlarge : ∀ᶠ M : ℕ in Filter.atTop,
      ccmActualHeadMatchedQuantileParabolicCenteredShift K ^ 2 < (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (Filter.eventually_gt_atTop (ccmActualHeadMatchedQuantileParabolicCenteredShift K ^ 2))
  exact hlarge.mono fun M hM =>
    lt_of_not_ge fun hnonpos => not_lt_of_ge
      (speQuantileRiesz_terminalCoefficient_nonpos_iff M K |>.mp hnonpos) hM

end RHTower
