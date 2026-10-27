import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryXiZeroHasALocalQuadraticTerminal
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip

/-!
# Right-hand quadratic terminals

Reflection in the critical line puts each quadratic terminal on the right
without changing its depth, ordinate, or terminal property.
-/

open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Every right-hand Xi zero has a right-hand quadratic terminal nearby,
at least as far from the critical line. -/
theorem exists_right_xi_quadratic_terminal_near :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re →
      ∃ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re ∧
        |xiZeroHeight p - xiZeroHeight q| ≤ C * Real.log (|xiZeroHeight q| + 3) ∧
        xiZeroDepth q ≤ xiZeroDepth p ∧
        ∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
          xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2 := by
  obtain ⟨C, hC, hterminal⟩ := exists_xi_quadratic_terminal_near
  refine ⟨C, hC, fun q hq => ?_⟩
  obtain ⟨p, hpnear, hpdepth, hpterminal⟩ := hterminal q
  have hqdepth : 0 < xiZeroDepth q := by
    rw [xiZeroDepth, abs_of_pos (by linarith)]
    linarith
  have hpdepthpos : 0 < xiZeroDepth p := lt_of_lt_of_le hqdepth hpdepth
  by_cases hp : 1 / 2 ≤ (p.1 : ℂ).re
  · have hpdepth' : xiZeroDepth p = (p.1 : ℂ).re - 1 / 2 := by
      rw [xiZeroDepth, abs_of_nonneg (by linarith)]
    have hp' : 1 / 2 < (p.1 : ℂ).re := by linarith
    exact ⟨p, hp', hpnear, hpdepth, hpterminal⟩
  · let p' := xiZeroCopyLineConjEquiv p
    have hp're : ((p'.1 : ℂ)).re = 1 - (p.1 : ℂ).re := by
      dsimp only [p']
      rw [xiZero_lineConj_eq]
      simp
    have hp'im : ((p'.1 : ℂ)).im = (p.1 : ℂ).im := by
      dsimp only [p']
      rw [xiZero_lineConj_eq]
      simp
    have hp'depth : xiZeroDepth p' = xiZeroDepth p := by
      dsimp only [xiZeroDepth]
      rw [hp're]
      have heq : 1 - (p.1 : ℂ).re - 1 / 2 = -((p.1 : ℂ).re - 1 / 2) := by ring
      rw [heq, abs_neg]
    have hp'height : xiZeroHeight p' = xiZeroHeight p := by
      dsimp only [xiZeroHeight]
      exact hp'im
    have hp' : 1 / 2 < (p'.1 : ℂ).re := by rw [hp're]; linarith
    refine ⟨p', hp', ?_, ?_, ?_⟩
    · simpa only [hp'height] using hpnear
    · simpa only [hp'depth] using hpdepth
    · simpa only [hp'depth, hp'height] using hpterminal

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
