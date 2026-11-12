import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimeErrorKeepsItsBoundaryTrace
import GaloisForLFunctions.RHTower.DigammaSeries

/-!+# Continuity of the complete right-substrip trace

Reciprocal zero mass dominates the normalized trace uniformly on the
positive half-line. Thus the infinite trace is continuous even when zero
abscissae accumulate at its bounding line.
-/

noncomputable section

open Complex Set
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- The full normalized trace is continuous, without a gap below its
bounding abscissa. All multiplicity copies remain in the sum. -/
theorem continuousOn_rightNormalizedZeroTrace {σ β : ℝ} (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    ContinuousOn (rightNormalizedZeroTrace σ β) (Ici 1) := by
  apply continuousOn_tsum (u := rightSubstripTailWeight σ ∅)
  · intro q
    by_cases hq : σ ≤ (q.1 : ℂ).re
    · simp only [rightNormalizedZeroTerm, if_pos hq]
      exact ((continuousOn_Ioi_cpow ((q.1 : ℂ) - (β : ℂ))).mono
        (fun _ hx => zero_lt_one.trans_le hx)).div_const _
    · simp only [rightNormalizedZeroTerm, if_neg hq]
      exact continuousOn_const
  · exact summable_rightSubstripTailWeight hσ ∅
  · intro q x hx
    exact norm_rightNormalizedZeroTerm_le hx hβ q

end GaloisForLFunctions.ZeroConfigurationGeometry
