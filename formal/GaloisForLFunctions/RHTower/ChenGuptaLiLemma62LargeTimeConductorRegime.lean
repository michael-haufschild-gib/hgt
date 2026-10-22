import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeSourceRegime
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailTruncatedConductorBounds

/-!
# Chen--Gupta--Li Lemma 6.2: large-time conductor-sensitive `I₂` regime

This instantiates CGL's literal large-time cutoff and window with the exact
`q / q*` Euler cancellation on the shifted far-left contour.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's exact large-time far-tail `I₂` integral with the primitive-conductor
cancellation retained through the literal floor cutoff and source window. -/
theorem cglLemma62_largeTime_truncated_conductor_tail_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump)
    (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
        C * (1 + |t| + S.truncationWindow.radius) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationWindow.radius) :=
  cglLemma62_largeTime_truncated_tail_bound S w d

/-- CGL's literal large-time `I₂` integral with every source-sensitive scale
still displayed, ready for the final depth and exponent calculation. -/
theorem cglLemma62_largeTime_truncated_conductor_factorized_tail_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump)
    (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
        C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          cglLemma62TailEulerConductorBudget B d *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))) *
          (1 + |t| + S.truncationWindow.radius) ^
            (2 * (d.value : ℝ) + 1 / 2) *
          (2 * S.truncationWindow.radius) := by
  exact cglLemma62_farTail_truncated_conductor_factorized_integral_bound
    w N B t S.tailCutoff d S.truncationWindow

end

end RHTower
