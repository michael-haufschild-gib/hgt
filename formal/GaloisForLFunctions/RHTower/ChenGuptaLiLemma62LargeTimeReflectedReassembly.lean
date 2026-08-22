import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeTailTruncation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedReassembly

/-!
# Chen--Gupta--Li Lemma 6.2: large-time reflected-side reassembly

The finite critical and far-left complementary CGL pieces have independent
large-time source-window errors.  This module combines them into one closed
error for the complete reflected line at the literal radius `X^(ε/2)`.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- At CGL's literal large-time window, the complete reflected side differs
from its critical finite and far-left tail windows by a closed `X⁻²⁰⁰` error. -/
theorem cglLemma62_largeTime_reflected_truncation_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v) -
          ((∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
              cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
                (cglLemma62CriticalPoint v).value) +
            ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
              cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨CF, hCF, hfinite⟩ :=
    cglLemma62_largeTime_finiteCritical_truncation_error_X200_bound S w
  obtain ⟨CT, hCT, htail⟩ :=
    cglLemma62_largeTime_farTail_truncation_error_X200_bound S w
  refine ⟨CF + CT, add_nonneg hCF hCT, ?_⟩
  rw [cglLemma62_reflected_integral_eq_finiteCritical_add_farTail
    w N B t S.tailCutoff S.decayDepth]
  calc
    ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint v).value) +
        (∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ((∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
              cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
                (cglLemma62CriticalPoint v).value) +
            ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
              cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ =
      ‖((∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
            (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
              (cglLemma62CriticalPoint v).value) +
        ((∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ := by
        congr 1
        ring
    _ ≤ ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
            (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
              (cglLemma62CriticalPoint v).value‖ +
        ‖(∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ :=
      norm_add_le _ _
    _ ≤ CF * S.base ^ (-200 : ℝ) + CT * S.base ^ (-200 : ℝ) :=
      add_le_add hfinite htail
    _ = (CF + CT) * S.base ^ (-200 : ℝ) := by ring

end

end RHTower
