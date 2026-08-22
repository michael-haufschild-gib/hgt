import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteTailTruncation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailShift
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedSplit

/-!
# Chen--Gupta--Li Lemma 6.2: reflected-side reassembly

CGL's reflected `L`-function splits into its finite dual polynomial and
complementary tail.  The two continued pieces are moved to their respective
critical and far-left lines, then the already closed small-time truncation
errors are combined into a single source-window error.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The literal reflected CGL integral is exactly its finite reflected
prefix plus its far-left complementary integral. -/
theorem cglLemma62_reflected_integral_eq_finite_add_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    (∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v) =
      (∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M.value v) +
        ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v := by
  have hfinite : Integrable (fun v : ℝ =>
      cglLemma62ReflectedFiniteIntegrand w N B t M.value v) := by
    refine (cglLemma62_finiteContourIntegrand_left_integrable w N B t M.value).congr ?_
    filter_upwards with v
    simpa using cglLemma62_finiteContourIntegrand_eq_line w N B t v M.value
  have htail : Integrable (fun v : ℝ =>
      cglLemma62ReflectedTailIntegrand w N B t M.value v) := by
    refine (cglLemma62_tailContour_right_integrable w N B t M d).congr ?_
    filter_upwards with v
    simpa using cglLemma62_tailContourIntegrand_eq_line w N B t v M.value
  have htailEq :
      (∫ v : ℝ, cglLemma62ReflectedTailIntegrand w N B t M.value v) =
        ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul] using
      cglLemma62_reflectedTail_verticalIntegral_eq_farTail w N B t M d
  calc
    (∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v) =
        ∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M.value v +
          cglLemma62ReflectedTailIntegrand w N B t M.value v := by
            apply integral_congr_ae
            filter_upwards with v
            exact cglLemma62_reflected_eq_finite_add_tail w N B t M.value v
    _ = (∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M.value v) +
          ∫ v : ℝ, cglLemma62ReflectedTailIntegrand w N B t M.value v :=
      integral_add hfinite htail
    _ = _ := by rw [htailEq]

/-- The literal reflected CGL integral, with its finite part moved to the
critical line, is exactly the critical finite integral plus the far-left
complementary integral. -/
theorem cglLemma62_reflected_integral_eq_finiteCritical_add_farTail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    (∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v) =
      (∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t M.value
          (cglLemma62CriticalPoint v).value) +
        ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v := by
  have hfiniteShift :
      (∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M.value v) =
        ∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t M.value
          (cglLemma62CriticalPoint v).value := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [VerticalIntegral, smul_eq_mul, cglLemma62CriticalPoint] using
      cglLemma62_reflectedFinite_verticalIntegral_eq_right w N B t M.value
  calc
    (∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v) =
        (∫ v : ℝ, cglLemma62ReflectedFiniteIntegrand w N B t M.value v) +
          ∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v :=
      cglLemma62_reflected_integral_eq_finite_add_farTail w N B t M d
    _ = _ := by rw [hfiniteShift]

/-- At CGL's literal small-time window, the complete reflected side differs
from its critical finite and far-left tail windows by a closed `X⁻²⁰⁰` error. -/
theorem cglLemma62_smallTime_reflected_truncation_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62ReflectedLineIntegrand w N B t v) -
          ((∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
                (cglLemma62CriticalPoint v).value) +
            ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨CF, hCF, hfinite⟩ :=
    cglLemma62_smallTime_finiteCritical_truncation_error_X200_bound S w S.tailCutoff.value
  obtain ⟨CT, hCT, htail⟩ :=
    cglLemma62_smallTime_farTail_truncation_error_X200_bound S w
  refine ⟨CF + CT, add_nonneg hCF hCT, ?_⟩
  rw [cglLemma62_reflected_integral_eq_finiteCritical_add_farTail
    w N B t S.tailCutoff S.decayDepth]
  calc
    ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint v).value) +
        (∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ((∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
                (cglLemma62CriticalPoint v).value) +
            ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
              cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ =
      ‖((∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
            (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
              (cglLemma62CriticalPoint v).value) +
        ((∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v)‖ := by
        congr 1
        ring
    _ ≤ ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
            (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
              (cglLemma62CriticalPoint v).value‖ +
        ‖(∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ :=
      norm_add_le _ _
    _ ≤ CF * S.base ^ (-200 : ℝ) + CT * S.base ^ (-200 : ℝ) :=
      add_le_add hfinite htail
    _ = (CF + CT) * S.base ^ (-200 : ℝ) := by ring

end

end RHTower
