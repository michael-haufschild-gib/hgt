import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeNonprincipalReassembly
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeFiniteWindowBound
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeFactorComposition

/-!
# Chen--Gupta--Li Lemma 6.2: large-time nonprincipal source bound

This combines the normalized nonprincipal physical-to-window identity, the
literal finite `I₁` bound, and the conductor-sensitive `I₂` saving.  Its
conclusion retains exactly CGL's dual Dirichlet-head integral plus the closed
`X⁻²⁰⁰` error.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's normalized nonprincipal large-time physical sum is bounded by the
literal finite dual Dirichlet-head integral plus a closed `X⁻²⁰⁰` error. -/
theorem cglLemma62_nonprincipal_largeTime_source_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(2 * Real.pi : ℝ) •
          (cglMellinPhase t N.value *
            cglLemma62SmoothedCharacterSum w N B.ambient B.character t)‖ ≤
        C * ((N.value : ℝ) ^ (1 / 2 : ℝ) *
          (∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
              (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖) +
          S.base ^ (-200 : ℝ)) := by
  obtain ⟨C0, hC0, hwindow⟩ :=
    cglLemma62_nonprincipal_largeTime_window_error_X200_bound S w
  obtain ⟨C1, hC1, hfinite⟩ :=
    cglLemma62_largeTime_finiteCritical_window_bound S w
  obtain ⟨C2, hC2, htail⟩ :=
    cglLemma62_largeTime_truncated_conductor_tail_X200_bound S w
  let P : ℂ := (2 * Real.pi : ℝ) •
    (cglMellinPhase t N.value * cglLemma62SmoothedCharacterSum w N B.ambient B.character t)
  let F : ℂ := ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
    cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value (cglLemma62CriticalPoint v).value
  let T : ℂ := ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
    cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v
  let H : ℝ := ∫ u : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
    ‖cglLemma62DirichletHead B.character⁻¹ S.tailCutoff.value
      (1 - (cglLemma62CriticalPoint u).value + (t : ℂ) * I)‖
  let A : ℝ := (N.value : ℝ) ^ (1 / 2 : ℝ) * H
  let E : ℝ := S.base ^ (-200 : ℝ)
  have hP : ‖P - (F + T)‖ ≤ C0 * E := by
    simpa [P, F, T, E] using hwindow
  have hF : ‖F‖ ≤ C1 * A := by
    simpa [F, H, A, mul_assoc] using hfinite
  have hT : ‖T‖ ≤ C2 * E := by
    simpa [T, E] using htail
  have hH : 0 ≤ H := by
    dsimp [H]
    apply intervalIntegral.integral_nonneg
    · linarith [S.truncationWindow.radius_nonneg]
    · intro u hu
      exact norm_nonneg _
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) hH
  have hE : 0 ≤ E := by
    dsimp [E]
    exact Real.rpow_nonneg (le_trans zero_le_one S.base_one) _
  have hextra : 0 ≤ C0 * A + C1 * E + C2 * A := by positivity
  refine ⟨C0 + C1 + C2, by positivity, ?_⟩
  have hbound : ‖P‖ ≤ (C0 + C1 + C2) * (A + E) := by
    calc
      ‖P‖ = ‖(P - (F + T)) + F + T‖ := by
        congr 1
        ring
      _ ≤ ‖(P - (F + T)) + F‖ + ‖T‖ := norm_add_le _ _
      _ ≤ (‖P - (F + T)‖ + ‖F‖) + ‖T‖ := by
        have h := norm_add_le (P - (F + T)) F
        linarith
      _ = ‖P - (F + T)‖ + ‖F‖ + ‖T‖ := by ring
      _ ≤ C0 * E + C1 * A + C2 * E := by gcongr
      _ ≤ (C0 * E + C1 * A + C2 * E) + (C0 * A + C1 * E + C2 * A) :=
        le_add_of_nonneg_right hextra
      _ = (C0 + C1 + C2) * (A + E) := by ring
  simpa [P, H, A, E, mul_assoc, add_assoc] using hbound

end

end RHTower
