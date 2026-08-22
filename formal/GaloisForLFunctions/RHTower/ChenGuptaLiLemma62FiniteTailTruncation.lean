import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteCritical
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteIntegrability
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeTailTruncation

/-!
# Chen--Gupta--Li Lemma 6.2: finite critical-line tail truncation

The finite reflected integral on CGL's critical line has arbitrary polynomial
decay: the finite Dirichlet prefix is uniformly bounded, while the remaining
Mellin factor is Schwartz.  The source small-time window therefore loses only
the required `X⁻²⁰⁰` complementary-ordinate error.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's full finite reflected critical-line integral differs from a
certified symmetric window by its exact two-sided Mellin power tail. -/
theorem cglLemma62_finiteCritical_integral_sub_truncation_le_power
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ)
    (U : CGLLemma62TailTruncationCertificate) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t M
          (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -U.radius..U.radius,
            cglLemma62FiniteContourIntegrand w N B t M
              (cglLemma62CriticalPoint v).value‖ ≤
        2 * C * (U.radius ^ (1 - (U.decayRate : ℝ)) /
          ((U.decayRate : ℝ) - 1)) := by
  let C : ℝ := cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate *
    (N.value : ℝ) ^ (1 / 2 : ℝ) * (M + 1)
  have hbudget : 0 ≤ cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate := by
    exact le_trans (by positivity) (cglLemma62_mellinTransform_vertical_rapidDecay
      w (1 / 2) U.decayRate 0)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hN : 0 ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg hbudget hN) (by positivity)
  have hintegrable : Integrable (fun v : ℝ => cglLemma62FiniteContourIntegrand w N B t M
      (cglLemma62CriticalPoint v).value) := by
    simpa [cglLemma62CriticalPoint] using
      cglLemma62_finiteContourIntegrand_right_integrable w N B t M
  have hrate : (1 : ℝ) < U.decayRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) U.decayRate_two)
  have hradius : 0 < U.radius := lt_of_lt_of_le zero_lt_one U.radius_one
  have hbound : ∀ v : ℝ, U.radius ≤ |v| →
      ‖cglLemma62FiniteContourIntegrand w N B t M (cglLemma62CriticalPoint v).value‖ ≤
        C * |v| ^ (-(U.decayRate : ℝ)) := by
    intro v hv
    have habspos : 0 < |v| := lt_of_lt_of_le zero_lt_one (U.radius_one.trans hv)
    have hMellin : |v| ^ U.decayRate *
        ‖cglLemma62MellinTransform w (cglLemma62CriticalPoint v).value‖ ≤
          cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate := by
      simpa [cglLemma62CriticalPoint] using
        cglLemma62_mellinTransform_vertical_rapidDecay w (1 / 2) U.decayRate v
    have hMellin' : ‖cglLemma62MellinTransform w (cglLemma62CriticalPoint v).value‖ ≤
        cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate / |v| ^ U.decayRate := by
      apply (le_div_iff₀ (pow_pos habspos _)).mpr
      simpa [mul_comm] using hMellin
    let z : CGLLemma62NonnegativePoint :=
      { value := 1 - (cglLemma62CriticalPoint v).value + (t : ℂ) * I
        nonnegative := by
          norm_num [cglLemma62CriticalPoint] }
    have hhead := cglLemma62_dirichletHead_norm_le B M z
    have hcritical := cglLemma62_finiteCritical_norm_eq w N B t M v
    have hpoint :
        ‖cglLemma62FiniteContourIntegrand w N B t M (cglLemma62CriticalPoint v).value‖ ≤
          C / |v| ^ U.decayRate := by
      rw [hcritical]
      calc
        ‖cglLemma62MellinTransform w (cglLemma62CriticalPoint v).value‖ *
            (N.value : ℝ) ^ (1 / 2 : ℝ) *
            ‖cglLemma62DirichletHead B.character⁻¹ M z.value‖ ≤
          (cglLemma62MellinLineDecayBudget w (1 / 2) U.decayRate /
            |v| ^ U.decayRate) * (N.value : ℝ) ^ (1 / 2 : ℝ) * (M + 1) := by
              gcongr
        _ = C / |v| ^ U.decayRate := by
          dsimp [C]
          field_simp [ne_of_gt habspos]
    calc
      _ ≤ C / |v| ^ U.decayRate := hpoint
      _ = C * |v| ^ (-(U.decayRate : ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg v), Real.rpow_natCast]
        ring
  exact ⟨C, hC, RHTower.Sieve.norm_integral_sub_interval_le_powerTail
    hintegrable hC hrate hradius hbound⟩

/-- CGL's literal small-time finite critical-line window loses a closed
`X⁻²⁰⁰` complementary-ordinate error. -/
theorem cglLemma62_smallTime_finiteCritical_truncation_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t M
          (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62FiniteContourIntegrand w N B t M
              (cglLemma62CriticalPoint v).value‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := cglLemma62_finiteCritical_integral_sub_truncation_le_power
    w N B t M S.tailTruncation
  have hrate : (1 : ℝ) < S.tailTruncationRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2)
      (cglLemma62_smallTime_tailTruncationRate_two S))
  have hden : 0 < (S.tailTruncationRate : ℝ) - 1 := by linarith
  have hscalar : 0 ≤ 2 * C / ((S.tailTruncationRate : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by norm_num) hC) hden.le
  have hpower := cglLemma62_smallTime_tailTruncation_power_le S
  refine ⟨2 * C / ((S.tailTruncationRate : ℝ) - 1), hscalar, ?_⟩
  calc
    _ ≤ 2 * C * (S.truncationRadius ^
        (1 - (S.tailTruncationRate : ℝ)) /
          ((S.tailTruncationRate : ℝ) - 1)) := htail
    _ = (2 * C / ((S.tailTruncationRate : ℝ) - 1)) *
        S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) := by ring
    _ ≤ (2 * C / ((S.tailTruncationRate : ℝ) - 1)) *
        S.base ^ (-200 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hscalar
    _ = _ := by ring

end

end RHTower
