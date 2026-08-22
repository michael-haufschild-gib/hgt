import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeSourceRegime
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailAllConductorBounds

/-!
# Chen--Gupta--Li Lemma 6.2: small-time conductor-sensitive `I₂` regime

This integrates the all-ordinate five-factor far-left estimate on CGL's
literal small-time window, retaining every source-critical scale.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62_smallTime_interval_abs_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t v : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (hv : v ∈ Set.uIoc (-S.truncationRadius) S.truncationRadius) :
    |v| ≤ S.truncationRadius := by
  have hradius : 0 ≤ S.truncationRadius := by
    unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
    exact Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one S.base_one).le _
  rw [Set.uIoc_of_le (by linarith)] at hv
  exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩

/-- CGL's small-time `I₂` integral, with the length, primitive conductor,
imprimitive Euler quotient, and literal floor-cutoff factors all retained. -/
theorem cglLemma62_smallTime_truncated_conductor_factorized_tail_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump)
    (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
        C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          cglLemma62TailEulerConductorBudget B d *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))) *
          (1 + 2 * S.base ^ S.epsilon) ^
            (2 * (d.value : ℝ) + 1 / 2) *
          (2 * S.truncationRadius) := by
  obtain ⟨C, hC, hpoint⟩ :=
    cglLemma62_farTail_all_conductor_factorized_point_bound
      w N B t S.tailCutoff d
  have hlength : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have hprimitive : 0 ≤ (B.primitive.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) := by positivity
  have heuler : 0 ≤ cglLemma62TailEulerConductorBudget B d := by
    let z : CGLLemma62TailEulerPoint d := ⟨(-2 * (d.value : ℝ) : ℂ), by simp⟩
    exact le_trans (norm_nonneg _)
      (cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d z)
  have hden : 0 ≤ 2 * (d.value : ℝ) := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have htail : 0 ≤ (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ)) := by
    exact div_nonneg (by positivity) hden
  have hfront : 0 ≤ C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
      (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
      cglLemma62TailEulerConductorBudget B d *
      ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
        (2 * (d.value : ℝ))) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hlength) hprimitive) heuler) htail
  have hpower_nonneg : 0 ≤ 2 * (d.value : ℝ) + 1 / 2 := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have hpoint' : ∀ v ∈ Set.uIoc (-S.truncationRadius) S.truncationRadius,
      ‖cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
        C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          cglLemma62TailEulerConductorBudget B d *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))) *
          (1 + 2 * S.base ^ S.epsilon) ^
            (2 * (d.value : ℝ) + 1 / 2) := by
    intro v hv
    have hvabs := cglLemma62_smallTime_interval_abs_le S hv
    let p : CGLLemma62SmallTimeWindowPoint S := {
      value := v
      abs_le_radius := hvabs }
    have hord := cglLemma62_smallTime_window_shiftedOrdinate_le S p
    have hheight : 1 + |v - t| ≤ 1 + 2 * S.base ^ S.epsilon := by
      simpa [p] using add_le_add_left hord 1
    have hpow : (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) ≤
        (1 + 2 * S.base ^ S.epsilon) ^ (2 * (d.value : ℝ) + 1 / 2) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact hheight
      · exact hpower_nonneg
    have hsource := hpoint v
    calc
      ‖cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
          C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
            (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
            cglLemma62TailEulerConductorBudget B d *
            ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
              (2 * (d.value : ℝ))) *
            (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
              simpa using hsource
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hfront
  refine ⟨C, hC, ?_⟩
  calc
    ‖∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
        (C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          cglLemma62TailEulerConductorBudget B d *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))) *
          (1 + 2 * S.base ^ S.epsilon) ^
            (2 * (d.value : ℝ) + 1 / 2)) *
          |S.truncationRadius - (-S.truncationRadius)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint'
    _ = C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        cglLemma62TailEulerConductorBudget B d *
        ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
          (2 * (d.value : ℝ))) *
        (1 + 2 * S.base ^ S.epsilon) ^
          (2 * (d.value : ℝ) + 1 / 2) *
        (2 * S.truncationRadius) := by
      have hradius : 0 ≤ S.truncationRadius := by
        unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
        exact Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one S.base_one).le _
      rw [show S.truncationRadius - (-S.truncationRadius) =
          2 * S.truncationRadius by ring,
        abs_of_nonneg (mul_nonneg (by norm_num) hradius)]

end

end RHTower
