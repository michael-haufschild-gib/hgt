import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeHeightArithmetic

/-!
# Chen--Gupta--Li Lemma 6.2: large-time source-scale collapse

The residual ambient-conductor and local-height powers in the shifted `I₂`
bound are dominated by the global source scale `X=qT`.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The certified local source height is at least one. -/
theorem cglLemma62_largeTime_time_one_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : 1 ≤ S.time := by
  have hbasePow : 1 ≤ S.base ^ S.epsilon :=
    Real.one_le_rpow S.base_one S.epsilon_pos.le
  exact hbasePow.trans S.source_height_lower

/-- The literal local product `qT₀` is bounded by CGL's global source scale. -/
theorem cglLemma62_largeTime_ambient_mul_time_le_base
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    (B.ambient.value : ℝ) * S.time ≤ S.base := by
  have hambientNonneg : 0 ≤ (B.ambient.value : ℝ) := by positivity
  calc
    (B.ambient.value : ℝ) * S.time ≤
        (B.ambient.value : ℝ) * S.globalHeight :=
      mul_le_mul_of_nonneg_left S.time_le_globalHeight hambientNonneg
    _ = S.base := S.base_eq_modulus_mul_globalHeight.symm

/-- The residual `q²T₀^(3/2)` factor after the CGL cutoff and window bounds
is at most `X²`. -/
theorem cglLemma62_largeTime_ambientSq_timeThreeHalves_le_baseSq
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    (B.ambient.value : ℝ) ^ (2 : ℝ) * S.time ^ (3 / 2 : ℝ) ≤
      S.base ^ (2 : ℝ) := by
  have htimeOne := cglLemma62_largeTime_time_one_le S
  have htimePower : S.time ^ (3 / 2 : ℝ) ≤ S.time ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le htimeOne
    norm_num
  have hambientPowerNonneg : 0 ≤ (B.ambient.value : ℝ) ^ (2 : ℝ) := by
    positivity
  have hproduct := cglLemma62_largeTime_ambient_mul_time_le_base S
  calc
    (B.ambient.value : ℝ) ^ (2 : ℝ) * S.time ^ (3 / 2 : ℝ) ≤
        (B.ambient.value : ℝ) ^ (2 : ℝ) * S.time ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_left htimePower hambientPowerNonneg
    _ = ((B.ambient.value : ℝ) * S.time) ^ (2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) S.time_pos.le]
    _ ≤ S.base ^ (2 : ℝ) := by
      apply Real.rpow_le_rpow
      · exact mul_nonneg (by positivity) S.time_pos.le
      · exact hproduct
      · norm_num

end

end RHTower
