import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeConductorRegime
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeDepth
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeCutoffArithmetic
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeCutoffCancellation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeConductorArithmetic
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeHeightArithmetic
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeScaleCollapse
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimePowerReassociation

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The literal nonconstant factor in CGL's small-time factorized `I₂`
estimate, retaining the source denominator `2k`. -/
def cglLemma62SmallTimeFactorizedTailScale
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) : ℝ :=
  (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
    (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
    cglLemma62TailEulerConductorBudget B d *
    ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ))) *
    (1 + 2 * S.base ^ S.epsilon) ^
      (2 * (d.value : ℝ) + 1 / 2) *
    (2 * S.truncationRadius)

/-- Before re-association, each literal CGL small-time factor is replaced
only by its proved source envelope. -/
theorem cglLemma62_smallTime_factorizedTailScale_le_sourceEnvelope
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    cglLemma62SmallTimeFactorizedTailScale S d ≤
      (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
        (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
          (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
          S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
            S.epsilon / 2)) := by
  have heuler := cglLemma62_tailEulerConductorBudget_le_conductorQuotient_power B d
  have hcut := cglLemma62_smallTime_tailCutoff_negativePower_le S d
  have hden : 0 ≤ 2 * (d.value : ℝ) := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have hcutdiv : (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ)) ≤
      (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
        (-2 * (d.value : ℝ))) / (2 * (d.value : ℝ)) :=
    div_le_div_of_nonneg_right hcut hden
  have hheight := cglLemma62_smallTime_heightWindow_factor_le S d
  have hlength : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have hprimitive : 0 ≤ (B.primitive.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) := by positivity
  have hquotient : 0 ≤ ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
      (2 * (d.value : ℝ) + 2) := by positivity
  have htail : 0 ≤ (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ)) := by
    exact div_nonneg (by positivity) hden
  have htail' : 0 ≤ (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
      (-2 * (d.value : ℝ))) / (2 * (d.value : ℝ)) := by
    have hscale : 0 ≤ S.cutoffScale ^ (-2 * (d.value : ℝ)) :=
      Real.rpow_nonneg (cglLemma62_smallTime_cutoffScale_pos S).le _
    exact div_nonneg (mul_nonneg (by positivity) hscale) hden
  have hEulerTail : cglLemma62TailEulerConductorBudget B d *
      ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
        (2 * (d.value : ℝ))) ≤
      ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
        (2 * (d.value : ℝ) + 2) *
        (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
          (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) := by
    calc
      _ ≤ ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))) :=
        mul_le_mul_of_nonneg_right heuler htail
      _ ≤ _ := mul_le_mul_of_nonneg_left hcutdiv hquotient
  have hfront : (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
      (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
      (cglLemma62TailEulerConductorBudget B d *
        ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
          (2 * (d.value : ℝ)))) ≤
      (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
          (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
            (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ)))) := by
    exact mul_le_mul_of_nonneg_left hEulerTail (mul_nonneg hlength hprimitive)
  have hfront' : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
      (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
      (((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
        (2 * (d.value : ℝ) + 2) *
        (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
          (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ)))) := by
    exact mul_nonneg (mul_nonneg hlength hprimitive)
      (mul_nonneg hquotient htail')
  have hwindow : 0 ≤ (1 + 2 * S.base ^ S.epsilon) ^
      (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationRadius) := by
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg
        (lt_of_lt_of_le zero_lt_one S.base_one).le _)
  unfold cglLemma62SmallTimeFactorizedTailScale
  calc
    _ = ((N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (cglLemma62TailEulerConductorBudget B d *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))))) *
        ((1 + 2 * S.base ^ S.epsilon) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationRadius)) := by ring
    _ ≤ ((N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
          (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
            (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ)))) *
        ((1 + 2 * S.base ^ S.epsilon) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationRadius)) :=
      mul_le_mul_of_nonneg_right hfront hwindow
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hheight hfront'

end

end RHTower
