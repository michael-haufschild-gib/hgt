import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailRapidTruncation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62SmallTimeDepth

/-!
# Chen--Gupta--Li Lemma 6.2: small-time complementary-ordinate truncation

CGL truncate the reflected far-left integral to `|v| ≤ X^(ε/2)` by rapid
Mellin decay.  This file makes that step source-specific and closed: the
literal radius and an internally selected integer decay rate make the omitted
two-sided tail `O(X⁻²⁰⁰)`.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A closed Mellin-decay rate which makes CGL's small-time complementary
ordinate tail save `X⁻²⁰⁰` at the literal radius `X^(ε/2)`. -/
noncomputable def CGLLemma62SmallTimeSourceRegime.tailTruncationRate
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) : ℕ :=
  Nat.ceil (2 + 400 / S.epsilon)

/-- The internally selected small-time tail rate is at least two. -/
theorem cglLemma62_smallTime_tailTruncationRate_two
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    2 ≤ S.tailTruncationRate := by
  have hceil : 2 + 400 / S.epsilon ≤ (S.tailTruncationRate : ℝ) :=
    Nat.le_ceil _
  have heps : 0 < S.epsilon := S.epsilon_pos
  have hnonneg : 0 ≤ 400 / S.epsilon := div_nonneg (by norm_num) heps.le
  have hrate : (2 : ℝ) ≤ (S.tailTruncationRate : ℝ) := by
    linarith
  exact_mod_cast hrate

/-- The product of the source radius exponent and the selected tail-decay
exponent is at most `-200`. -/
theorem cglLemma62_smallTime_tailTruncation_exponent_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    (S.epsilon / 2) * (1 - (S.tailTruncationRate : ℝ)) ≤ -200 := by
  have hceil : 2 + 400 / S.epsilon ≤ (S.tailTruncationRate : ℝ) :=
    Nat.le_ceil _
  have heps : 0 < S.epsilon := S.epsilon_pos
  have hmul := mul_le_mul_of_nonneg_left hceil heps.le
  have hdiv : S.epsilon * (400 / S.epsilon) = 400 := by
    field_simp
  rw [mul_add, hdiv] at hmul
  nlinarith

/-- The literal small-time radius raised to the omitted-tail power is at most
the required CGL saving. -/
theorem cglLemma62_smallTime_tailTruncation_power_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    S.truncationRadius ^ (1 - (S.tailTruncationRate : ℝ)) ≤
      S.base ^ (-200 : ℝ) := by
  have hbase : 0 ≤ S.base := le_trans zero_le_one S.base_one
  have hexponent := cglLemma62_smallTime_tailTruncation_exponent_le S
  unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
  rw [← Real.rpow_mul hbase]
  exact Real.rpow_le_rpow_of_exponent_le S.base_one hexponent

/-- CGL's literal small-time radius with a closed Mellin-decay rate sufficient
for its complementary-ordinate tail to save `X⁻²⁰⁰`. -/
noncomputable def CGLLemma62SmallTimeSourceRegime.tailTruncation
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    CGLLemma62TailTruncationCertificate where
  radius := S.truncationRadius
  radius_one := by
    unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
    apply Real.one_le_rpow S.base_one
    linarith [S.epsilon_pos]
  decayRate := S.tailTruncationRate
  decayRate_two := cglLemma62_smallTime_tailTruncationRate_two S

/-- The complementary ordinate tails omitted from CGL's small-time `I₂`
window have a closed `X⁻²⁰⁰` bound at the literal source radius. -/
theorem cglLemma62_smallTime_farTail_truncation_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
            cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := cglLemma62_farTail_integral_sub_truncation_le_power
    w N B t S.tailCutoff S.decayDepth S.tailTruncation
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
