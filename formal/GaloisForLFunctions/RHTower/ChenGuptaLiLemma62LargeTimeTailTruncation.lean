import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FiniteTailTruncation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeDepth

/-!
# Chen--Gupta--Li Lemma 6.2: large-time ordinate truncation

At the literal CGL large-time source radius `X^(ε/2)`, this module selects a
closed rapid-decay rate and proves that both reflected pieces lose at most
`O(X⁻²⁰⁰)` outside the source window.  The finite critical contribution and
the far-left complementary contribution use the same certified radius and
rate, so their later reassembly has no external truncation premise.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A closed Mellin-decay rate which makes CGL's large-time ordinate tails
save `X⁻²⁰⁰` at the literal radius `X^(ε/2)`. -/
noncomputable def CGLLemma62LargeTimeSourceRegime.tailTruncationRate
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : ℕ :=
  Nat.ceil (2 + 400 / S.epsilon)

/-- The internally selected large-time tail rate is at least two. -/
theorem cglLemma62_largeTime_tailTruncationRate_two
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    2 ≤ S.tailTruncationRate := by
  have hceil : 2 + 400 / S.epsilon ≤ (S.tailTruncationRate : ℝ) := Nat.le_ceil _
  have hnonneg : 0 ≤ 400 / S.epsilon := div_nonneg (by norm_num) S.epsilon_pos.le
  have hrate : (2 : ℝ) ≤ (S.tailTruncationRate : ℝ) := by linarith
  exact_mod_cast hrate

/-- The product of CGL's large-time radius exponent and the selected
tail-decay exponent is at most `-200`. -/
theorem cglLemma62_largeTime_tailTruncation_exponent_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    (S.epsilon / 2) * (1 - (S.tailTruncationRate : ℝ)) ≤ -200 := by
  have hceil : 2 + 400 / S.epsilon ≤ (S.tailTruncationRate : ℝ) := Nat.le_ceil _
  have heps : 0 < S.epsilon := S.epsilon_pos
  have hmul := mul_le_mul_of_nonneg_left hceil heps.le
  have hdiv : S.epsilon * (400 / S.epsilon) = 400 := by field_simp
  rw [mul_add, hdiv] at hmul
  nlinarith

/-- The literal CGL large-time radius raised to the omitted-tail power is at
most the required `X⁻²⁰⁰` saving. -/
theorem cglLemma62_largeTime_tailTruncation_power_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    S.truncationWindow.radius ^ (1 - (S.tailTruncationRate : ℝ)) ≤
      S.base ^ (-200 : ℝ) := by
  have hbase : 0 ≤ S.base := le_trans zero_le_one S.base_one
  have hexp := cglLemma62_largeTime_tailTruncation_exponent_le S
  unfold CGLLemma62LargeTimeSourceRegime.truncationWindow
  rw [← Real.rpow_mul hbase]
  exact Real.rpow_le_rpow_of_exponent_le S.base_one hexp

/-- CGL's literal large-time radius with a closed rate sufficient for the
source `X⁻²⁰⁰` tail saving. -/
noncomputable def CGLLemma62LargeTimeSourceRegime.tailTruncation
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : CGLLemma62TailTruncationCertificate where
  radius := S.truncationWindow.radius
  radius_one := by
    unfold CGLLemma62LargeTimeSourceRegime.truncationWindow
    apply Real.one_le_rpow S.base_one
    linarith [S.epsilon_pos]
  decayRate := S.tailTruncationRate
  decayRate_two := cglLemma62_largeTime_tailTruncationRate_two S

/-- CGL's full large-time far-left complementary integral differs from its
literal source window by a closed `O(X⁻²⁰⁰)` error. -/
theorem cglLemma62_largeTime_farTail_truncation_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v) -
          ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := cglLemma62_farTail_integral_sub_truncation_le_power
    w N B t S.tailCutoff S.decayDepth S.tailTruncation
  have hrate : (1 : ℝ) < S.tailTruncationRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2)
      (cglLemma62_largeTime_tailTruncationRate_two S))
  have hden : 0 < (S.tailTruncationRate : ℝ) - 1 := by linarith
  have hscalar : 0 ≤ 2 * C / ((S.tailTruncationRate : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by norm_num) hC) hden.le
  have hpower := cglLemma62_largeTime_tailTruncation_power_le S
  refine ⟨2 * C / ((S.tailTruncationRate : ℝ) - 1), hscalar, ?_⟩
  calc
    _ ≤ 2 * C * (S.truncationWindow.radius ^
        (1 - (S.tailTruncationRate : ℝ)) / ((S.tailTruncationRate : ℝ) - 1)) := htail
    _ = (2 * C / ((S.tailTruncationRate : ℝ) - 1)) *
        S.truncationWindow.radius ^ (1 - (S.tailTruncationRate : ℝ)) := by ring
    _ ≤ (2 * C / ((S.tailTruncationRate : ℝ) - 1)) * S.base ^ (-200 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hscalar
    _ = _ := by ring

/-- CGL's full large-time finite critical integral differs from its literal
source window by a closed `O(X⁻²⁰⁰)` error. -/
theorem cglLemma62_largeTime_finiteCritical_truncation_error_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
          (cglLemma62CriticalPoint v).value) -
          ∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
            cglLemma62FiniteContourIntegrand w N B t S.tailCutoff.value
              (cglLemma62CriticalPoint v).value‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := cglLemma62_finiteCritical_integral_sub_truncation_le_power
    w N B t S.tailCutoff.value S.tailTruncation
  have hrate : (1 : ℝ) < S.tailTruncationRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2)
      (cglLemma62_largeTime_tailTruncationRate_two S))
  have hden : 0 < (S.tailTruncationRate : ℝ) - 1 := by linarith
  have hscalar : 0 ≤ 2 * C / ((S.tailTruncationRate : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by norm_num) hC) hden.le
  have hpower := cglLemma62_largeTime_tailTruncation_power_le S
  refine ⟨2 * C / ((S.tailTruncationRate : ℝ) - 1), hscalar, ?_⟩
  calc
    _ ≤ 2 * C * (S.truncationWindow.radius ^
        (1 - (S.tailTruncationRate : ℝ)) / ((S.tailTruncationRate : ℝ) - 1)) := htail
    _ = (2 * C / ((S.tailTruncationRate : ℝ) - 1)) *
        S.truncationWindow.radius ^ (1 - (S.tailTruncationRate : ℝ)) := by ring
    _ ≤ (2 * C / ((S.tailTruncationRate : ℝ) - 1)) * S.base ^ (-200 : ℝ) :=
      mul_le_mul_of_nonneg_left hpower hscalar
    _ = _ := by ring

end

end RHTower
