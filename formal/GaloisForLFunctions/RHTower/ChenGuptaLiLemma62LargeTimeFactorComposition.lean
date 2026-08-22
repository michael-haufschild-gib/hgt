import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeConductorRegime
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeDepth
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeCutoffArithmetic
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeCutoffCancellation
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeConductorArithmetic
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeHeightArithmetic
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimeScaleCollapse
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62LargeTimePowerReassociation

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The literal nonconstant factor in CGL's large-time factorized `I₂`
estimate, retaining the source denominator `2k`. -/
def cglLemma62LargeTimeFactorizedTailScale
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) : ℝ :=
  (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
    (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
    cglLemma62TailEulerConductorBudget B d *
    ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ))) *
    (1 + |t| + S.truncationWindow.radius) ^
      (2 * (d.value : ℝ) + 1 / 2) *
    (2 * S.truncationWindow.radius)

private theorem cglLemma62_largeTime_tailScale_nonneg
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    0 ≤ cglLemma62LargeTimeFactorizedTailScale S d := by
  unfold cglLemma62LargeTimeFactorizedTailScale
  have hden : 0 < 2 * (d.value : ℝ) := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have hcut : 0 ≤ (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have heuler : 0 ≤ cglLemma62TailEulerConductorBudget B d := by
    let z : CGLLemma62TailEulerPoint d := ⟨(-2 * (d.value : ℝ) : ℂ), by simp⟩
    exact le_trans (norm_nonneg _)
      (cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d z)
  have hlength : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have hprimitive : 0 ≤ (B.primitive.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) := by positivity
  have htail : 0 ≤ (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ)) := div_nonneg hcut hden.le
  have hheight : 0 ≤ (1 + |t| + S.truncationWindow.radius) ^
      (2 * (d.value : ℝ) + 1 / 2) := by
    apply Real.rpow_nonneg
    nlinarith [abs_nonneg t, S.truncationWindow.radius_nonneg]
  have hwidth : 0 ≤ 2 * S.truncationWindow.radius :=
    mul_nonneg (by norm_num) S.truncationWindow.radius_nonneg
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg hlength hprimitive) heuler) htail) hheight) hwidth

/-- Before re-association, each literal CGL factor is replaced only by its
proved source envelope. -/
theorem cglLemma62_largeTime_factorizedTailScale_le_sourceEnvelope
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    cglLemma62LargeTimeFactorizedTailScale S d ≤
      (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
        (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
          (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) := by
  have heuler := cglLemma62_tailEulerConductorBudget_le_conductorQuotient_power B d
  have hcut := cglLemma62_largeTime_tailCutoff_negativePower_le S d
  have hden : 0 ≤ 2 * (d.value : ℝ) := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have hcutdiv : (S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
      (2 * (d.value : ℝ)) ≤
      (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
        (-2 * (d.value : ℝ))) / (2 * (d.value : ℝ)) :=
    div_le_div_of_nonneg_right hcut hden
  have hheight := cglLemma62_largeTime_heightWindow_factor_le S d
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
      Real.rpow_nonneg (cglLemma62_largeTime_cutoffScale_pos S).le _
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
  unfold cglLemma62LargeTimeFactorizedTailScale
  calc
    _ = ((N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (cglLemma62TailEulerConductorBudget B d *
          ((S.tailCutoff.value : ℝ) ^ (-2 * (d.value : ℝ)) /
            (2 * (d.value : ℝ))))) *
        ((1 + |t| + S.truncationWindow.radius) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationWindow.radius)) := by ring
    _ ≤ ((N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
          (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
            (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))))) *
        ((1 + |t| + S.truncationWindow.radius) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationWindow.radius)) :=
      mul_le_mul_of_nonneg_right hfront
        (mul_nonneg (Real.rpow_nonneg (by
          nlinarith [abs_nonneg t, S.truncationWindow.radius_nonneg]) _)
          (mul_nonneg (by norm_num) S.truncationWindow.radius_nonneg))
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hheight hfront'

/-- The source envelope collapses to the exact global-scale power after the
retained length, conductor, and height factors are re-associated. -/
theorem cglLemma62_largeTime_sourceEnvelope_le_globalPower
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t)
    (d : CGLLemma62TailContourDepth) :
    (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
        (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
          (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) ≤
      (2 ^ (2 * (d.value : ℝ)) *
        (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) /
          (2 * (d.value : ℝ))) *
        S.base ^ (2 - 4 * S.epsilon * (d.value : ℝ)) := by
  have hcancel := cglLemma62_largeTime_length_cutoffScale_negativePower_eq S d
  have hcond := cglLemma62_primitiveConductor_eulerQuotient_le_ambient_power B d
  have hpower := cglLemma62_largeTime_sourcePower_reassociation S d
  have hscale := cglLemma62_largeTime_ambientSq_timeThreeHalves_le_baseSq S
  have hden : 0 < 2 * (d.value : ℝ) := by
    have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
    positivity
  have hscalar : 0 ≤ 2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ)) :=
    div_nonneg (by positivity) hden.le
  have hcore : 0 ≤ (S.base ^ (2 * S.epsilon) *
      (B.ambient.value : ℝ) * S.time) ^ (-2 * (d.value : ℝ)) := by
    apply Real.rpow_nonneg
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one S.base_one).le _)
        (by positivity))
      S.time_pos.le
  have hheight : 0 ≤ (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) *
      (2 * S.time) := by
    exact mul_nonneg
      (Real.rpow_nonneg (mul_nonneg (by norm_num) S.time_pos.le) _)
      (mul_nonneg (by norm_num) S.time_pos.le)
  have houter : 0 ≤ (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
      (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
        (-2 * (d.value : ℝ)) *
      ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) := by
    exact mul_nonneg (mul_nonneg hscalar hcore) hheight
  have hpre : 0 ≤ (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
      (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
      S.base ^ (-4 * S.epsilon * (d.value : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg hscalar
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num)))
      (Real.rpow_nonneg (lt_of_lt_of_le zero_lt_one S.base_one).le _)
  calc
    _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        ((N.value : ℝ) ^ (-2 * (d.value : ℝ)) * S.cutoffScale ^
          (-2 * (d.value : ℝ))) *
        ((B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
            (2 * (d.value : ℝ) + 2)) *
        ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) := by ring
    _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
          (-2 * (d.value : ℝ)) *
        ((B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
            (2 * (d.value : ℝ) + 2)) *
        ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) := by rw [hcancel]
    _ ≤ (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
          (-2 * (d.value : ℝ)) * (B.ambient.value : ℝ) ^
          (2 * (d.value : ℝ) + 2) *
        ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) := by
      calc
        _ = ((2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
            (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
              (-2 * (d.value : ℝ)) *
            ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time))) *
            ((B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
              ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
                (2 * (d.value : ℝ) + 2)) := by ring
        _ ≤ ((2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
            (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
              (-2 * (d.value : ℝ)) *
            ((4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time))) *
            (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hcond houter
        _ = _ := by ring
    _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
        S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
        ((B.ambient.value : ℝ) ^ (2 : ℝ) * S.time ^ (3 / 2 : ℝ)) := by
      calc
        _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
            ((S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time) ^
              (-2 * (d.value : ℝ)) * (B.ambient.value : ℝ) ^
                (2 * (d.value : ℝ) + 2) *
              (4 * S.time) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * S.time)) := by ring
        _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
            ((4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
              S.base ^ (-4 * S.epsilon * (d.value : ℝ)) *
              (B.ambient.value : ℝ) ^ (2 : ℝ) * S.time ^ (3 / 2 : ℝ)) := by
          rw [hpower]
        _ = _ := by ring
    _ ≤ (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
        (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
        S.base ^ (-4 * S.epsilon * (d.value : ℝ)) * S.base ^ (2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hscale hpre
    _ = _ := by
      calc
        _ = ((2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
            (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2)) *
            (S.base ^ (-4 * S.epsilon * (d.value : ℝ)) * S.base ^ (2 : ℝ)) := by ring
        _ = ((2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
            (4 ^ (2 * (d.value : ℝ) + 1 / 2) * 2)) *
            S.base ^ (-4 * S.epsilon * (d.value : ℝ) + 2) := by
          rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one S.base_one)]
        _ = _ := by
          have hexp : -4 * S.epsilon * (d.value : ℝ) + 2 =
              2 - 4 * S.epsilon * (d.value : ℝ) := by ring
          rw [hexp]
          ring

/-- CGL Lemma 6.2's large-time truncated `I₂` bound at the certified contour
depth.  All source factors are retained through the proof and then collapsed
to the stated `X⁻²⁰⁰` saving. -/
theorem cglLemma62_largeTime_truncated_conductor_tail_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ :=
    cglLemma62_largeTime_truncated_conductor_factorized_tail_bound S w S.decayDepth
  have hfactor :=
    cglLemma62_largeTime_factorizedTailScale_le_sourceEnvelope S S.decayDepth
  have hglobal :=
    cglLemma62_largeTime_sourceEnvelope_le_globalPower S S.decayDepth
  have hscale : cglLemma62LargeTimeFactorizedTailScale S S.decayDepth ≤
      (2 ^ (2 * (S.decayDepth.value : ℝ)) *
        (4 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
          (2 * (S.decayDepth.value : ℝ))) *
        S.base ^ (2 - 4 * S.epsilon * (S.decayDepth.value : ℝ)) :=
    le_trans hfactor hglobal
  have htail' : ‖∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
      cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ ≤
      C * cglLemma62LargeTimeFactorizedTailScale S S.decayDepth := by
    unfold cglLemma62LargeTimeFactorizedTailScale
    convert htail using 1
    all_goals ring
  have hdepth := cglLemma62_largeTime_decayDepth_source_exponent_le S
  have hexponent : 2 - 4 * S.epsilon * (S.decayDepth.value : ℝ) ≤ -200 := by
    linarith [S.epsilon_pos]
  have hpower : S.base ^ (2 - 4 * S.epsilon * (S.decayDepth.value : ℝ)) ≤
      S.base ^ (-200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le S.base_one hexponent
  have hscalar : 0 ≤ (2 ^ (2 * (S.decayDepth.value : ℝ)) *
      (4 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
        (2 * (S.decayDepth.value : ℝ))) := by
    have hden : 0 ≤ 2 * (S.decayDepth.value : ℝ) := by
      have hd : 0 < (S.decayDepth.value : ℝ) := by
        exact_mod_cast S.decayDepth.positive
      positivity
    exact div_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num))) hden
  have hCscalar : 0 ≤ C * (2 ^ (2 * (S.decayDepth.value : ℝ)) *
      (4 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
        (2 * (S.decayDepth.value : ℝ))) := mul_nonneg hC hscalar
  refine ⟨C * (2 ^ (2 * (S.decayDepth.value : ℝ)) *
      (4 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
        (2 * (S.decayDepth.value : ℝ))), hCscalar, ?_⟩
  calc
    _ ≤ C * cglLemma62LargeTimeFactorizedTailScale S S.decayDepth := htail'
    _ ≤ C * ((2 ^ (2 * (S.decayDepth.value : ℝ)) *
        (4 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
          (2 * (S.decayDepth.value : ℝ))) *
        S.base ^ (2 - 4 * S.epsilon * (S.decayDepth.value : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale hC
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hCscalar

end

end RHTower
