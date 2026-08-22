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
      exact add_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg
          (lt_of_lt_of_le zero_lt_one S.base_one).le _))
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
            (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))))) *
        ((1 + 2 * S.base ^ S.epsilon) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationRadius)) :=
      mul_le_mul_of_nonneg_right hfront hwindow
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hheight hfront'

 /-- The small-time source envelope collapses to CGL's exact global-scale
 power after the retained length, conductor, and window factors are
 re-associated. -/
 theorem cglLemma62_smallTime_sourceEnvelope_le_globalPower
     {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
     (S : CGLLemma62SmallTimeSourceRegime B N t)
     (d : CGLLemma62TailContourDepth) :
     (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
         (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
         ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
           (2 * (d.value : ℝ) + 2) *
         (2 ^ (2 * (d.value : ℝ)) * S.cutoffScale ^
           (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
         ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
           S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
             S.epsilon / 2)) ≤
       (2 ^ (2 * (d.value : ℝ)) *
         (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) /
           (2 * (d.value : ℝ))) *
         S.base ^ (2 + S.epsilon - 2 * S.epsilon * (d.value : ℝ)) := by
   have hcancel := cglLemma62_smallTime_length_cutoffScale_negativePower_eq S d
   have hcond := cglLemma62_primitiveConductor_eulerQuotient_le_ambient_power B d
   have hpower := cglLemma62_smallTime_sourcePower_reassociation S d
   have hscale := cglLemma62_smallTime_ambientSq_le_baseSq S
   have hbase : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
   have hden : 0 < 2 * (d.value : ℝ) := by
     have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
     positivity
   have hscalar : 0 ≤ 2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ)) :=
     div_nonneg (by positivity) hden.le
   have hcore : 0 ≤ (S.base ^ (2 * S.epsilon) *
       (B.ambient.value : ℝ)) ^ (-2 * (d.value : ℝ)) := by
     apply Real.rpow_nonneg
     exact mul_nonneg (Real.rpow_nonneg hbase.le _) (by positivity)
   have hthree : 0 ≤ (3 : ℝ) ^ (2 * (d.value : ℝ) + 1 / 2) * 2 := by
     exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num)
   have hbasePower : 0 ≤ S.base ^ (S.epsilon *
       (2 * (d.value : ℝ) + 1 / 2) + S.epsilon / 2) :=
     Real.rpow_nonneg hbase.le _
   have houter : 0 ≤ (2 ^ (2 * (d.value : ℝ)) /
       (2 * (d.value : ℝ))) *
       (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
         (-2 * (d.value : ℝ)) *
       ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
         S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
           S.epsilon / 2)) := by
     exact mul_nonneg (mul_nonneg hscalar hcore) (mul_nonneg hthree hbasePower)
   calc
     _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
         ((N.value : ℝ) ^ (-2 * (d.value : ℝ)) * S.cutoffScale ^
           (-2 * (d.value : ℝ))) *
         ((B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
           ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
             (2 * (d.value : ℝ) + 2)) *
         ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
           S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
             S.epsilon / 2)) := by ring
     _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
         (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
           (-2 * (d.value : ℝ)) *
         ((B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
           ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
             (2 * (d.value : ℝ) + 2)) *
         ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
           S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
             S.epsilon / 2)) := by rw [hcancel]
     _ ≤ (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
         (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
           (-2 * (d.value : ℝ)) * (B.ambient.value : ℝ) ^
           (2 * (d.value : ℝ) + 2) *
         ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
           S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
             S.epsilon / 2)) := by
       calc
         _ = ((2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
             (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
               (-2 * (d.value : ℝ)) *
             ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
               S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
                 S.epsilon / 2))) *
             ((B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
               ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
                 (2 * (d.value : ℝ) + 2)) := by ring
         _ ≤ ((2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
             (S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
               (-2 * (d.value : ℝ)) *
             ((3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
               S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
                 S.epsilon / 2))) *
             (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) :=
           mul_le_mul_of_nonneg_left hcond houter
         _ = _ := by ring
     _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
         (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
         (S.base ^ (S.epsilon - 2 * S.epsilon * (d.value : ℝ)) *
           (B.ambient.value : ℝ) ^ (2 : ℝ)) := by
       calc
         _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
             ((S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ)) ^
               (-2 * (d.value : ℝ)) * (B.ambient.value : ℝ) ^
                 (2 * (d.value : ℝ) + 2) *
               S.base ^ (S.epsilon * (2 * (d.value : ℝ) + 1 / 2) +
                 S.epsilon / 2)) *
             (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) := by ring
         _ = (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
             (S.base ^ (S.epsilon - 2 * S.epsilon * (d.value : ℝ)) *
               (B.ambient.value : ℝ) ^ (2 : ℝ)) *
             (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) := by rw [hpower]
         _ = _ := by ring
     _ ≤ (2 ^ (2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
         (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) *
         (S.base ^ (S.epsilon - 2 * S.epsilon * (d.value : ℝ)) *
           S.base ^ (2 : ℝ)) := by
       exact mul_le_mul_of_nonneg_left
         (mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hbase.le _))
         (mul_nonneg hscalar hthree)
     _ = _ := by
       calc
         _ = (2 ^ (2 * (d.value : ℝ)) *
             (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) /
               (2 * (d.value : ℝ))) *
             (S.base ^ (S.epsilon - 2 * S.epsilon * (d.value : ℝ)) *
               S.base ^ (2 : ℝ)) := by ring
         _ = (2 ^ (2 * (d.value : ℝ)) *
             (3 ^ (2 * (d.value : ℝ) + 1 / 2) * 2) /
               (2 * (d.value : ℝ))) *
             S.base ^ ((S.epsilon - 2 * S.epsilon * (d.value : ℝ)) + 2) := by
           rw [← Real.rpow_add hbase]
         _ = _ := by ring

 end

/-- CGL Lemma 6.2's small-time truncated `I₂` bound at the certified contour
depth. All source factors are retained through the proof and then collapsed
to the stated `X⁻²⁰⁰` saving. -/
theorem cglLemma62_smallTime_truncated_conductor_tail_X200_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) (w : CGLRealSmoothBump) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ ≤
        C * S.base ^ (-200 : ℝ) := by
  obtain ⟨C, hC, htail⟩ :=
    cglLemma62_smallTime_truncated_conductor_factorized_tail_bound S w S.decayDepth
  have hfactor :=
    cglLemma62_smallTime_factorizedTailScale_le_sourceEnvelope S S.decayDepth
  have hglobal :=
    cglLemma62_smallTime_sourceEnvelope_le_globalPower S S.decayDepth
  have hscale : cglLemma62SmallTimeFactorizedTailScale S S.decayDepth ≤
      (2 ^ (2 * (S.decayDepth.value : ℝ)) *
        (3 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
          (2 * (S.decayDepth.value : ℝ))) *
        S.base ^ (2 + S.epsilon - 2 * S.epsilon *
          (S.decayDepth.value : ℝ)) :=
    le_trans hfactor hglobal
  have htail' : ‖∫ v : ℝ in -S.truncationRadius..S.truncationRadius,
      cglLemma62FarTailIntegrand w N B t S.tailCutoff.value S.decayDepth v‖ ≤
      C * cglLemma62SmallTimeFactorizedTailScale S S.decayDepth := by
    unfold cglLemma62SmallTimeFactorizedTailScale
    convert htail using 1
    all_goals ring
  have hdepth := cglLemma62_smallTime_decayDepth_source_exponent_le S
  have hpower : S.base ^ (2 + S.epsilon - 2 * S.epsilon *
      (S.decayDepth.value : ℝ)) ≤ S.base ^ (-200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le S.base_one hdepth
  have hscalar : 0 ≤ (2 ^ (2 * (S.decayDepth.value : ℝ)) *
      (3 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
        (2 * (S.decayDepth.value : ℝ))) := by
    have hden : 0 ≤ 2 * (S.decayDepth.value : ℝ) := by
      have hd : 0 < (S.decayDepth.value : ℝ) := by
        exact_mod_cast S.decayDepth.positive
      positivity
    exact div_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num))) hden
  have hCscalar : 0 ≤ C * (2 ^ (2 * (S.decayDepth.value : ℝ)) *
      (3 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
        (2 * (S.decayDepth.value : ℝ))) := mul_nonneg hC hscalar
  refine ⟨C * (2 ^ (2 * (S.decayDepth.value : ℝ)) *
      (3 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
        (2 * (S.decayDepth.value : ℝ))), hCscalar, ?_⟩
  calc
    _ ≤ C * cglLemma62SmallTimeFactorizedTailScale S S.decayDepth := htail'
    _ ≤ C * ((2 ^ (2 * (S.decayDepth.value : ℝ)) *
        (3 ^ (2 * (S.decayDepth.value : ℝ) + 1 / 2) * 2) /
          (2 * (S.decayDepth.value : ℝ))) *
        S.base ^ (2 + S.epsilon - 2 * S.epsilon *
          (S.decayDepth.value : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale hC
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hCscalar

end RHTower
