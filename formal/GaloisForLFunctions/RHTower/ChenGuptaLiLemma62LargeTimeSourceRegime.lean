import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailTruncatedBounds

/-!
# Chen--Gupta--Li Lemma 6.2: large-time source regime

This stores the literal `qT`, `T₀`, and `ε` scale data for CGL's large-time
branch and derives its exact integer tail cutoff and truncated far-line bound.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's literal large-time scale.  Every source inequality is held in
certified data; exported results take no raw real-inequality premise. -/
structure CGLLemma62LargeTimeSourceRegime
    (B : CGLLemma62InducedCharacter) (N : CGLPositiveLength) (t : ℝ) where
  base : ℝ
  base_one : 1 ≤ base
  globalHeight : ℝ
  globalHeight_pos : 0 < globalHeight
  base_eq_modulus_mul_globalHeight : base = (B.ambient.value : ℝ) * globalHeight
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  time : ℝ
  time_pos : 0 < time
  time_le_globalHeight : time ≤ globalHeight
  ordinate_le_two_time : |t| ≤ 2 * time
  source_height_lower : base ^ epsilon ≤ time
  truncation_separated : 2 + base ^ (epsilon / 2) ≤ |t|
  cutoff_scale_two : 2 ≤ base ^ (2 * epsilon) * (B.ambient.value : ℝ) * time / N.value

/-- The literal large-time cutoff scale `X^{2ε}qT₀/N`. -/
def CGLLemma62LargeTimeSourceRegime.cutoffScale
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : ℝ :=
  S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) * S.time / N.value

theorem cglLemma62_largeTime_cutoffScale_pos
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : 0 < S.cutoffScale := by
  unfold CGLLemma62LargeTimeSourceRegime.cutoffScale
  have hbase : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hq : 0 < (B.ambient.value : ℝ) := by exact_mod_cast B.ambient.positive
  have hN : 0 < (N.value : ℝ) := by exact_mod_cast N.positive
  have hpow : 0 < S.base ^ (2 * S.epsilon) := Real.rpow_pos_of_pos hbase _
  exact div_pos (mul_pos (mul_pos hpow hq) S.time_pos) hN

/-- The source local height `T₀` is bounded by its global scale `qT`. -/
theorem cglLemma62_largeTime_time_le_base
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : S.time ≤ S.base := by
  have hq : (1 : ℝ) ≤ B.ambient.value := by exact_mod_cast B.ambient.positive
  have hglobal : 0 ≤ S.globalHeight := S.globalHeight_pos.le
  calc
    S.time ≤ S.globalHeight := S.time_le_globalHeight
    _ = 1 * S.globalHeight := by ring
    _ ≤ (B.ambient.value : ℝ) * S.globalHeight := by
      exact mul_le_mul_of_nonneg_right hq hglobal
    _ = S.base := S.base_eq_modulus_mul_globalHeight.symm

/-- The CGL truncation radius is below its certified large local height. -/
theorem cglLemma62_largeTime_truncationRadius_le_time
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    S.base ^ (S.epsilon / 2) ≤ S.time := by
  have hpow : S.base ^ (S.epsilon / 2) ≤ S.base ^ S.epsilon := by
    apply Real.rpow_le_rpow_of_exponent_le S.base_one
    linarith [S.epsilon_pos]
  exact hpow.trans S.source_height_lower

/-- The literal CGL window and dyadic ordinate range give the source height
envelope needed for the far-left Gamma factor. -/
theorem cglLemma62_largeTime_height_envelope
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    1 + |t| + S.base ^ (S.epsilon / 2) ≤ 4 * S.time := by
  have htime_one : 1 ≤ S.time := by
    have hpow_one : 1 ≤ S.base ^ S.epsilon :=
      Real.one_le_rpow S.base_one S.epsilon_pos.le
    exact hpow_one.trans S.source_height_lower
  have hradius := cglLemma62_largeTime_truncationRadius_le_time S
  linarith [S.ordinate_le_two_time]

/-- The exact integer cutoff corresponding to the literal real source cutoff.
Using its floor preserves the source split `m≤M`/`m>M`. -/
noncomputable def CGLLemma62LargeTimeSourceRegime.tailCutoff
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : CGLLemma62TailCutoff where
  value := Nat.floor S.cutoffScale
  one_le := by
    apply (Nat.one_le_floor_iff S.cutoffScale).mpr
    have htwo : 2 ≤ S.cutoffScale := by
      simpa [CGLLemma62LargeTimeSourceRegime.cutoffScale] using S.cutoff_scale_two
    linarith

/-- Rounding the literal cutoff down loses at most a factor two once its
certified source scale is at least two. -/
theorem cglLemma62_largeTime_tailCutoff_half_scale_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) :
    S.cutoffScale / 2 ≤ (S.tailCutoff.value : ℝ) := by
  have hpos := cglLemma62_largeTime_cutoffScale_pos S
  have hlt : S.cutoffScale < (Nat.floor S.cutoffScale : ℝ) + 1 :=
    Nat.lt_floor_add_one S.cutoffScale
  have hle : S.cutoffScale ≤ (Nat.floor S.cutoffScale : ℝ) + 1 := hlt.le
  have htwo : 2 ≤ S.cutoffScale := by
    simpa [CGLLemma62LargeTimeSourceRegime.cutoffScale] using S.cutoff_scale_two
  change S.cutoffScale / 2 ≤ (Nat.floor S.cutoffScale : ℝ)
  nlinarith

/-- The literal `X^{ε/2}` CGL truncation window. -/
noncomputable def CGLLemma62LargeTimeSourceRegime.truncationWindow
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) : CGLLemma62TailTruncationWindow t where
  radius := S.base ^ (S.epsilon / 2)
  radius_nonneg := Real.rpow_nonneg (le_trans zero_le_one S.base_one) _
  separated := S.truncation_separated

/-- CGL's exact large-time far-tail integral, now instantiated at the literal
source cutoff and truncation radius. -/
theorem cglLemma62_largeTime_truncated_tail_bound
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62LargeTimeSourceRegime B N t) (w : CGLRealSmoothBump)
    (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -S.truncationWindow.radius..S.truncationWindow.radius,
        cglLemma62FarTailIntegrand w N B t S.tailCutoff.value d v‖ ≤
        C * (1 + |t| + S.truncationWindow.radius) ^
          (2 * (d.value : ℝ) + 1 / 2) * (2 * S.truncationWindow.radius) := by
  exact cglLemma62_farTail_truncated_integral_bound w N B t S.tailCutoff d S.truncationWindow

end

end RHTower
