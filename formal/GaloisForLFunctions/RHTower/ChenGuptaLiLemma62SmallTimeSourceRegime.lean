import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailBounds

/-!
# Chen--Gupta--Li Lemma 6.2: small-time source regime

The small-time branch of CGL Lemma 6.2 uses the literal cutoff
`X^(2ε) q / N` and the window `|v| ≤ X^(ε/2)`.  This file records that
source data and closes the elementary floor and ordinate arithmetic needed by
the low-height Gamma-factor estimate.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- Certified source data for the `|t| ≤ X^ε` branch of CGL Lemma 6.2.
Every inequality used by its public API is stored in this data rather than
passed as a raw proposition. -/
structure CGLLemma62SmallTimeSourceRegime
    (B : CGLLemma62InducedCharacter) (N : CGLPositiveLength) (t : ℝ) where
  base : ℝ
  base_one : 1 ≤ base
  ambient_le_base : (B.ambient.value : ℝ) ≤ base
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  ordinate_small : |t| ≤ base ^ epsilon
  cutoff_scale_two : 2 ≤ base ^ (2 * epsilon) * (B.ambient.value : ℝ) / N.value

/-- The literal small-time cutoff `X^(2ε)q/N` from CGL Lemma 6.2. -/
def CGLLemma62SmallTimeSourceRegime.cutoffScale
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) : ℝ :=
  S.base ^ (2 * S.epsilon) * (B.ambient.value : ℝ) / N.value

theorem cglLemma62_smallTime_cutoffScale_pos
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) : 0 < S.cutoffScale := by
  unfold CGLLemma62SmallTimeSourceRegime.cutoffScale
  have hbase : 0 < S.base := lt_of_lt_of_le zero_lt_one S.base_one
  have hq : 0 < (B.ambient.value : ℝ) := by exact_mod_cast B.ambient.positive
  have hN : 0 < (N.value : ℝ) := by exact_mod_cast N.positive
  exact div_pos (mul_pos (Real.rpow_pos_of_pos hbase _) hq) hN

/-- The exact integer split point for the small-time tail. -/
noncomputable def CGLLemma62SmallTimeSourceRegime.tailCutoff
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) : CGLLemma62TailCutoff where
  value := Nat.floor S.cutoffScale
  one_le := by
    apply (Nat.one_le_floor_iff S.cutoffScale).mpr
    have htwo : 2 ≤ S.cutoffScale := by
      simpa [CGLLemma62SmallTimeSourceRegime.cutoffScale] using S.cutoff_scale_two
    linarith

/-- Rounding CGL's small-time cutoff down loses at most a factor two. -/
theorem cglLemma62_smallTime_tailCutoff_half_scale_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) :
    S.cutoffScale / 2 ≤ (S.tailCutoff.value : ℝ) := by
  have hlt : S.cutoffScale < (Nat.floor S.cutoffScale : ℝ) + 1 :=
    Nat.lt_floor_add_one S.cutoffScale
  have hle : S.cutoffScale ≤ (Nat.floor S.cutoffScale : ℝ) + 1 := hlt.le
  have htwo : 2 ≤ S.cutoffScale := by
    simpa [CGLLemma62SmallTimeSourceRegime.cutoffScale] using S.cutoff_scale_two
  change S.cutoffScale / 2 ≤ (Nat.floor S.cutoffScale : ℝ)
  nlinarith

/-- CGL's literal small-time truncation radius. -/
def CGLLemma62SmallTimeSourceRegime.truncationRadius
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) : ℝ :=
  S.base ^ (S.epsilon / 2)

/-- A certified point in the source's small-time truncation window. -/
structure CGLLemma62SmallTimeWindowPoint
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t) where
  value : ℝ
  abs_le_radius : |value| ≤ S.truncationRadius

/-- The small-time source window keeps the Gamma-factor ordinate within
`2X^ε`, exactly the scale used by CGL's small-time bound. -/
theorem cglLemma62_smallTime_window_shiftedOrdinate_le
    {B : CGLLemma62InducedCharacter} {N : CGLPositiveLength} {t : ℝ}
    (S : CGLLemma62SmallTimeSourceRegime B N t)
    (p : CGLLemma62SmallTimeWindowPoint S) :
    |p.value - t| ≤ 2 * S.base ^ S.epsilon := by
  have hradius : S.truncationRadius ≤ S.base ^ S.epsilon := by
    unfold CGLLemma62SmallTimeSourceRegime.truncationRadius
    apply Real.rpow_le_rpow_of_exponent_le S.base_one
    linarith [S.epsilon_pos]
  have htriangle : |p.value - t| ≤ |p.value| + |t| := by
    calc
      |p.value - t| = |p.value + (-t)| := by ring_nf
      _ ≤ |p.value| + |-t| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  linarith [S.ordinate_small, p.abs_le_radius]

end

end RHTower
