import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFarPointBounds

/-!
# Chen--Gupta--Li Lemma 6.2: truncated far-left tail

This turns the five-factor high-point bound into the exact finite ordinate
window estimate used in CGL's `I₂` analysis.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- A symmetric ordinate window separated from the functional-factor's
low-height region. -/
structure CGLLemma62TailTruncationWindow (t : ℝ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  separated : 2 + radius ≤ |t|

private theorem cglLemma62_tailWindow_abs_le
    {t : ℝ} (U : CGLLemma62TailTruncationWindow t)
    {v : ℝ} (hv : v ∈ Set.uIoc (-U.radius) U.radius) : |v| ≤ U.radius := by
  rw [Set.uIoc_of_le (by linarith [U.radius_nonneg])] at hv
  exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩

private theorem cglLemma62_tailWindow_high
    {t : ℝ} (U : CGLLemma62TailTruncationWindow t)
    {v : ℝ} (hv : v ∈ Set.uIoc (-U.radius) U.radius) : 2 ≤ |v - t| := by
  have hvabs := cglLemma62_tailWindow_abs_le U hv
  have htri : |t| ≤ |t - v| + |v| := by
    calc
      |t| = |(t - v) + v| := by congr 1; ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_sub_comm]
  linarith [U.separated]

/-- The literal far-left complementary tail, integrated over a CGL truncation
window, is bounded by its five-factor budget times the window length. -/
theorem cglLemma62_farTail_truncated_integral_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth)
    (U : CGLLemma62TailTruncationWindow t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -U.radius..U.radius,
        cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * U.radius) := by
  rcases cglLemma62_farTail_high_point_bound w N B t M d with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  have hpoint : ∀ v ∈ Set.uIoc (-U.radius) U.radius,
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) := by
    intro v hv
    have hhigh := cglLemma62_tailWindow_high U hv
    have hvabs := cglLemma62_tailWindow_abs_le U hv
    have hbase : 1 + |v - t| ≤ 1 + |t| + U.radius := by
      have htri : |v - t| ≤ |v| + |t| := by
        calc
          |v - t| = |v + (-t)| := by ring_nf
          _ ≤ |v| + |-t| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith
    have hpow : (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) ≤
        (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact hbase
      · positivity
    exact (hbound v hhigh).trans (mul_le_mul_of_nonneg_left hpow hC)
  calc
    ‖∫ v : ℝ in -U.radius..U.radius,
        cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        (C * (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2)) *
          |U.radius - (-U.radius)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = C * (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) *
        (2 * U.radius) := by
      have hwidth : |U.radius - (-U.radius)| = 2 * U.radius := by
        rw [show U.radius - (-U.radius) = 2 * U.radius by ring_nf,
          abs_of_nonneg (mul_nonneg (by norm_num) U.radius_nonneg)]
      rw [hwidth]

end

end RHTower
