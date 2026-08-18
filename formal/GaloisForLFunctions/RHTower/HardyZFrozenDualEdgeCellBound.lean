import GaloisForLFunctions.RHTower.HardyZDirectEdgeCellBound

/-!
# The frozen dual edge of the Hardy-`Z` smooth AFE, cell by cell

The dual weight `smoothAFEZetaDualWeight τ Y` depends on the height `τ`, so its cell integral is not
directly covered by the constant-weight estimate.  Freezing the weight at one height makes it
constant, and the tree already prices that: `exists_norm_smoothAFEZetaDualSeriesWeightError_le`
bounds the whole frozen-series error by `(A/x)·|τ − u|` times the `3/2`-power majorant.

This module treats the frozen edge, whose weights are `τ`-independent and therefore obey the same
cell estimate as the direct edge.
-/

open Set MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The `n`-th term of the dual edge with the weight frozen at height `u`. -/
def dualEdgeTermAt (x u : ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  (Real.sqrt ((n : ℝ) + 1))⁻¹ *
    (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re +
      Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im)

theorem continuous_dualEdgeTermAt (x u : ℝ) (n : ℕ) : Continuous (dualEdgeTermAt x u n) := by
  unfold dualEdgeTermAt
  exact continuous_const.mul
    (((Real.continuous_cos.comp (continuous_hardyTwistPhase _)).mul continuous_const).add
      ((Real.continuous_sin.comp (continuous_hardyTwistPhase _)).mul continuous_const))

theorem abs_dualEdgeTermAt_le (x u : ℝ) (n : ℕ) (τ : ℝ) :
    |dualEdgeTermAt x u n τ|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (|(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
          + |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|) := by
  unfold dualEdgeTermAt
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hc := Real.abs_cos_le_one (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)
  have hs := Real.abs_sin_le_one (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)
  calc |Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re +
        Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|
      ≤ |Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
        + |Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im| := abs_add_le _ _
    _ ≤ |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
        + |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im| := by
        rw [abs_mul, abs_mul]
        have h1 : |Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)| *
            |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
            ≤ 1 * |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re| :=
          mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        have h2 : |Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)| *
            |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|
            ≤ 1 * |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im| :=
          mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        linarith

theorem summable_dualEdgeAt_absMass {x u : ℝ} (hx : 0 < x) {a b : ℝ} (hab : a ≤ b) :
    Summable (fun n : ℕ => ∫ τ in Ioc a b, |dualEdgeTermAt x u n τ|) := by
  obtain ⟨K, hK, hweight⟩ := exists_norm_smoothAFEZetaDualWeight_le_inv
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hmaj : Summable
      (fun n : ℕ => ((b - a) * (2 * (K * (1 + |u|)) / x)) *
        (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ))) := hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact integral_nonneg fun τ => abs_nonneg _
  · have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hY : (0 : ℝ) < ((n : ℝ) + 1) * x := by positivity
    have hb := hweight u hY
    have hre : |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
        ≤ K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹ :=
      le_trans (Complex.abs_re_le_norm _) hb
    have him : |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|
        ≤ K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹ :=
      le_trans (Complex.abs_im_le_norm _) hb
    have hpt : ∀ τ : ℝ, |dualEdgeTermAt x u n τ|
        ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (2 * (K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹)) := by
      intro τ
      refine le_trans (abs_dualEdgeTermAt_le x u n τ) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    have hconst : (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (2 * (K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹))
        = (2 * (K * (1 + |u|)) / x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
      have h1 : Real.sqrt ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      have h2 : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) * ((n : ℝ) + 1)
          = ((n : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
        nth_rewrite 2 [← Real.rpow_one ((n : ℝ) + 1)]
        rw [← Real.rpow_add hy]
        norm_num
      have hhalf : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
      rw [h1, ← h2]
      field_simp
    have hconv : (∫ τ in Ioc a b, |dualEdgeTermAt x u n τ|)
        = ∫ τ in a..b, |dualEdgeTermAt x u n τ| :=
      (intervalIntegral.integral_of_le hab).symm
    rw [hconv]
    calc (∫ τ in a..b, |dualEdgeTermAt x u n τ|)
        ≤ ∫ _τ in a..b, (Real.sqrt ((n : ℝ) + 1))⁻¹ *
            (2 * (K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹)) := by
          refine intervalIntegral.integral_mono_on hab ?_ intervalIntegrable_const
            fun τ _ => hpt τ
          exact ((continuous_dualEdgeTermAt x u n).abs).intervalIntegrable a b
      _ = (b - a) * ((Real.sqrt ((n : ℝ) + 1))⁻¹ *
            (2 * (K * (1 + |u|) * (((n : ℝ) + 1) * x)⁻¹))) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = ((b - a) * (2 * (K * (1 + |u|)) / x)) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
          rw [hconst]; ring

/-- **The frozen dual-edge cell bound.** -/
theorem abs_integral_frozenDualEdge_le {x u a b : ℝ} (hx : 0 < x) (hab : a ≤ b) {B : ℕ → ℝ}
    (hB : Summable B) (hbound : ∀ n : ℕ, |∫ τ in a..b, dualEdgeTermAt x u n τ| ≤ B n) :
    |∫ τ in a..b, ∑' n : ℕ, dualEdgeTermAt x u n τ| ≤ ∑' n : ℕ, B n :=
  abs_intervalIntegral_tsum_le hab
    (fun n => (continuous_dualEdgeTermAt x u n).integrableOn_Ioc)
    (summable_dualEdgeAt_absMass hx hab) hbound hB

/-- The per-term frozen dual-edge cell bound below the conductor. -/
theorem abs_integral_dualEdgeTermAt_le {x u a b δ T : ℝ} {n : ℕ} (hab : a ≤ b) (hδ : 0 < δ)
    (hT : 0 < T) (ha : T ≤ a)
    (herr : 33 / (16 * T ^ 2) + Real.pi / (2 * T) ≤ δ)
    (hL : Real.log ((n : ℝ) + 1) ≤ Real.log (T / (2 * Real.pi)) / 2 - 2 * δ) :
    |∫ τ in a..b, dualEdgeTermAt x u n τ|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (|(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
            + |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|) *
          (2 / δ + (b - a) * (1 / T ^ 2 + Real.pi / (4 * T)) / δ ^ 2) := by
  have hrw : (∫ τ in a..b, dualEdgeTermAt x u n τ)
      = (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        ∫ τ in a..b, ((smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re *
            Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)
          + (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im *
            Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    unfold dualEdgeTermAt
    ring
  rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹)]
  have hmain := abs_integral_hardyTwistCombination_le (u := a) (v := b)
    (L := Real.log ((n : ℝ) + 1)) (δ := δ) (T := T)
    (a := (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re)
    (b := (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im) hab hδ hT ha herr hL
  calc (Real.sqrt ((n : ℝ) + 1))⁻¹ *
      |∫ τ in a..b, ((smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re *
          Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)
        + (smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im *
          Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ))|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        ((|(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
            + |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|) *
          (2 / δ + (b - a) * (1 / T ^ 2 + Real.pi / (4 * T)) / δ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (|(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).re|
            + |(smoothAFEZetaDualWeight u (((n : ℝ) + 1) * x)).im|) *
          (2 / δ + (b - a) * (1 / T ^ 2 + Real.pi / (4 * T)) / δ ^ 2) := by ring

end RHTower

end
