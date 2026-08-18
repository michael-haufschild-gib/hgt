import GaloisForLFunctions.RHTower.HardyZSmoothAFEReal
import GaloisForLFunctions.RHTower.HardyTwistCellCombination
import GaloisForLFunctions.HTGeometry.IntervalIntegralTsumBound

/-!
# The direct edge of the Hardy-`Z` smooth AFE, cell by cell

The direct edge of `hardyZ_eq_two_tsum_smoothAFE_real` has `τ`-independent weights, so each of its
terms is covered by `abs_integral_afeTerm_le`.  This module discharges the two technical hypotheses
of the termwise interchange — integrability of each term on a cell and summability of the termwise
absolute masses — so that any summable family of per-term cell bounds bounds the cell integral of
the whole direct edge.
-/

open Set MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The `n`-th term of the direct edge of the real Hardy-`Z` smooth AFE. -/
def directEdgeTerm (x : ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  (Real.sqrt ((n : ℝ) + 1))⁻¹ *
    (Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFECutoff (((n : ℝ) + 1) / x)).re -
      Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
        (smoothAFECutoff (((n : ℝ) + 1) / x)).im)

theorem continuous_directEdgeTerm (x : ℝ) (n : ℕ) : Continuous (directEdgeTerm x n) := by
  unfold directEdgeTerm
  exact continuous_const.mul
    (((Real.continuous_cos.comp (continuous_hardyTwistPhase _)).mul continuous_const).sub
      ((Real.continuous_sin.comp (continuous_hardyTwistPhase _)).mul continuous_const))

theorem abs_directEdgeTerm_le (x : ℝ) (n : ℕ) (τ : ℝ) :
    |directEdgeTerm x n τ|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
        (|(smoothAFECutoff (((n : ℝ) + 1) / x)).re|
          + |(smoothAFECutoff (((n : ℝ) + 1) / x)).im|) := by
  unfold directEdgeTerm
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFECutoff (((n : ℝ) + 1) / x)).re -
        Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFECutoff (((n : ℝ) + 1) / x)).im|
      ≤ |Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFECutoff (((n : ℝ) + 1) / x)).re|
        + |Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ) *
          (smoothAFECutoff (((n : ℝ) + 1) / x)).im| := abs_sub _ _
    _ ≤ |(smoothAFECutoff (((n : ℝ) + 1) / x)).re|
        + |(smoothAFECutoff (((n : ℝ) + 1) / x)).im| := by
        rw [abs_mul, abs_mul]
        have hc := Real.abs_cos_le_one (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)
        have hs := Real.abs_sin_le_one (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)
        have h1 : |Real.cos (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)| *
            |(smoothAFECutoff (((n : ℝ) + 1) / x)).re|
            ≤ 1 * |(smoothAFECutoff (((n : ℝ) + 1) / x)).re| :=
          mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        have h2 : |Real.sin (hardyTwistPhase (Real.log ((n : ℝ) + 1)) τ)| *
            |(smoothAFECutoff (((n : ℝ) + 1) / x)).im|
            ≤ 1 * |(smoothAFECutoff (((n : ℝ) + 1) / x)).im| :=
          mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        linarith

theorem summable_directEdge_absMass {x : ℝ} (hx : 0 < x) {u v : ℝ} (huv : u ≤ v) :
    Summable (fun n : ℕ => ∫ τ in Ioc u v, |directEdgeTerm x n τ|) := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := (1 : ℝ)) (by norm_num)
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) :=
    summable_smoothAFEZetaMajorant (by norm_num)
  have hmaj : Summable
      (fun n : ℕ => ((v - u) * (2 * K * x)) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ))) :=
    hbase.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact integral_nonneg fun τ => abs_nonneg _
  · have hy : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hratio : (0 : ℝ) < ((n : ℝ) + 1) / x := by positivity
    have hb := hcut hratio
    have hrpow : ((((n : ℝ) + 1) / x)) ^ (-(1 : ℝ)) = x / ((n : ℝ) + 1) := by
      rw [Real.rpow_neg_one, inv_div]
    rw [hrpow] at hb
    have hre : |(smoothAFECutoff (((n : ℝ) + 1) / x)).re|
        ≤ K * (x / ((n : ℝ) + 1)) :=
      le_trans (Complex.abs_re_le_norm _) hb
    have him : |(smoothAFECutoff (((n : ℝ) + 1) / x)).im|
        ≤ K * (x / ((n : ℝ) + 1)) :=
      le_trans (Complex.abs_im_le_norm _) hb
    have hpt : ∀ τ : ℝ, |directEdgeTerm x n τ|
        ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ * (2 * (K * (x / ((n : ℝ) + 1)))) := by
      intro τ
      refine le_trans (abs_directEdgeTerm_le x n τ) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    have hconst : (Real.sqrt ((n : ℝ) + 1))⁻¹ * (2 * (K * (x / ((n : ℝ) + 1))))
        = (2 * K * x) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
      have h1 : Real.sqrt ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      have h2 : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) * ((n : ℝ) + 1)
          = ((n : ℝ) + 1) ^ ((3 : ℝ) / 2) := by
        nth_rewrite 2 [← Real.rpow_one ((n : ℝ) + 1)]
        rw [← Real.rpow_add hy]
        norm_num
      have hhalf : (0 : ℝ) < ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
      have hthree : (0 : ℝ) < ((n : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hy _
      rw [h1, ← h2]
      field_simp
    have hconv : (∫ τ in Ioc u v, |directEdgeTerm x n τ|)
        = ∫ τ in u..v, |directEdgeTerm x n τ| :=
      (intervalIntegral.integral_of_le huv).symm
    rw [hconv]
    calc (∫ τ in u..v, |directEdgeTerm x n τ|)
        ≤ ∫ _τ in u..v, (Real.sqrt ((n : ℝ) + 1))⁻¹ * (2 * (K * (x / ((n : ℝ) + 1)))) := by
          refine intervalIntegral.integral_mono_on huv ?_ intervalIntegrable_const
            fun τ _ => hpt τ
          exact ((continuous_directEdgeTerm x n).abs).intervalIntegrable u v
      _ = (v - u) * ((Real.sqrt ((n : ℝ) + 1))⁻¹ * (2 * (K * (x / ((n : ℝ) + 1))))) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = ((v - u) * (2 * K * x)) * (1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)) := by
          rw [hconst]; ring

/-- **The direct-edge cell bound.**  Any summable family of per-term cell bounds bounds the cell
integral of the whole direct edge. -/
theorem abs_integral_directEdge_le {x u v : ℝ} (hx : 0 < x) (huv : u ≤ v) {B : ℕ → ℝ}
    (hB : Summable B) (hbound : ∀ n : ℕ, |∫ τ in u..v, directEdgeTerm x n τ| ≤ B n) :
    |∫ τ in u..v, ∑' n : ℕ, directEdgeTerm x n τ| ≤ ∑' n : ℕ, B n :=
  abs_intervalIntegral_tsum_le huv
    (fun n => (continuous_directEdgeTerm x n).integrableOn_Ioc)
    (summable_directEdge_absMass hx huv) hbound hB

/-- The per-term cell bound below the conductor, in the form the direct edge consumes. -/
theorem abs_integral_directEdgeTerm_le {x u v δ T : ℝ} {n : ℕ} (huv : u ≤ v) (hδ : 0 < δ)
    (hT : 0 < T) (hu : T ≤ u)
    (herr : 33 / (16 * T ^ 2) + Real.pi / (2 * T) ≤ δ)
    (hL : Real.log ((n : ℝ) + 1) ≤ Real.log (T / (2 * Real.pi)) / 2 - 2 * δ) :
    |∫ τ in u..v, directEdgeTerm x n τ|
      ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ *
          (|(smoothAFECutoff (((n : ℝ) + 1) / x)).re|
            + |(smoothAFECutoff (((n : ℝ) + 1) / x)).im|) *
          (2 / δ + (v - u) * (1 / T ^ 2 + Real.pi / (4 * T)) / δ ^ 2) :=
  abs_integral_afeTerm_le (c := (Real.sqrt ((n : ℝ) + 1))⁻¹)
    (by positivity) huv hδ hT hu herr hL

end RHTower

end
