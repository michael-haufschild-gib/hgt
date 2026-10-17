import GaloisForLFunctions.RHTower.CHMDCompactSourceClass
import GaloisForLFunctions.RHTower.XiWeilHilbertCore

/-!
# Absolute Xi sampling and strong compact truncation

The strip tail bound controls the full multiplicity-exact square-sum, rather
than only the signed Weil sum. No location assumption on the zeros is used.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
noncomputable section
namespace RHTower
open WeilSpectral

theorem xiWeilSquareSummable_of_strip_bound {F : ℂ → ℂ} {M : ℝ}
    (hF : ∀ z : ℂ, |z.im| ≤ 1/2 → (1+|z.re|)*‖F z‖ ≤ M) :
    XiWeilSquareSummable F := by
  change Summable (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖^2)
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (M^2))
  ·
    let z := xiSpectralPoint q
    have hz : |z.im| ≤ 1/2 := (abs_im_lt_half_of_XiC_eq_zero (XiC_xiSpectralPoint_eq_zero q)).le
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hnorm : ‖z‖ ≤ 1+|z.re| := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      linarith
    have hb : ‖F z‖ ≤ M/‖z‖ := by
      apply (le_div_iff₀ hn).mpr
      exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
        (by simpa only [mul_comm] using hF z hz)
    have hs := pow_le_pow_left₀ (norm_nonneg (F z)) hb 2
    calc ‖F z‖^2 ≤ (M/‖z‖)^2 := hs
      _ = M^2*(1/‖z‖^2) := by ring

theorem WeilSpectral.ExpDecayTest.strip_bound {f : ℝ → ℝ} (hf : ExpDecayTest f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, |z.im| ≤ 1/2 →
      (1+|z.re|)*‖paperFT (fun x => (f x : ℂ)) z‖ ≤ M := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨∫ x, tailMajorant f Λ x, integral_nonneg fun x => tailMajorant_nonneg f hΛ0 x, ?_⟩
  intro z hz
  apply le_of_tendsto (((tendsto_paperFT_truncTest hf hz).norm).const_mul (1+|z.re|))
  exact Eventually.of_forall fun L => one_add_abs_re_mul_norm_paperFT_truncTest_le hf hΛ hΛ0 L hz

theorem WeilSpectral.ExpDecayTest.squareSummable {f : ℝ → ℝ} (hf : ExpDecayTest f) :
    XiWeilSquareSummable (paperFT (fun x => (f x : ℂ))) := by
  obtain ⟨M, _, hb⟩ := hf.strip_bound
  exact xiWeilSquareSummable_of_strip_bound hb

def realXiEvaluation (f : ℝ → ℝ) (hf : ExpDecayTest f) : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilEvaluationLp (paperFT (fun x => (f x : ℂ))) hf.squareSummable

theorem realXiEvaluation_trunc_tendsto {f : ℝ → ℝ} (hf : ExpDecayTest f) :
    Tendsto (fun L : ℝ => realXiEvaluation (truncTest f L)
      (CHMDDoobGraph.compact_expDecayTest (contDiff_truncTest hf.1 L)
        (hasCompactSupport_truncTest f L))) atTop (𝓝 (realXiEvaluation f hf)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  let V : ℝ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun L =>
    realXiEvaluation (truncTest f L)
      (CHMDDoobGraph.compact_expDecayTest (contDiff_truncTest hf.1 L)
        (hasCompactSupport_truncTest f L)) - realXiEvaluation f hf
  have hb (L : ℝ) (q : XiZeroCopy) :
      ‖V L q‖^2 ≤ (tailBound f Λ L)^2 * (1/‖xiSpectralPoint q‖^2) := by
    let z := xiSpectralPoint q
    have hz : |z.im| ≤ 1/2 := (abs_im_lt_half_of_XiC_eq_zero (XiC_xiSpectralPoint_eq_zero q)).le
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hnorm : ‖z‖ ≤ 1+|z.re| := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      linarith
    have hpoint := one_add_abs_re_mul_norm_paperFT_truncTest_sub_self_le hf hΛ hΛ0 L hz
    change (1+|z.re|)*‖V L q‖ ≤ tailBound f Λ L at hpoint
    have hd : ‖V L q‖ ≤ tailBound f Λ L/‖z‖ := by
      apply (le_div_iff₀ hn).mpr
      exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
        (by simpa only [mul_comm] using hpoint)
    calc ‖V L q‖^2 ≤ (tailBound f Λ L/‖z‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
      _ = _ := by ring
  have hnorm (L : ℝ) : ‖V L‖^2 ≤
      (tailBound f Λ L)^2 * (∑' q : XiZeroCopy, 1/‖xiSpectralPoint q‖^2) := by
    rw [HilbertSchmidt.lp_norm_sq_eq, ← tsum_mul_left]
    exact (HilbertSchmidt.summable_coe_sq (V L)).tsum_le_tsum (hb L)
      (xiSpectralPoint_inv_sq_summable.mul_left _)
  have ht := ((tendsto_tailBound hf hΛ0).pow 2).mul_const
    (∑' q : XiZeroCopy, 1/‖xiSpectralPoint q‖^2)
  have hs : Tendsto (fun L => ‖V L‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hnorm
      (by simpa using ht)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [V, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs.sqrt

end RHTower
