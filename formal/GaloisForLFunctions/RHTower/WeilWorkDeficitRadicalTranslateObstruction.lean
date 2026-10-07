import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# A fixed arithmetic cost for positive mixtures of translated Riemann kernels

Allow arbitrary translations, nonnegative weights, and distinct truncations beyond `log 2 + 1`.
Their spectral density is bounded by a fixed multiple of their arithmetic value at `2`.
Consequently spectral normalization cannot make the full arithmetic repair budget vanish in
this family. Coherent linear combinations inside a test are not covered by this obstruction.
-/

open Complex MeasureTheory
open scoped Real ComplexConjugate NNReal
open Zeta23

namespace RHTower.WeilSpectral

noncomputable section

private theorem weilTest_transl_self (f : ℝ → ℂ) (y x : ℝ) :
    EF.weilTest (transl y f) (transl y f) x = EF.weilTest f f x := by
  simp only [weilTest_apply, transl]
  simp_rw [show ∀ u : ℝ, u - x - y = (u - y) - x from fun u => by ring]
  exact integral_sub_right_eq_self (fun u => f u * conj (f (u - x))) y

private theorem norm_truncatedRiemannKernel_le (L u : ℝ) :
    ‖truncatedRiemannKernel L u‖ ≤ ‖riemannPhiKernel u‖ := by
  rw [truncatedRiemannKernel_eq, riemannPhiKernel_eq_ofReal,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (truncatedRiemannKernelReal_nonneg L u),
    abs_of_pos (riemannKernelReal_pos u)]
  exact (mul_le_mul_of_nonneg_left (bulkCutoff_le_one L u)
    (riemannKernelReal_pos u).le).trans_eq (mul_one _)

/-- A positive mixture of translated truncated Riemann kernels pays a fixed positive
arithmetic cost at `2` per unit of spectral density, uniformly over all real frequencies.
Cutoffs and weights carry their intrinsic domain constraints; no spectral premise is used. -/
theorem exists_logValue_two_ge_translated_radical_density :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ)
      (L : Fin N → {L : ℝ // Real.log 2 + 1 ≤ L}) (y : Fin N → ℝ)
      (w : Fin N → ℝ≥0) (r : ℝ),
      δ * (∑ i, (w i : ℝ) * ‖paperFT (transl (y i) (truncatedRiemannKernel (L i))) r‖ ^ 2) ≤
        ∑ i, (w i : ℝ) * WeilOneSided.logValue
          (transl (y i) (truncatedRiemannKernel (L i))) 2 := by
  obtain ⟨κ, hκ, hκL⟩ :=
    exists_weilTest_truncatedRiemannKernel_ge (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  let M : ℝ := ∫ u, ‖riemannPhiKernel u‖
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  let a : ℝ := κ / Real.sqrt 2
  have ha : 0 < a := div_pos hκ (Real.sqrt_pos.mpr (by norm_num))
  let δ : ℝ := a / (M ^ 2 + 1)
  have hδ : 0 < δ := div_pos ha (by positivity)
  have hδM : δ * M ^ 2 ≤ a := by
    have heq : δ * (M ^ 2 + 1) = a := div_mul_cancel₀ a (by positivity)
    nlinarith
  refine ⟨δ, hδ, fun N L y w r => ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hFT : ‖paperFT (transl (y i) (truncatedRiemannKernel (L i))) r‖ ≤ M := by
    rw [paperFT_transl, norm_mul, norm_cexp_I_mul_ofReal, one_mul]
    refine (norm_paperFT_real_le _ r).trans ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      integrable_riemannPhiKernel.norm
      (Filter.Eventually.of_forall fun u => norm_truncatedRiemannKernel_le (L i) u)
  have hFTsq : ‖paperFT (transl (y i) (truncatedRiemannKernel (L i))) r‖ ^ 2 ≤ M ^ 2 := by
    nlinarith [norm_nonneg (paperFT (transl (y i) (truncatedRiemannKernel (L i))) r)]
  have haL : a ≤ WeilOneSided.logValue (transl (y i) (truncatedRiemannKernel (L i))) 2 := by
    simp only [WeilOneSided.logValue, weilTest_transl_self, Complex.add_re, Nat.cast_ofNat]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg 2)
    have hpos := weilTest_truncatedRiemannKernel_re_nonneg (L i) (-Real.log 2)
    have hlower := hκL (L i) (L i).property
    linarith
  have hsingle := (mul_le_mul_of_nonneg_left hFTsq hδ.le).trans (hδM.trans haL)
  simpa only [mul_left_comm δ] using mul_le_mul_of_nonneg_left hsingle (w i).coe_nonneg

end

end RHTower.WeilSpectral
