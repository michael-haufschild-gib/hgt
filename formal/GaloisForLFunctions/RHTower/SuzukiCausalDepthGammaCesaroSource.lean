import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaMaximalSource
import Mathlib.Algebra.Order.Chebyshev

/-!
# An explicit universal Gamma graph regularization

Cesàro averaging removes the output-dependent subsequence from radial source
regularization. The same input operators converge in every actual Gamma graph
norm. Parameters and outputs impose no additional approximation hypothesis.
-/

open Filter Topology
open scoped BigOperators ENNReal InnerProduct
set_option autoImplicit false

noncomputable section
namespace RHTower

private abbrev H := SuzukiCausalDepthGammaTraceL2

private theorem norm_add_sq_le_twice {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hn := pow_le_pow_left₀ (norm_nonneg (x + y)) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem norm_cesaro_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → E) (N : ℕ) :
    ‖(N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, f n‖ ^ 2 ≤
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖f n‖ ^ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  calc
    ((N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f n‖) ^ 2 ≤
        ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖f n‖) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ _ := by
      simpa only [Finset.card_range, div_eq_mul_inv, mul_comm] using
        (sum_div_card_sq_le_sum_sq_div_card
          (s := Finset.range N) (f := fun n => ‖f n‖))

private theorem summable_tail (v : H) :
    Summable (fun j : ℕ => ‖v (Sum.inr (j + 1))‖ ^ 2) := by
  apply (HilbertSchmidt.summable_coe_sq v).comp_injective
  intro j k hjk
  exact Nat.add_right_cancel (Sum.inr.inj hjk)

private theorem first_tail_error_le (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) (n : ℕ) :
    ‖v (Sum.inr 1) - suzukiGammaRegularizedSynthesis h a n u (Sum.inr 1)‖ ^ 2 ≤
      suzukiGammaJacobiTailEnergy (fun j => ‖v (Sum.inr (j + 1))‖ ^ 2) n := by
  have hs := summable_suzukiGammaJacobiTailWeight_mul (summable_tail v)
    (fun j => sq_nonneg _) n
  have ht := hs.le_tsum n (fun j _ =>
    mul_nonneg (suzukiGammaJacobiTailWeight_nonneg n j) (sq_nonneg _))
  calc
    _ = suzukiGammaJacobiTailWeight n n * ‖v (Sum.inr (n + 1))‖ ^ 2 := by
      rw [show 1 = 0 + 1 from rfl, suzukiGammaRegularizedSynthesis_tail_error h a huv]
      rw [norm_mul, norm_div, mul_pow, div_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      simp only [zero_add, suzukiGammaJacobiTailWeight, le_refl, ↓reduceIte,
        Nat.sub_self, suzukiGammaBoundaryCoefficient, suzukiCausalDepthGammaSurvivingDegree,
        semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]
    _ ≤ _ := ht

/-- The average of the squared full output errors vanishes. The cancelled
first row supplies the missing exceptional coordinate. -/
theorem tendsto_suzukiGammaRegularizedSynthesis_mean_error_sq
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖v - suzukiGammaRegularizedSynthesis h a n u‖ ^ 2) atTop (𝓝 0) := by
  let e : ℕ → H := fun n => v - suzukiGammaRegularizedSynthesis h a n u
  let b : ℕ → ℝ := fun j => ‖v (Sum.inr (j + 1))‖ ^ 2
  let q : ℕ → ℂ := fun n => inner ℂ (suzukiGammaBoundaryRowVector h a 0)
    (u - suzukiGammaSourceRegularization n u)
  let c₀ := suzukiGammaBoundaryCoefficient 0
  let c₁ := suzukiGammaBoundaryCoefficient 1
  have hc₁ : 0 < c₁ := suzukiGammaBoundaryCoefficient_pos 1
  have hq : Tendsto q atTop (𝓝 0) := by
    have hd : Tendsto (fun n => u - suzukiGammaSourceRegularization n u) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := u)).sub
        (tendsto_suzukiGammaSourceRegularization u)
    have hi := (innerSL ℂ (suzukiGammaBoundaryRowVector h a 0)).continuous.tendsto 0
    simpa only [Function.comp_def, map_zero, innerSL_apply_apply] using hi.comp hd
  have hqmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖q n‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      (hq.norm.pow 2).cesaro
  have hEmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      suzukiGammaJacobiTailEnergy b n) atTop (𝓝 0) :=
    tendsto_suzukiGammaJacobiTailEnergy_mean_zero (summable_tail v) (fun j => sq_nonneg _)
  have hpoint (n : ℕ) : c₁ ^ 2 * ‖e n‖ ^ 2 ≤
      2 * ‖q n‖ ^ 2 + (2 * c₀ ^ 2 + c₁ ^ 2) * suzukiGammaJacobiTailEnergy b n := by
    have herr : (u - suzukiGammaSourceRegularization n u, e n) ∈
        suzukiGammaSourceEquationGraph h a :=
      (suzukiGammaSourceEquationGraph h a).sub_mem huv
        (suzukiGammaTwoLegClosedGraph_le_equationGraph h a
          (suzukiGammaRegularizedSynthesis_mem_closedGraph h a n u))
    have hr : (c₁ : ℂ) * e n (Sum.inr 0) = q n + (c₀ : ℂ) * e n (Sum.inr 1) := by
      have ht := suzukiGammaSourceEquationGraph_row h a herr 0
      change (c₁ : ℂ) * e n (Sum.inr 0) - (c₀ : ℂ) * e n (Sum.inr 1) = q n at ht
      linear_combination ht
    have hs := norm_add_sq_le_twice (q n) ((c₀ : ℂ) * e n (Sum.inr 1))
    rw [← hr, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at hs
    have ht : ‖e n (Sum.inr 1)‖ ^ 2 ≤ suzukiGammaJacobiTailEnergy b n :=
      first_tail_error_le h a huv n
    have he : ‖e n‖ ^ 2 = ‖e n (Sum.inr 0)‖ ^ 2 + suzukiGammaJacobiTailEnergy b n :=
      suzukiGammaRegularizedSynthesis_error_norm_sq h a huv n
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg c₀)]
  have hmean (N : ℕ) : c₁ ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖e n‖ ^ 2) ≤
      2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖q n‖ ^ 2) +
        (2 * c₀ ^ 2 + c₁ ^ 2) * ((N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N, suzukiGammaJacobiTailEnergy b n) := by
    have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n (_ : n ∈ Finset.range N) =>
      hpoint n) (inv_nonneg.mpr (Nat.cast_nonneg N) : 0 ≤ (N : ℝ)⁻¹)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    nlinarith [hs]
  have hbound : Tendsto (fun N : ℕ => (2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖q n‖ ^ 2) +
      (2 * c₀ ^ 2 + c₁ ^ 2) * ((N : ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, suzukiGammaJacobiTailEnergy b n)) / c₁ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_div] using
      ((hqmean.const_mul 2).add (hEmean.const_mul (2 * c₀ ^ 2 + c₁ ^ 2))).div_const (c₁ ^ 2)
  apply squeeze_zero (fun N => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun n _ => sq_nonneg _)) _ hbound
  intro N
  exact (le_div_iff₀ (by positivity : 0 < c₁ ^ 2)).mpr
    (by simpa only [mul_comm] using hmean N)

/-- Parameter-independent averaged input regularization. -/
def suzukiGammaCesaroSource (N : ℕ) : H →L[ℂ] H :=
  Complex.ofReal ((N : ℝ)⁻¹) • ∑ n ∈ Finset.range N, suzukiGammaSourceRegularization n

/-- The corresponding averaged output uses the literal two-leg columns. -/
def suzukiGammaCesaroSynthesis (h a : Set.Ioi (0 : ℝ)) (N : ℕ) : H →L[ℂ] H :=
  Complex.ofReal ((N : ℝ)⁻¹) • ∑ n ∈ Finset.range N, suzukiGammaRegularizedSynthesis h a n

theorem suzukiGammaCesaroSource_apply (N : ℕ) (u : H) :
    suzukiGammaCesaroSource N u =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, suzukiGammaSourceRegularization n u := by
  rw [suzukiGammaCesaroSource, _root_.smul_apply, _root_.sum_apply, Complex.coe_smul]

theorem suzukiGammaCesaroSynthesis_apply (h a : Set.Ioi (0 : ℝ)) (N : ℕ) (u : H) :
    suzukiGammaCesaroSynthesis h a N u =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, suzukiGammaRegularizedSynthesis h a n u := by
  rw [suzukiGammaCesaroSynthesis, _root_.smul_apply, _root_.sum_apply, Complex.coe_smul]

theorem tendsto_suzukiGammaCesaroSource (u : H) :
    Tendsto (fun N => suzukiGammaCesaroSource N u) atTop (𝓝 u) := by
  simpa only [suzukiGammaCesaroSource_apply] using
      (tendsto_suzukiGammaSourceRegularization u).cesaro_smul

/-- Full-sequence convergence holds for every solution of the actual source
equations; the regularizers do not depend on the output or Gamma parameters. -/
theorem tendsto_suzukiGammaCesaroSynthesis
    (h a : Set.Ioi (0 : ℝ)) {u v : H}
    (huv : (u, v) ∈ suzukiGammaSourceEquationGraph h a) :
    Tendsto (fun N => suzukiGammaCesaroSynthesis h a N u) atTop (𝓝 v) := by
  let e : ℕ → H := fun n => v - suzukiGammaRegularizedSynthesis h a n u
  have hs : Tendsto (fun N : ℕ => ‖(N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, e n‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun N => sq_nonneg _) (norm_cesaro_sq_le e)
    exact tendsto_suzukiGammaRegularizedSynthesis_mean_error_sq h a huv
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  have he : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, e n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hv := (tendsto_const_nhds (x := v) : Tendsto (fun _ : ℕ => v) atTop (𝓝 v)).cesaro_smul
  have ht := hv.sub he
  simpa only [e, Finset.sum_sub_distrib, smul_sub, sub_sub_cancel, sub_zero,
    suzukiGammaCesaroSynthesis_apply] using ht

end RHTower
