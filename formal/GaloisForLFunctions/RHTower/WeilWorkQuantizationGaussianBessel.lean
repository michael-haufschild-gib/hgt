import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianEnergy
import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianGram

/-!
# Finite Bessel lower bounds for the actual centered source

Integrating a nonnegative square gives an exact finite variational bound.
The actual coefficient-recovery theorem and finite Gaussian Gram limit
then recover every fixed finite coefficient energy. Full positivity pays
all source estimates; no physical mean or infinite boundary series is assumed.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
variable {lam : ℕ → ℝ}

private theorem centered_polynomial_cross (hW : WeilPositiveFull lam)
    (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (T t : ℝ) :
    (quantizationCenteredTrace hW t * conj (quantizationGaussianPolynomial S c ω t)) *
        (quantizationGaussianWeight T t : ℂ) =
      ∑ n ∈ S, conj (c n) * quantizationCenteredGaussianTrace hW T (ω n) t := by
  simp only [quantizationGaussianPolynomial, map_sum, map_mul, conj_conj,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  unfold quantizationCenteredGaussianTrace quantizationGaussianCharacter
  ring

/-- A finite Gaussian variational lower bound for the literal centered trace. -/
theorem quantizationCenteredGaussianEnergy_variational (hW : WeilPositiveFull lam)
    (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    2 * (∑ n ∈ S, conj (c n) * quantizationCenteredGaussianMoment hW T (ω n)).re -
        (quantizationGaussianGram S c ω T).re ≤
      2 * quantizationCenteredGaussianEnergy hW T / (T * Real.sqrt Real.pi) := by
  let M := T * Real.sqrt Real.pi
  have hM : 0 < M := mul_pos hT (Real.sqrt_pos.mpr Real.pi_pos)
  have hJ (n : ℕ) := (integrable_quantizationCenteredGaussianTrace hW hT (ω n)).const_mul
    (conj (c n))
  have hsum := integrable_finsetSum S fun n _ => hJ n
  have hleft := hsum.re.const_mul 2
  have hA := integrable_quantizationCenteredTrace_gaussian_square hW hT
  have hP := integrable_quantizationGaussianPolynomial_square S c ω hT
  have hp (t : ℝ) :
      2 * (∑ n ∈ S, conj (c n) * quantizationCenteredGaussianTrace hW T (ω n) t).re ≤
        ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t +
        ‖quantizationGaussianPolynomial S c ω t‖ ^ 2 * quantizationGaussianWeight T t := by
    rw [← centered_polynomial_cross hW S c ω T t]
    have hn := Complex.re_le_norm
      (quantizationCenteredTrace hW t * conj (quantizationGaussianPolynomial S c ω t))
    rw [norm_mul, Complex.norm_conj] at hn
    have hg : 0 ≤ quantizationGaussianWeight T t := (Real.exp_pos _).le
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hn ⊢
    nlinarith [mul_le_mul_of_nonneg_right hn hg,
      mul_nonneg (sq_nonneg (‖quantizationCenteredTrace hW t‖ -
        ‖quantizationGaussianPolynomial S c ω t‖)) hg]
  have hi := integral_mono hleft (hA.add hP) hp
  change (∫ t : ℝ, 2 * (∑ n ∈ S,
      conj (c n) * quantizationCenteredGaussianTrace hW T (ω n) t).re) ≤
    ∫ t : ℝ, ‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t +
      ‖quantizationGaussianPolynomial S c ω t‖ ^ 2 * quantizationGaussianWeight T t at hi
  have hir : (∫ t : ℝ, (∑ n ∈ S,
      conj (c n) * quantizationCenteredGaussianTrace hW T (ω n) t).re) =
      (∫ t : ℝ, ∑ n ∈ S,
        conj (c n) * quantizationCenteredGaussianTrace hW T (ω n) t).re := integral_re hsum
  rw [integral_const_mul, hir, integral_finsetSum S (fun n _ => hJ n),
    integral_add hA hP, integral_quantizationCenteredTrace_gaussian_square,
    integral_quantizationGaussianPolynomial_square S c ω hT] at hi
  have hmom (n : ℕ) : (∫ t : ℝ, quantizationCenteredGaussianTrace hW T (ω n) t) =
      (M : ℂ) * quantizationCenteredGaussianMoment hW T (ω n) := by
    dsimp [M, quantizationCenteredGaussianMoment]
    have hm : ((T * Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]
  have hsumEq : (∑ n ∈ S, ∫ t : ℝ,
      conj (c n) * quantizationCenteredGaussianTrace hW T (ω n) t) =
      (M : ℂ) * ∑ n ∈ S, conj (c n) * quantizationCenteredGaussianMoment hW T (ω n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul, hmom]
    ring
  rw [hsumEq] at hi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hi
  apply (le_div_iff₀ hM).mpr
  dsimp only [M] at hi ⊢
  nlinarith

/-- Every fixed finite coefficient set contributes its full asymptotic physical energy. -/
theorem eventually_quantizationCenteredGaussianEnergy_finset_lower
    (hW : WeilPositiveFull lam) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      (∑ n ∈ S, ‖quantizationCenteredCoeff hW n‖ ^ 2 / n) - ε ≤
        2 * quantizationCenteredGaussianEnergy hW T / (T * Real.sqrt Real.pi) := by
  let c : ℕ → ℂ := fun n => quantizationCenteredCoeff hW n / (Real.sqrt (n : ℝ) : ℂ)
  let Q : ℝ := ∑ n ∈ S, ‖c n‖ ^ 2
  have hω : Set.InjOn (fun n : ℕ => Real.log (n : ℝ)) S := by
    intro n hn m hm he
    have hn0 : (n : ℝ) ∈ Ioi 0 := by change 0 < (n : ℝ); exact_mod_cast hS n hn
    have hm0 : (m : ℝ) ∈ Ioi 0 := by change 0 < (m : ℝ); exact_mod_cast hS m hm
    exact_mod_cast Real.log_injOn_pos hn0 hm0 he
  have hmom := tendsto_finsetSum S fun n hn =>
    (tendsto_quantizationCenteredGaussianMoment hW (hS n hn)).const_mul (conj (c n))
  have heq : (∑ n ∈ S, conj (c n) * c n) = (Q : ℂ) := by
    simp only [Q, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change Tendsto (fun T : ℝ => ∑ n ∈ S,
      conj (c n) * quantizationCenteredGaussianMoment hW T (Real.log (n : ℝ)))
    atTop (𝓝 (∑ n ∈ S, conj (c n) * c n)) at hmom
  rw [heq] at hmom
  have hcross := (Complex.continuous_re.tendsto (Q : ℂ)).comp hmom
  have hgram := (Complex.continuous_re.tendsto (Q : ℂ)).comp
    (tendsto_quantizationGaussianGram S c (fun n => Real.log (n : ℝ)) hω)
  have ht := (hcross.const_mul 2).sub hgram
  have hlim : Tendsto (fun T : ℝ =>
      2 * (∑ n ∈ S, conj (c n) * quantizationCenteredGaussianMoment hW T (Real.log (n : ℝ))).re -
        (quantizationGaussianGram S c (fun n => Real.log (n : ℝ)) T).re)
      atTop (𝓝 Q) := by
    simpa only [Function.comp_def, Complex.ofReal_re, two_mul, add_sub_cancel_right] using ht
  have hQ : Q = ∑ n ∈ S, ‖quantizationCenteredCoeff hW n‖ ^ 2 / n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [c]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  filter_upwards [hlim.eventually (lt_mem_nhds (show Q - ε < Q by linarith)),
    eventually_gt_atTop (0 : ℝ)] with T hT hT0
  rw [← hQ]
  exact hT.le.trans (quantizationCenteredGaussianEnergy_variational hW S c _ hT0)

end RHTower.WeilSpectral
