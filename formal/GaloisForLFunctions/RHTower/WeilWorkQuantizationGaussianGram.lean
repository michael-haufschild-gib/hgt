import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianPhase
import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianFourier

/-!
# Exact finite Gaussian Gram matrices

Finite exponential polynomials have an explicit, absolutely integrable
Gaussian square. Its normalized Gram matrix converges to the coefficient
square sum at distinct frequencies. No infinite boundary expansion or
interchange of a moving truncation with a limit is used.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral

def quantizationGaussianCharacter (ℓ t : ℝ) : ℂ := Complex.exp (ℓ * ((t : ℂ) * I))

@[simp] theorem norm_quantizationGaussianCharacter (ℓ t : ℝ) :
    ‖quantizationGaussianCharacter ℓ t‖ = 1 := by
  simp [quantizationGaussianCharacter, Complex.norm_exp]

theorem quantizationGaussianCharacter_conj (ℓ t : ℝ) :
    conj (quantizationGaussianCharacter ℓ t) = quantizationGaussianCharacter (-ℓ) t := by
  rw [quantizationGaussianCharacter, ← Complex.exp_conj, quantizationGaussianCharacter]
  congr 1
  simp

theorem quantizationGaussianCharacter_mul (ℓ k t : ℝ) :
    quantizationGaussianCharacter ℓ t * quantizationGaussianCharacter k t =
      quantizationGaussianCharacter (ℓ + k) t := by
  unfold quantizationGaussianCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem character_gaussian_quadratic (T ℓ t : ℝ) :
    quantizationGaussianCharacter ℓ t * (quantizationGaussianWeight T t : ℂ) =
      Complex.exp (-(1 / (T : ℂ) ^ 2) * t ^ 2 + ((ℓ : ℂ) * I) * t + 0) := by
  unfold quantizationGaussianCharacter quantizationGaussianWeight
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_quantizationGaussianCharacter {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    Integrable (fun t : ℝ => quantizationGaussianCharacter ℓ t * quantizationGaussianWeight T t) := by
  have hb : 0 < (1 / (T : ℂ) ^ 2).re := by
    have he : (1 / (T : ℂ) ^ 2).re = 1 / T ^ 2 := by norm_cast
    rw [he]
    positivity
  simpa only [character_gaussian_quadratic] using
    integrable_cexp_quadratic hb ((ℓ : ℂ) * I) 0

theorem integral_quantizationGaussianCharacter {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    (∫ t : ℝ, quantizationGaussianCharacter ℓ t * quantizationGaussianWeight T t) =
      ((T * Real.sqrt Real.pi : ℝ) : ℂ) * (Real.exp (-((T * ℓ) ^ 2 / 4)) : ℂ) := by
  have hTc : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
  have hb : (-(1 / (T : ℂ) ^ 2)).re < 0 := by
    have he : (-(1 / (T : ℂ) ^ 2)).re = -(1 / T ^ 2) := by norm_cast
    rw [he]
    exact neg_lt_zero.mpr (by positivity)
  simp_rw [character_gaussian_quadratic]
  rw [integral_cexp_quadratic hb]
  have hbase : (Real.pi : ℂ) / -(-(1 / (T : ℂ) ^ 2)) = ((Real.pi * T ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hsqrt : (((Real.pi * T ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      ((T * Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hT.le]
    push_cast
    ring
  rw [hbase, hsqrt, Complex.ofReal_exp]
  congr 2
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

def quantizationGaussianPolynomial (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, c n * conj (quantizationGaussianCharacter (ω n) t)

def quantizationGaussianGram (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (T : ℝ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S, c n * conj (c m) *
    (Real.exp (-((T * (ω m - ω n)) ^ 2 / 4)) : ℂ)

theorem norm_quantizationGaussianPolynomial_le (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (t : ℝ) :
    ‖quantizationGaussianPolynomial S c ω t‖ ≤ ∑ n ∈ S, ‖c n‖ := by
  calc
    _ ≤ ∑ n ∈ S, ‖c n * conj (quantizationGaussianCharacter (ω n) t)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_conj, norm_quantizationGaussianCharacter, mul_one]

theorem integrable_quantizationGaussianPolynomial_square (S : Finset ℕ) (c : ℕ → ℂ)
    (ω : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => ‖quantizationGaussianPolynomial S c ω t‖ ^ 2 *
      quantizationGaussianWeight T t) := by
  have hg : Integrable (quantizationGaussianWeight T) :=
    integrable_exp_neg_mul_sq (by positivity : 0 < 1 / T ^ 2)
  refine (hg.const_mul ((∑ n ∈ S, ‖c n‖) ^ 2)).mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hp : Continuous (fun t : ℝ => ‖quantizationGaussianPolynomial S c ω t‖ ^ 2 *
        quantizationGaussianWeight T t) := by
      unfold quantizationGaussianPolynomial quantizationGaussianCharacter quantizationGaussianWeight
      fun_prop
    exact hp.aestronglyMeasurable
  · have hg0 : 0 ≤ quantizationGaussianWeight T t := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hg0)]
    apply mul_le_mul_of_nonneg_right _ hg0
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_quantizationGaussianPolynomial_le S c ω t) 2

private theorem polynomial_square_expansion (S : Finset ℕ) (c : ℕ → ℂ)
    (ω : ℕ → ℝ) (T t : ℝ) :
    ((‖quantizationGaussianPolynomial S c ω t‖ ^ 2 * quantizationGaussianWeight T t : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, (c n * conj (c m)) *
        (quantizationGaussianCharacter (ω m - ω n) t * quantizationGaussianWeight T t) := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold quantizationGaussianPolynomial
  simp only [map_sum, map_mul, conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [quantizationGaussianCharacter_conj]
  have he := quantizationGaussianCharacter_mul (-ω n) (ω m) t
  rw [show -ω n + ω m = ω m - ω n by ring] at he
  calc
    _ = (c n * conj (c m)) *
        ((quantizationGaussianCharacter (-ω n) t * quantizationGaussianCharacter (ω m) t) *
          quantizationGaussianWeight T t) := by ring
    _ = _ := by rw [he]

theorem integral_quantizationGaussianPolynomial_square (S : Finset ℕ) (c : ℕ → ℂ)
    (ω : ℕ → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, ‖quantizationGaussianPolynomial S c ω t‖ ^ 2 * quantizationGaussianWeight T t) =
      T * Real.sqrt Real.pi * (quantizationGaussianGram S c ω T).re := by
  have hi (n m : ℕ) : Integrable (fun t : ℝ => (c n * conj (c m)) *
      (quantizationGaussianCharacter (ω m - ω n) t * quantizationGaussianWeight T t)) :=
    (integrable_quantizationGaussianCharacter hT _).const_mul _
  have hc : ((∫ t : ℝ, ‖quantizationGaussianPolynomial S c ω t‖ ^ 2 *
      quantizationGaussianWeight T t : ℝ) : ℂ) =
      ((T * Real.sqrt Real.pi : ℝ) : ℂ) * quantizationGaussianGram S c ω T := by
    rw [← integral_complex_ofReal]
    simp_rw [polynomial_square_expansion]
    rw [integral_finsetSum S (fun n _ => integrable_finsetSum S (fun m _ => hi n m))]
    simp_rw [integral_finsetSum S (fun m _ => hi _ m), integral_const_mul,
      integral_quantizationGaussianCharacter hT]
    unfold quantizationGaussianGram
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

theorem tendsto_quantizationGaussianKernel {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun T : ℝ => Real.exp (-((T * x) ^ 2 / 4))) atTop (𝓝 0) := by
  have hq : Tendsto (fun T : ℝ => (x ^ 2 / 4) * T ^ 2) atTop atTop :=
    tendsto_const_mul_pow_atTop (by decide) (by positivity)
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hq using 1
  ext T
  congr 1
  dsimp only [Function.comp_def]
  ring

theorem tendsto_quantizationGaussianGram (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ)
    (hω : Set.InjOn ω S) :
    Tendsto (quantizationGaussianGram S c ω) atTop
      (𝓝 ((∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ)) := by
  have hh (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm : m ∈ S) :
      Tendsto (fun T : ℝ => c n * conj (c m) *
        (Real.exp (-((T * (ω m - ω n)) ^ 2 / 4)) : ℂ)) atTop
        (𝓝 (if m = n then (‖c n‖ ^ 2 : ℂ) else 0)) := by
    by_cases hmn : m = n
    · subst m
      simpa only [sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, neg_zero,
        Real.exp_zero, ofReal_one, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        if_true, Complex.ofReal_pow] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => ((‖c n‖ ^ 2 : ℝ) : ℂ)) atTop _)
    have hd : ω m - ω n ≠ 0 := fun he => hmn (hω hm hn (sub_eq_zero.mp he))
    have hz := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_quantizationGaussianKernel hd)
    simpa only [if_neg hmn, Function.comp_def, ofReal_zero, mul_zero] using
      hz.const_mul (c n * conj (c m))
  have ht := tendsto_finsetSum S fun n hn => tendsto_finsetSum S fun m hm => hh n hn m hm
  unfold quantizationGaussianGram
  simpa using ht

end RHTower.WeilSpectral
