import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanTypeI

/-!
# An independent arithmetic bound for complete Gaussian prime blocks

Vaughan's identity combines two curvature-controlled type-I terms with
Gaussian bilinear correlations. All coefficients and divisor cutoffs remain
explicit. No assertion about zeta zeros enters the bound.
-/

open Complex Finset RHTower RHTower.Sieve ArithmeticFunction

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The two type-I contributions, retaining the exact truncated coefficients. -/
def gaussianVaughanTypeIBound (σ α ξ t : ℝ) (A B L U V : ℕ) : ℝ :=
  (∑ b ∈ Icc 1 L,
    ‖(((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ)‖ *
      gaussianTypeIFibreBound σ α ξ t A B b) +
  ∑ b ∈ Icc 1 L, ‖((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ)‖ *
    (2 * gaussianTypeIFibreBound σ α ξ t A B b * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ))

/-- The type-II energy retains the Gaussian pair damping and the exact intersection
of both divisor fibres. -/
def gaussianVaughanTypeIIEnergy (σ α ξ : ℝ) (A B L U V : ℕ) : ℝ :=
  (∑ d ∈ Icc 1 L, ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
    ∑ m₁ ∈ Icc 1 L, ∑ m₂ ∈ Icc 1 L,
      ‖((typeIIShort V m₁ : ℝ) : ℂ) * (((m₁ : ℝ) ^ (-σ) : ℝ) : ℂ)‖ *
      ‖((typeIIShort V m₂ : ℝ) : ℂ) * (((m₂ : ℝ) ^ (-σ) : ℝ) : ℂ)‖ *
      gaussianBlockPairBound α ξ A B 1 (L + 1) m₁ m₂

private theorem norm_gaussian_zeta_conv_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {A B L : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBL : B - 1 ≤ L)
    (c : ArithmeticFunction ℝ) :
    ‖∑ n ∈ Ico A B, ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ) *
      gaussianPrimeWeight σ α ξ t n‖ ≤
        ∑ b ∈ Icc 1 L, ‖((c b : ℝ) : ℂ)‖ * gaussianTypeIFibreBound σ α ξ t A B b := by
  simp_rw [coe_zeta_mul_apply']
  rw [sum_conv_mul_Ico_eq hA (hA.trans hAB) hBL (fun _ => (1 : ℂ))
    (fun b => ((c b : ℝ) : ℂ)) (gaussianPrimeWeight σ α ξ t)]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b hb
  rw [norm_mul]
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_sum_gaussianPrimeWeight_fibre_le hσ hα hξ ht hAB (mem_Icc.mp hb).1

private theorem norm_gaussian_log_conv_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {A B L : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBL : B - 1 ≤ L)
    (c : ArithmeticFunction ℝ) :
    ‖∑ n ∈ Ico A B, (((ArithmeticFunction.log * c) n : ℝ) : ℂ) *
      gaussianPrimeWeight σ α ξ t n‖ ≤
        ∑ b ∈ Icc 1 L, ‖((c b : ℝ) : ℂ)‖ *
          (2 * gaussianTypeIFibreBound σ α ξ t A B b *
            Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ)) := by
  simp_rw [coe_log_mul_apply']
  rw [sum_conv_mul_Ico_eq hA (hA.trans hAB) hBL (fun a => (Real.log a : ℂ))
    (fun b => ((c b : ℝ) : ℂ)) (gaussianPrimeWeight σ α ξ t)]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro b hb
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_sum_log_gaussianPrimeWeight_fibre_le hσ hα hξ ht hAB (mem_Icc.mp hb).1

/-- A complete von Mangoldt block has an independent arithmetic bound,
with both type-I terms and the actual type-II coefficients. -/
theorem norm_gaussian_vonMangoldt_block_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hξ : 0 ≤ ξ) (ht : 0 < t)
    {A B L U V : ℕ} (hUA : U < A) (hAB : A ≤ B) (hBL : B - 1 ≤ L) :
    ‖∑ n ∈ Ico A B, ((vonMangoldt n : ℝ) : ℂ) * gaussianPrimeWeight σ α ξ t n‖ ≤
      gaussianVaughanTypeIBound σ α ξ t A B L U V +
        Real.sqrt (gaussianVaughanTypeIIEnergy σ α ξ A B L U V) := by
  have hA : 1 ≤ A := by omega
  have h₁ := norm_gaussian_zeta_conv_le hσ hα hξ ht hA hAB hBL
    (truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V)
  have h₂ := norm_gaussian_log_conv_le hσ hα hξ ht hA hAB hBL
    (truncAF (moebius : ArithmeticFunction ℝ) V)
  have h₃ := norm_gaussianVaughan_typeII_sq_le hα σ ξ t hA (hA.trans hAB) hBL U V
  have h₃' : ‖∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
      gaussianPrimeWeight σ α ξ t n‖ ≤
        Real.sqrt (gaussianVaughanTypeIIEnergy σ α ξ A B L U V) := by
    exact Real.le_sqrt_of_sq_le h₃
  rw [sum_vonMangoldt_block_decomp (V := V) hUA]
  refine (norm_add_le _ _).trans ?_
  refine (_root_.add_le_add (norm_add_le (_ : ℂ) _) le_rfl).trans ?_
  simp only [norm_neg]
  unfold gaussianVaughanTypeIBound
  rw [← mul_assoc] at h₁
  exact add_le_add (add_le_add h₁ h₂) h₃'

/-- The arithmetic estimate applies to the literal complex Gaussian Dirichlet
weight throughout the lower right damping quadrant. -/
theorem norm_complexGaussian_vonMangoldt_block_le {σ t : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hεre : 0 ≤ ε.re) (hεim : ε.im ≤ 0) (ht : 0 < t)
    {A B L U V : ℕ} (hUA : U < A) (hAB : A ≤ B) (hBL : B - 1 ≤ L) :
    ‖∑ n ∈ Ico A B, ((vonMangoldt n : ℝ) : ℂ) *
      ((n : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.exp (-(ε * (n : ℂ) ^ 2)))‖ ≤
        gaussianVaughanTypeIBound σ ε.re (-ε.im) t A B L U V +
          Real.sqrt (gaussianVaughanTypeIIEnergy σ ε.re (-ε.im) A B L U V) := by
  have hε : (ε.re : ℂ) - (-ε.im : ℝ) * I = ε := by
    apply Complex.ext <;> simp
  have hb := norm_gaussian_vonMangoldt_block_le (V := V) hσ hεre (neg_nonneg.mpr hεim) ht hUA hAB hBL
  have hs : (∑ n ∈ Ico A B, ((vonMangoldt n : ℝ) : ℂ) *
      gaussianPrimeWeight σ ε.re (-ε.im) t n) =
      ∑ n ∈ Ico A B, ((vonMangoldt n : ℝ) : ℂ) *
        ((n : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.exp (-(ε * (n : ℂ) ^ 2))) := by
    apply sum_congr rfl
    intro n hn
    rw [gaussianPrimeWeight_eq σ ε.re (-ε.im) t (by have := (mem_Ico.mp hn).1; omega), hε]
  rw [hs] at hb
  exact hb

/-- Every lower-half interior rotation has the complete arithmetic block bound. -/
theorem norm_rotatedGaussian_vonMangoldt_block_le {y φ σ t : ℝ}
    (hy : 0 < y) (hφ : |φ| < Real.pi / 2) (hφ0 : φ ≤ 0)
    (hσ : 0 ≤ σ) (ht : 0 < t) {A B L U V : ℕ}
    (hUA : U < A) (hAB : A ≤ B) (hBL : B - 1 ≤ L) :
    let ε := complexGaussianDamping y φ
    ‖∑ n ∈ Ico A B, ((vonMangoldt n : ℝ) : ℂ) *
      ((n : ℂ) ^ (-((σ : ℂ) + t * I)) * Complex.exp (-(ε * (n : ℂ) ^ 2)))‖ ≤
        gaussianVaughanTypeIBound σ ε.re (-ε.im) t A B L U V +
          Real.sqrt (gaussianVaughanTypeIIEnergy σ ε.re (-ε.im) A B L U V) := by
  have him : (complexGaussianDamping y φ).im ≤ 0 := by
    rw [complexGaussianDamping, Complex.exp_im]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le hφ0 (by
        have hh := (abs_lt.mp hφ).1
        linarith only [hh, Real.pi_pos]))
  exact norm_complexGaussian_vonMangoldt_block_le hσ
    (complexGaussianDamping_re_pos hy hφ).le him ht hUA hAB hBL

#print axioms norm_rotatedGaussian_vonMangoldt_block_le
#print axioms norm_gaussian_vonMangoldt_block_le
#print axioms norm_complexGaussian_vonMangoldt_block_le

end GaloisForLFunctions.ExceptionalLayerTheory
