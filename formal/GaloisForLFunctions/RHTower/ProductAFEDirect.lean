import GaloisForLFunctions.RHTower.ProductAFEContour
import GaloisForLFunctions.RHTower.SmoothAFEZetaDirichletExpansion

/-!
# The right edge of the product AFE: a double Dirichlet series

On a positive vertical line `Re w = c` with `1 < Re s₁ + c` and `1 < Re s₂ + c`, both zeta
factors of the product integrand are absolutely convergent Dirichlet series, so the integrand is
the double series of terms `(m+1)^{-s₁-w} (n+1)^{-s₂-w} x^w e^{w²}/w`.  Each term is
`(m+1)^{-s₁} (n+1)^{-s₂}` times the Gaussian inverse-Mellin integrand at `(m+1)(n+1)/x`, and the
double series may be integrated termwise by an explicit product majorant.  The normalized
right-edge integral is therefore

  `Σ'_{m,n} (m+1)^{-s₁} (n+1)^{-s₂} · V((m+1)(n+1)/x)`

with `V` the canonical Gaussian smooth cutoff.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

/-- One term of the double Dirichlet expansion of the product integrand. -/
def productAFEMellinTerm (s₁ s₂ : ℂ) (x : ℝ) (p : ℕ × ℕ) (w : ℂ) : ℂ :=
  smoothAFEZetaMellinTerm s₁ x p.1 w * (1 / (p.2 + 1 : ℂ) ^ (s₂ + w))

theorem norm_one_div_nat_succ_cpow (n : ℕ) (s : ℂ) :
    ‖(1 : ℂ) / (n + 1 : ℂ) ^ s‖ = 1 / (n + 1 : ℝ) ^ s.re := by
  rw [norm_div, norm_one, show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.succ_pos n)]

theorem summable_norm_one_div_nat_succ_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(1 : ℂ) / (n + 1 : ℂ) ^ s‖ := by
  have hsum0 := Complex.summable_one_div_nat_cpow.mpr hs
  have hsum := (summable_nat_add_iff 1).2 hsum0
  have hsum' : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hsum
  exact hsum'.norm

theorem summable_norm_smoothAFEZetaMellinTerm_vertical {s : ℂ} {x c : ℝ} (hx : 0 < x)
    (hc : 0 < c) (hsc : 1 < s.re + c) (t : ℝ) :
    Summable fun m : ℕ => ‖smoothAFEZetaMellinTerm s x m ((c : ℂ) + (t : ℂ) * I)‖ := by
  have hmaj : Summable (fun m : ℕ =>
      (1 / (m + 1 : ℝ) ^ (s.re + c)) * (x ^ c * (Real.exp (c ^ 2) / c) * Real.exp (-(t ^ 2)))) :=
    (summable_smoothAFEZetaMajorant hsc).mul_right _
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
  refine (norm_smoothAFEZetaMellinTerm_vertical_le hx hc m t).trans (le_of_eq ?_)
  ring

/-- The product integrand on a positive line is the double series of its terms. -/
theorem productAFEIntegrand_eq_tsum {s₁ s₂ : ℂ} {x c t : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc₁ : 1 < s₁.re + c) (hsc₂ : 1 < s₂.re + c) :
    productAFEIntegrand s₁ s₂ x ((c : ℂ) + (t : ℂ) * I)
      = ∑' p : ℕ × ℕ, productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I) := by
  have hre₂ : 1 < (s₂ + ((c : ℂ) + (t : ℂ) * I)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hF : productAFEIntegrand s₁ s₂ x ((c : ℂ) + (t : ℂ) * I)
      = smoothAFEZetaMellinIntegrand s₁ x ((c : ℂ) + (t : ℂ) * I)
        * riemannZeta (s₂ + ((c : ℂ) + (t : ℂ) * I)) := by
    rw [productAFEIntegrand_eq_mul]
    ring
  rw [hF, smoothAFEZetaMellinIntegrand_eq_tsum hsc₁, zeta_eq_tsum_one_div_nat_add_one_cpow hre₂,
    tsum_mul_tsum_of_summable_norm
      (summable_norm_smoothAFEZetaMellinTerm_vertical hx hc hsc₁ t)
      (summable_norm_one_div_nat_succ_cpow hre₂)]
  rfl

theorem norm_productAFEMellinTerm_vertical_le {s₁ s₂ : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (p : ℕ × ℕ) (t : ℝ) :
    ‖productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I)‖
      ≤ ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))
          * (x ^ c * (Real.exp (c ^ 2) / c))) * Real.exp (-(t ^ 2)) := by
  rw [productAFEMellinTerm, norm_mul, norm_one_div_nat_succ_cpow]
  have hre : (s₂ + ((c : ℂ) + (t : ℂ) * I)).re = s₂.re + c := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [hre]
  have h1 := norm_smoothAFEZetaMellinTerm_vertical_le (s := s₁) hx hc p.1 t
  calc ‖smoothAFEZetaMellinTerm s₁ x p.1 ((c : ℂ) + (t : ℂ) * I)‖
        * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))
      ≤ ((((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * x ^ c) * (Real.exp (c ^ 2) / c))
          * Real.exp (-(t ^ 2))) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := by ring

theorem continuous_one_div_nat_succ_cpow_vertical (n : ℕ) (s : ℂ) (c : ℝ) :
    Continuous fun t : ℝ => (1 : ℂ) / (n + 1 : ℂ) ^ (s + ((c : ℂ) + (t : ℂ) * I)) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine continuous_const.div (Continuous.cpow continuous_const (by fun_prop) ?_) ?_
  · intro t
    left
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  · intro t
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn)

theorem productAFEMellinTerm_verticalIntegrable {s₁ s₂ : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (p : ℕ × ℕ) :
    Integrable (fun t : ℝ => productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I)) := by
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))
        * (x ^ c * (Real.exp (c ^ 2) / c))))
  · exact ((smoothAFEZetaMellinTerm_verticalIntegrable (s := s₁) hx hc p.1).aestronglyMeasurable.mul
      (continuous_one_div_nat_succ_cpow_vertical p.2 s₂ c).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun t => by
      simpa using norm_productAFEMellinTerm_vertical_le hx hc p t

theorem summable_integral_norm_productAFEMellinTerm {s₁ s₂ : ℂ} {x c : ℝ} (hx : 0 < x)
    (hc : 0 < c) (hsc₁ : 1 < s₁.re + c) (hsc₂ : 1 < s₂.re + c) :
    Summable (fun p : ℕ × ℕ => ∫ t : ℝ,
      ‖productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I)‖) := by
  let D : ℝ := x ^ c * (Real.exp (c ^ 2) / c) * ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hbase : Summable (fun p : ℕ × ℕ =>
      (1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))) :=
    (summable_smoothAFEZetaMajorant hsc₁).mul_of_nonneg (summable_smoothAFEZetaMajorant hsc₂)
      (fun n => by positivity) (fun n => by positivity)
  have hmajor : Summable (fun p : ℕ × ℕ =>
      ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))) * D) :=
    hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun p => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_) hmajor
  have hterm := productAFEMellinTerm_verticalIntegrable (s₁ := s₁) (s₂ := s₂) hx hc p
  have hgauss := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hdom : Integrable (fun t : ℝ =>
      ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))
        * (x ^ c * (Real.exp (c ^ 2) / c))) * Real.exp (-(t ^ 2))) := by
    simpa using hgauss.const_mul
      ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))
        * (x ^ c * (Real.exp (c ^ 2) / c)))
  calc ∫ t : ℝ, ‖productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))
          * (x ^ c * (Real.exp (c ^ 2) / c))) * Real.exp (-(t ^ 2)) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun t => norm_productAFEMellinTerm_vertical_le hx hc p t
    _ = ((1 / (p.1 + 1 : ℝ) ^ (s₁.re + c)) * (1 / (p.2 + 1 : ℝ) ^ (s₂.re + c))) * D := by
      rw [MeasureTheory.integral_const_mul]
      dsimp [D]
      ring

theorem integral_productAFEIntegrand_eq_tsum {s₁ s₂ : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc₁ : 1 < s₁.re + c) (hsc₂ : 1 < s₂.re + c) :
    (∫ t : ℝ, productAFEIntegrand s₁ s₂ x ((c : ℂ) + (t : ℂ) * I))
      = ∑' p : ℕ × ℕ, ∫ t : ℝ, productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I) := by
  calc (∫ t : ℝ, productAFEIntegrand s₁ s₂ x ((c : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ, ∑' p : ℕ × ℕ, productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => productAFEIntegrand_eq_tsum hx hc hsc₁ hsc₂
    _ = ∑' p : ℕ × ℕ, ∫ t : ℝ, productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I) := by
        symm
        apply MeasureTheory.integral_tsum_of_summable_integral_norm
        · exact fun p => productAFEMellinTerm_verticalIntegrable hx hc p
        · exact summable_integral_norm_productAFEMellinTerm hx hc hsc₁ hsc₂

/-- Each term is a monomial times the Gaussian inverse-Mellin integrand at `(m+1)(n+1)/x`. -/
theorem productAFEMellinTerm_eq_cpow_mul_cutoffIntegrand {x : ℝ} (hx : 0 < x) (s₁ s₂ : ℂ)
    (p : ℕ × ℕ) (w : ℂ) :
    productAFEMellinTerm s₁ s₂ x p w =
      (p.1 + 1 : ℂ) ^ (-s₁) * (p.2 + 1 : ℂ) ^ (-s₂) *
        smoothAFEMellinIntegrand (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / x) w := by
  have hn : (p.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p.2
  have hm : (0 : ℝ) < p.1 + 1 := by exact_mod_cast Nat.succ_pos p.1
  have hn' : (0 : ℝ) ≤ p.2 + 1 := by exact_mod_cast Nat.zero_le (p.2 + 1)
  rw [productAFEMellinTerm, smoothAFEZetaMellinTerm_eq_cpow_mul_cutoffIntegrand hx s₁ p.1 w,
    one_div, ← Complex.cpow_neg, show -(s₂ + w) = -s₂ + -w by ring, Complex.cpow_add _ _ hn,
    smoothAFEMellinIntegrand, smoothAFEMellinIntegrand]
  have hmul : (((p.1 + 1 : ℝ) / x : ℝ) : ℂ) ^ (-w) * (p.2 + 1 : ℂ) ^ (-w)
      = ((((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / x : ℝ) : ℂ) ^ (-w) := by
    rw [show (p.2 + 1 : ℂ) = ((p.2 + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg (div_pos hm hx).le hn' (-w)]
    congr 2
    push_cast
    ring
  calc (p.1 + 1 : ℂ) ^ (-s₁) * ((((p.1 + 1 : ℝ) / x : ℝ) : ℂ) ^ (-w) * smoothAFEGaussianKernel w)
        * ((p.2 + 1 : ℂ) ^ (-s₂) * (p.2 + 1 : ℂ) ^ (-w))
      = (p.1 + 1 : ℂ) ^ (-s₁) * (p.2 + 1 : ℂ) ^ (-s₂)
        * ((((p.1 + 1 : ℝ) / x : ℝ) : ℂ) ^ (-w) * (p.2 + 1 : ℂ) ^ (-w))
        * smoothAFEGaussianKernel w := by ring
    _ = _ := by rw [hmul]; ring

theorem integral_productAFEMellinTerm_eq_cpow_mul_cutoffIntegral {x c : ℝ} (hx : 0 < x)
    (s₁ s₂ : ℂ) (p : ℕ × ℕ) :
    (∫ t : ℝ, productAFEMellinTerm s₁ s₂ x p ((c : ℂ) + (t : ℂ) * I))
      = (p.1 + 1 : ℂ) ^ (-s₁) * (p.2 + 1 : ℂ) ^ (-s₂) * ∫ t : ℝ,
          smoothAFEMellinIntegrand (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / x) ((c : ℂ) + (t : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    productAFEMellinTerm_eq_cpow_mul_cutoffIntegrand hx s₁ s₂ p _

/-- Normalized product Gaussian Mellin integral on the line `Re w = c`. -/
def productAFEMellinAt (c : ℝ) (s₁ s₂ : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ t : ℝ, productAFEIntegrand s₁ s₂ x ((c : ℂ) + (t : ℂ) * I)

theorem productAFEMellinAt_eq_tsum_cutoffAt {s₁ s₂ : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc₁ : 1 < s₁.re + c) (hsc₂ : 1 < s₂.re + c) :
    productAFEMellinAt c s₁ s₂ x =
      ∑' p : ℕ × ℕ, (p.1 + 1 : ℂ) ^ (-s₁) * (p.2 + 1 : ℂ) ^ (-s₂) *
        smoothAFECutoffAt c (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / x) := by
  unfold productAFEMellinAt
  rw [integral_productAFEIntegrand_eq_tsum hx hc hsc₁ hsc₂, Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [integral_productAFEMellinTerm_eq_cpow_mul_cutoffIntegral hx, smoothAFECutoffAt_eq_integral,
    Complex.real_smul]
  ring

/-- **The right edge of the product AFE is the double smoothed Dirichlet series.** -/
theorem productAFEMellinAt_eq_tsum_smoothAFECutoff {s₁ s₂ : ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hsc₁ : 1 < s₁.re + c) (hsc₂ : 1 < s₂.re + c) :
    productAFEMellinAt c s₁ s₂ x =
      ∑' p : ℕ × ℕ, (p.1 + 1 : ℂ) ^ (-s₁) * (p.2 + 1 : ℂ) ^ (-s₂) *
        smoothAFECutoff (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / x) := by
  rw [productAFEMellinAt_eq_tsum_cutoffAt hx hc hsc₁ hsc₂]
  apply tsum_congr
  intro p
  have hm : (0 : ℝ) < p.1 + 1 := by exact_mod_cast Nat.succ_pos p.1
  have hn : (0 : ℝ) < p.2 + 1 := by exact_mod_cast Nat.succ_pos p.2
  rw [smoothAFECutoffAt_eq_smoothAFECutoff (div_pos (mul_pos hm hn) hx) hc]

end RHTower

end
