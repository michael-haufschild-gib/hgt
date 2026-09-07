import GaloisForLFunctions.RHTower.ProductAFEDirect
import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralDualExpansion

/-!
# The left edge of the product AFE: the reflected double series

On the line `Re w = -1` with `0 < Re s_i < 1`, both zeta factors satisfy the functional equation
`ζ(s_i+w) = χ(s_i+w) ζ(1-s_i-w)` with `Re (1-s_i-w) > 1`, so the product integrand is the
double series of reflected terms

`χ(s₁+w) (m+1)^{s₁-1+w} · χ(s₂+w) (n+1)^{s₂-1+w} · x^w e^{w²}/w`.

Each term factors as `χ(s₁)χ(s₂)(m+1)^{s₁-1}(n+1)^{s₂-1}` times the two-ratio dual integrand at the
reciprocal scale `1/((m+1)(n+1)x)`, and the double series integrates termwise by an explicit
product majorant.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

/-- One reflected term of the product integrand on the left line. -/
def productAFEReflectedTerm (s₁ s₂ : ℂ) (x : ℝ) (p : ℕ × ℕ) (w : ℂ) : ℂ :=
  smoothAFEZetaReflectedTerm s₁ x p.1 w *
    (zetaChi (s₂ + w) * (1 / (p.2 + 1 : ℂ) ^ (1 - (s₂ + w))))

/-- The two-ratio dual integrand `[χ(s₁+w)/χ(s₁)] [χ(s₂+w)/χ(s₂)] y^{-w} e^{w²}/w`. -/
def productAFEDualRatioIntegrand (s₁ s₂ : ℂ) (y : ℝ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio s₁ w * smoothAFEZetaChiShiftRatio s₂ w *
    smoothAFEMellinIntegrand y w

/-- The exact two-ratio dual cutoff on the left line. -/
def productAFEDualCutoff (s₁ s₂ : ℂ) (y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    productAFEDualRatioIntegrand s₁ s₂ y (((-1 : ℝ) : ℂ) + (v : ℂ) * I)

/-- The normalized left-edge integral of the product integrand. -/
def productAFEDualMellinAt (s₁ s₂ : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    productAFEIntegrand s₁ s₂ x (((-1 : ℝ) : ℂ) + (v : ℂ) * I)

/-! ## Expansion on the left line -/

theorem left_one_re (s : ℂ) (v : ℝ) : (s + ((-1 : ℂ) + (v : ℂ) * I)).re = s.re - 1 := by
  simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
  ring

theorem riemannZeta_left_one_eq_chi_mul_tsum {s : ℂ} (h1 : s.re < 1) (v : ℝ) :
    riemannZeta (s + ((-1 : ℂ) + (v : ℂ) * I)) =
      zetaChi (s + ((-1 : ℂ) + (v : ℂ) * I)) *
        ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (1 - (s + ((-1 : ℂ) + (v : ℂ) * I))) := by
  set w : ℂ := (-1 : ℂ) + (v : ℂ) * I with hw
  have hre : (s + w).re = s.re - 1 := left_one_re s v
  have h0 : s + w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    linarith
  have h1' : s + w ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    linarith
  have hG : Gammaℝ (1 - (s + w)) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re, hre]
    linarith
  have hre2 : 1 < (1 - (s + w)).re := by
    simp only [Complex.sub_re, Complex.one_re, hre]
    linarith
  rw [zeta_eq_zetaChi_mul h0 h1' hG, zeta_eq_tsum_one_div_nat_add_one_cpow hre2]

theorem summable_norm_smoothAFEZetaReflectedTerm_left_one {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (v : ℝ) :
    Summable fun m : ℕ => ‖smoothAFEZetaReflectedTerm s x m ((-1 : ℂ) + (v : ℂ) * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_zetaChi_add_left_one_le h0 h1
  have h2 : 1 < 2 - s.re := by linarith
  have hmaj : Summable (fun m : ℕ => (1 / (m + 1 : ℝ) ^ (2 - s.re)) *
      (x⁻¹ * Real.exp 1 * C * ((1 + |s.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))))) :=
    (summable_smoothAFEZetaMajorant h2).mul_right _
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
  refine (norm_smoothAFEZetaReflectedTerm_general_left_one_le hx hC m v).trans (le_of_eq ?_)
  ring

/-- **The product integrand on the left line is the double reflected series.** -/
theorem productAFEIntegrand_eq_reflected_tsum_left_one {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂1 : s₂.re < 1) (v : ℝ) :
    productAFEIntegrand s₁ s₂ x ((-1 : ℂ) + (v : ℂ) * I) =
      ∑' p : ℕ × ℕ, productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I) := by
  have hre2 : 1 < (1 - (s₂ + ((-1 : ℂ) + (v : ℂ) * I))).re := by
    simp only [Complex.sub_re, Complex.one_re, left_one_re]
    linarith
  have hF : productAFEIntegrand s₁ s₂ x ((-1 : ℂ) + (v : ℂ) * I) =
      smoothAFEZetaMellinIntegrand s₁ x ((-1 : ℂ) + (v : ℂ) * I)
        * riemannZeta (s₂ + ((-1 : ℂ) + (v : ℂ) * I)) := by
    rw [productAFEIntegrand_eq_mul]
    ring
  have hg : Summable fun n : ℕ =>
      ‖zetaChi (s₂ + ((-1 : ℂ) + (v : ℂ) * I))
        * (1 / (n + 1 : ℂ) ^ (1 - (s₂ + ((-1 : ℂ) + (v : ℂ) * I))))‖ := by
    simpa [norm_mul] using
      (summable_norm_one_div_nat_succ_cpow hre2).mul_left
        ‖zetaChi (s₂ + ((-1 : ℂ) + (v : ℂ) * I))‖
  rw [hF, smoothAFEZetaMellinIntegrand_eq_reflected_tsum_left_one_of_re_lt_one h₁1,
    riemannZeta_left_one_eq_chi_mul_tsum h₂1 v, ← tsum_mul_left,
    tsum_mul_tsum_of_summable_norm
      (summable_norm_smoothAFEZetaReflectedTerm_left_one hx h₁0 h₁1 v) hg]
  rfl

/-! ## Termwise bounds, integrability, and summability -/

theorem norm_productAFEReflectedTerm_left_one_le {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    {C₁ C₂ : ℝ} (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ v : ℝ, ‖zetaChi (s₁ + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤ C₁ * (1 + |s₁.im| + |v|) ^ 2)
    (hC₂ : ∀ v : ℝ, ‖zetaChi (s₂ + ((-1 : ℂ) + (v : ℂ) * I))‖ ≤ C₂ * (1 + |s₂.im| + |v|) ^ 2)
    (p : ℕ × ℕ) (v : ℝ) :
    ‖productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I)‖ ≤
      (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
          * (x⁻¹ * Real.exp 1 * C₁ * C₂))
        * (((2 + |s₁.im| + |s₂.im|) + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  have h1 := norm_smoothAFEZetaReflectedTerm_general_left_one_le hx hC₁ p.1 v
  have hcpow : ‖(1 : ℂ) / (p.2 + 1 : ℂ) ^ (1 - (s₂ + ((-1 : ℂ) + (v : ℂ) * I)))‖
      = 1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re) := by
    rw [norm_one_div_nat_succ_cpow]
    congr 2
    simp only [Complex.sub_re, Complex.one_re, left_one_re]
    ring
  have h2 : ‖zetaChi (s₂ + ((-1 : ℂ) + (v : ℂ) * I))
      * (1 / (p.2 + 1 : ℂ) ^ (1 - (s₂ + ((-1 : ℂ) + (v : ℂ) * I))))‖
      ≤ C₂ * (1 + |s₂.im| + |v|) ^ 2 * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)) := by
    rw [norm_mul, hcpow]
    exact mul_le_mul_of_nonneg_right (hC₂ v) (by positivity)
  have hprod : (1 + |s₁.im| + |v|) ^ 2 * (1 + |s₂.im| + |v|) ^ 2
      ≤ ((2 + |s₁.im| + |s₂.im|) + |v|) ^ 4 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s₂.im]) 2)
      (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s₁.im]) 2)
      (by positivity) (by positivity)
  have hC₁0 : 0 ≤ C₁ := by
    have := hC₁ 0
    have hn : 0 ≤ ‖zetaChi (s₁ + ((-1 : ℂ) + ((0 : ℝ) : ℂ) * I))‖ := norm_nonneg _
    have hp : 0 < (1 + |s₁.im| + |(0 : ℝ)|) ^ 2 := by positivity
    nlinarith
  have hK : 0 ≤ ((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
      * (x⁻¹ * Real.exp 1 * C₁ * C₂) := by positivity
  rw [productAFEReflectedTerm, norm_mul]
  calc _
      ≤ (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * x⁻¹ * Real.exp 1 * C₁) *
          ((1 + |s₁.im| + |v|) ^ 2 * Real.exp (-(v ^ 2))))
        * (C₂ * (1 + |s₂.im| + |v|) ^ 2 * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
          * (x⁻¹ * Real.exp 1 * C₁ * C₂))
        * (((1 + |s₁.im| + |v|) ^ 2 * (1 + |s₂.im| + |v|) ^ 2) * Real.exp (-(v ^ 2))) := by
        ring
    _ ≤ _ :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) hK

theorem continuous_zetaChi_left_one {s : ℂ} (h1 : s.re < 1) :
    Continuous fun v : ℝ => zetaChi (s + ((-1 : ℂ) + (v : ℂ) * I)) := by
  refine continuous_iff_continuousAt.mpr fun v => ?_
  have hpath : ContinuousAt (fun u : ℝ => s + ((-1 : ℂ) + (u : ℂ) * I)) v := by fun_prop
  have hG : Gammaℝ (1 - (s + ((-1 : ℂ) + (v : ℂ) * I))) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re, left_one_re]
    linarith
  have hcomp : ContinuousAt (zetaChi ∘ fun u : ℝ => s + ((-1 : ℂ) + (u : ℂ) * I)) v :=
    ContinuousAt.comp (zetaChi_analyticAt hG).continuousAt hpath
  simpa [Function.comp_def] using hcomp

theorem continuous_one_div_nat_succ_cpow_left_one (n : ℕ) (s : ℂ) :
    Continuous fun v : ℝ => (1 : ℂ) / (n + 1 : ℂ) ^ (1 - (s + ((-1 : ℂ) + (v : ℂ) * I))) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine continuous_const.div (Continuous.cpow continuous_const (by fun_prop) ?_) ?_
  · intro v
    left
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  · intro v
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn)

theorem productAFEReflectedTerm_left_one_integrable {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) (p : ℕ × ℕ) :
    Integrable (fun v : ℝ => productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C₁, _, hC₁⟩ := norm_zetaChi_add_left_one_le h₁0 h₁1
  obtain ⟨C₂, hC₂0, hC₂⟩ := norm_zetaChi_add_left_one_le h₂0 h₂1
  apply Integrable.mono'
    ((integrable_shifted_pow_mul_exp_neg_sq (2 + |s₁.im| + |s₂.im|) 4).const_mul
      (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
        * (x⁻¹ * Real.exp 1 * C₁ * C₂)))
  · exact (smoothAFEZetaReflectedTerm_general_left_one_integrable hx h₁0 h₁1 p.1).aestronglyMeasurable.mul
      ((continuous_zetaChi_left_one h₂1).mul
        (continuous_one_div_nat_succ_cpow_left_one p.2 s₂)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun v => by
      simpa using norm_productAFEReflectedTerm_left_one_le hx hC₂0 hC₁ hC₂ p v

theorem summable_integral_norm_productAFEReflectedTerm_left_one {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) :
    Summable (fun p : ℕ × ℕ => ∫ v : ℝ,
      ‖productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I)‖) := by
  obtain ⟨C₁, _, hC₁⟩ := norm_zetaChi_add_left_one_le h₁0 h₁1
  obtain ⟨C₂, hC₂0, hC₂⟩ := norm_zetaChi_add_left_one_le h₂0 h₂1
  let D : ℝ := (x⁻¹ * Real.exp 1 * C₁ * C₂) *
    ∫ v : ℝ, ((2 + |s₁.im| + |s₂.im|) + |v|) ^ 4 * Real.exp (-(v ^ 2))
  have h₁2 : 1 < 2 - s₁.re := by linarith
  have h₂2 : 1 < 2 - s₂.re := by linarith
  have hbase : Summable (fun p : ℕ × ℕ =>
      (1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re))) :=
    (summable_smoothAFEZetaMajorant h₁2).mul_of_nonneg (summable_smoothAFEZetaMajorant h₂2)
      (fun n => by positivity) (fun n => by positivity)
  have hmajor : Summable (fun p : ℕ × ℕ =>
      ((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re))) * D) :=
    hbase.mul_right D
  refine Summable.of_nonneg_of_le
    (fun p => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_) hmajor
  have hterm := productAFEReflectedTerm_left_one_integrable hx h₁0 h₁1 h₂0 h₂1 p
  have hdom : Integrable (fun v : ℝ =>
      (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
          * (x⁻¹ * Real.exp 1 * C₁ * C₂))
        * (((2 + |s₁.im| + |s₂.im|) + |v|) ^ 4 * Real.exp (-(v ^ 2)))) := by
    simpa using (integrable_shifted_pow_mul_exp_neg_sq (2 + |s₁.im| + |s₂.im|) 4).const_mul
      (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
        * (x⁻¹ * Real.exp 1 * C₁ * C₂))
  calc ∫ v : ℝ, ‖productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v : ℝ, (((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re)))
          * (x⁻¹ * Real.exp 1 * C₁ * C₂))
        * (((2 + |s₁.im| + |s₂.im|) + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
        apply integral_mono_ae hterm.norm hdom
        exact Filter.Eventually.of_forall fun v =>
          norm_productAFEReflectedTerm_left_one_le hx hC₂0 hC₁ hC₂ p v
    _ = ((1 / (p.1 + 1 : ℝ) ^ (2 - s₁.re)) * (1 / (p.2 + 1 : ℝ) ^ (2 - s₂.re))) * D := by
      rw [MeasureTheory.integral_const_mul]
      dsimp [D]
      ring

theorem integral_productAFEIntegrand_left_one_eq_tsum {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) :
    (∫ v : ℝ, productAFEIntegrand s₁ s₂ x ((-1 : ℂ) + (v : ℂ) * I)) =
      ∑' p : ℕ × ℕ, ∫ v : ℝ, productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I) := by
  calc (∫ v : ℝ, productAFEIntegrand s₁ s₂ x ((-1 : ℂ) + (v : ℂ) * I))
      = ∫ v : ℝ, ∑' p : ℕ × ℕ, productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v =>
          productAFEIntegrand_eq_reflected_tsum_left_one hx h₁0 h₁1 h₂1 v
    _ = _ := by
        symm
        apply integral_tsum_of_summable_integral_norm
        · exact fun p => productAFEReflectedTerm_left_one_integrable hx h₁0 h₁1 h₂0 h₂1 p
        · exact summable_integral_norm_productAFEReflectedTerm_left_one hx h₁0 h₁1 h₂0 h₂1

/-! ## Factorization through the two-ratio dual integrand -/

theorem productAFEReflectedTerm_eq_dualRatio {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (hχ₁ : zetaChi s₁ ≠ 0) (hχ₂ : zetaChi s₂ ≠ 0) (p : ℕ × ℕ) (w : ℂ) :
    productAFEReflectedTerm s₁ s₂ x p w =
      (zetaChi s₁ * zetaChi s₂ * (p.1 + 1 : ℂ) ^ (s₁ - 1) * (p.2 + 1 : ℂ) ^ (s₂ - 1)) *
        productAFEDualRatioIntegrand s₁ s₂ (1 / ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x)) w := by
  have hn : (p.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p.2
  have hm0 : (0 : ℝ) < p.1 + 1 := by exact_mod_cast Nat.succ_pos p.1
  have hn0 : (0 : ℝ) < p.2 + 1 := by exact_mod_cast Nat.succ_pos p.2
  have hmx : (0 : ℝ) < (p.1 + 1 : ℝ) * x := mul_pos hm0 hx
  have hmnx : (0 : ℝ) < (p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x := by positivity
  -- the second factor
  have hsecond : zetaChi (s₂ + w) * (1 / (p.2 + 1 : ℂ) ^ (1 - (s₂ + w)))
      = zetaChi s₂ * (p.2 + 1 : ℂ) ^ (s₂ - 1) *
        (smoothAFEZetaChiShiftRatio s₂ w * (p.2 + 1 : ℂ) ^ w) := by
    rw [smoothAFEZetaChiShiftRatio, one_div, ← Complex.cpow_neg,
      show -(1 - (s₂ + w)) = (s₂ - 1) + w by ring, Complex.cpow_add _ _ hn]
    field_simp
  -- the scales
  have hrecip₁ : (((1 / ((p.1 + 1 : ℝ) * x) : ℝ) : ℂ) ^ (-w)) = (((p.1 + 1 : ℝ) * x : ℝ) : ℂ) ^ w := by
    simpa using cpow_div_pos_neg (a := 1) (b := (p.1 + 1 : ℝ) * x) zero_lt_one hmx w
  have hrecip₂ : (((1 / ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x) : ℝ) : ℂ) ^ (-w))
      = (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x : ℝ) : ℂ) ^ w := by
    simpa using cpow_div_pos_neg (a := 1) (b := (p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x)
      zero_lt_one hmnx w
  have hscale : (((p.1 + 1 : ℝ) * x : ℝ) : ℂ) ^ w * (p.2 + 1 : ℂ) ^ w
      = (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x : ℝ) : ℂ) ^ w := by
    rw [show (p.2 + 1 : ℂ) = ((p.2 + 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg hmx.le hn0.le w]
    congr 2
    push_cast
    ring
  rw [productAFEReflectedTerm, smoothAFEZetaReflectedTerm_eq_dualRatioTerm p.1 hχ₁,
    smoothAFEDualRatioTerm_eq_integrand hx, hsecond, smoothAFEDualRatioIntegrand,
    productAFEDualRatioIntegrand, smoothAFEMellinIntegrand, smoothAFEMellinIntegrand, hrecip₁,
    hrecip₂, ← hscale]
  ring

theorem integral_productAFEReflectedTerm_left_one_eq {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) (p : ℕ × ℕ) :
    (∫ v : ℝ, productAFEReflectedTerm s₁ s₂ x p ((-1 : ℂ) + (v : ℂ) * I)) =
      (zetaChi s₁ * zetaChi s₂ * (p.1 + 1 : ℂ) ^ (s₁ - 1) * (p.2 + 1 : ℂ) ^ (s₂ - 1)) *
        ∫ v : ℝ, productAFEDualRatioIntegrand s₁ s₂ (1 / ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x))
          ((-1 : ℂ) + (v : ℂ) * I) := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    productAFEReflectedTerm_eq_dualRatio hx (zetaChi_ne_zero_of_mem_openStrip h₁0 h₁1)
      (zetaChi_ne_zero_of_mem_openStrip h₂0 h₂1) p _

/-- **The left edge is the double dual series with the two-ratio cutoff.** -/
theorem productAFEDualMellinAt_eq_tsum {x : ℝ} (hx : 0 < x) {s₁ s₂ : ℂ}
    (h₁0 : 0 < s₁.re) (h₁1 : s₁.re < 1) (h₂0 : 0 < s₂.re) (h₂1 : s₂.re < 1) :
    productAFEDualMellinAt s₁ s₂ x =
      ∑' p : ℕ × ℕ,
        (zetaChi s₁ * zetaChi s₂ * (p.1 + 1 : ℂ) ^ (s₁ - 1) * (p.2 + 1 : ℂ) ^ (s₂ - 1)) *
          productAFEDualCutoff s₁ s₂ (1 / ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * x)) := by
  unfold productAFEDualMellinAt
  rw [show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num,
    integral_productAFEIntegrand_left_one_eq_tsum hx h₁0 h₁1 h₂0 h₂1, Complex.real_smul,
    ← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [integral_productAFEReflectedTerm_left_one_eq hx h₁0 h₁1 h₂0 h₂1 p, productAFEDualCutoff,
    show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num, Complex.real_smul]
  ring

end RHTower

end
