import GaloisForLFunctions.BiScaleUncertainty.LogGridUniformDirichletTail
import GaloisForLFunctions.RHTower.PaperEGCSourceLanding

/-!
# The coefficient-faithful arithmetic remainder on EGC source rays

Subtracting the literal pole/Gamma difference leaves a convergent signed Dirichlet
series. Its exponential bound is uniform on the whole frequency line, and the first
prime coefficient survives after normalization. Neither statement locates Xi zeros.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section
open GaloisForLFunctions.BiScaleUncertainty

/-- Exact pole/Gamma part, with the same real shift as the full correction. -/
def paperEGCRayArch (eps x σ : ℝ) : ℂ :=
  Complex.I * (eps : ℂ) / 2 *
    (logDeriv archFactor ((σ : ℂ) + ((x + eps : ℝ) : ℂ) * Complex.I) -
      logDeriv archFactor ((σ : ℂ) + ((x - eps : ℝ) : ℂ) * Complex.I))

/-- Signed prime-power coefficient of the exact archimedean-subtracted ray. -/
def paperEGCRayCoeff (eps x : ℝ) (n : ℕ) : ℂ :=
  (-Complex.I * (eps : ℂ) / 2) *
    ((ArithmeticFunction.vonMangoldt n : ℂ) /
        (n : ℂ) ^ (((x + eps : ℝ) : ℂ) * Complex.I) -
      (ArithmeticFunction.vonMangoldt n : ℂ) /
        (n : ℂ) ^ (((x - eps : ℝ) : ℂ) * Complex.I))

/-- Source-defined arithmetic remainder; no zero indexing enters this definition. -/
def paperEGCRayArithmetic (eps x σ : ℝ) : ℂ :=
  LSeries (paperEGCRayCoeff eps x) (σ : ℂ)

theorem paperEGCRayCoeff_zero (eps x : ℝ) : paperEGCRayCoeff eps x 0 = 0 := by
  simp [paperEGCRayCoeff]

theorem paperEGCRayCoeff_one (eps x : ℝ) : paperEGCRayCoeff eps x 1 = 0 := by
  simp [paperEGCRayCoeff]

/-- Every phase is retained, while one frequency-independent positive row bounds its norm. -/
theorem norm_paperEGCRayCoeff_le (eps x : ℝ) (n : ℕ) :
    ‖paperEGCRayCoeff eps x n‖ ≤ |eps| * ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n = 0
  · subst n
    simp [paperEGCRayCoeff_zero]
  have hp : 0 < n := Nat.pos_of_ne_zero hn
  have hphase (t : ℝ) : ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp]
    simp
  have hvm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [paperEGCRayCoeff, norm_mul]
  calc
    ‖-Complex.I * (eps : ℂ) / 2‖ *
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (((x + eps : ℝ) : ℂ) * Complex.I) -
          (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (((x - eps : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖-Complex.I * (eps : ℂ) / 2‖ *
          (‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (((x + eps : ℝ) : ℂ) * Complex.I)‖ +
            ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (((x - eps : ℝ) : ℂ) * Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = _ := by
      simp only [norm_div, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, hphase, hvm, div_one, one_mul]
      norm_num
      ring

private theorem rayCoeff_majorant (eps x : ℝ) (n : ℕ) :
    ‖paperEGCRayCoeff eps x n‖ ≤
      ‖((|eps| : ℝ) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
      norm_paperEGCRayCoeff_le eps x n

/-- Admission is proved from the actual von Mangoldt series, at every Euler-safe abscissa. -/
theorem lSeriesSummable_paperEGCRayCoeff (eps x : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable (paperEGCRayCoeff eps x) (σ : ℂ) := by
  have hg := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)).smul ((|eps| : ℝ) : ℂ)
  exact (lSeries_geometric_bound_of_support (b := 2) (by omega) hg (by simp)
    (by intro n hn; interval_cases n <;> simp [paperEGCRayCoeff_zero, paperEGCRayCoeff_one])
    (rayCoeff_majorant eps x)).1

private theorem rayTerm_identity (eps x σ : ℝ) (n : ℕ) :
    LSeries.term (paperEGCRayCoeff eps x) (σ : ℂ) n =
      (-Complex.I * (eps : ℂ) / 2) *
        (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + ((x + eps : ℝ) : ℂ) * Complex.I) n -
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((σ : ℂ) + ((x - eps : ℝ) : ℂ) * Complex.I) n) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term_of_ne_zero hn, paperEGCRayCoeff,
    Complex.cpow_add _ _ hnC, div_mul_eq_div_div]
  ring

/-- Literal source identity for the entire arithmetic row, not a finite prime approximation. -/
theorem paperEGCRayArithmetic_eq_primeFlux (eps x : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    paperEGCRayArithmetic eps x σ = (-Complex.I * (eps : ℂ) / 2) *
      (infinitePrimeFlux ((σ : ℂ) + ((x + eps : ℝ) : ℂ) * Complex.I) -
        infinitePrimeFlux ((σ : ℂ) + ((x - eps : ℝ) : ℂ) * Complex.I)) := by
  have hp : 1 < ((σ : ℂ) + ((x + eps : ℝ) : ℂ) * Complex.I).re := by simpa using hσ
  have hm : 1 < ((σ : ℂ) + ((x - eps : ℝ) : ℂ) * Complex.I).re := by simpa using hσ
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hp, infinitePrimeFlux_eq_vonMangoldtLSeries hm]
  unfold paperEGCRayArithmetic LSeries
  simp_rw [rayTerm_identity]
  rw [tsum_mul_left, (ArithmeticFunction.LSeriesSummable_vonMangoldt hp).tsum_sub
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hm)]

/-- The actual predeclared EGC ray splits exactly into its pole/Gamma baseline and signed
arithmetic remainder. Every multiplicity copy remains in the complete correction. -/
theorem paperEGCCompleteCorrection_source_ray_split
    (eps x : PaperEGCSmallParameter) {σ : ℝ} (hσ : 1 < σ) :
    paperEGCCompleteCorrection eps x (1 / 2 - σ) =
      paperEGCRayArch eps x σ + paperEGCRayArithmetic eps x σ := by
  have hadd (r : ℝ) :
      (1 / 2 : ℂ) +
        ((((x : ℝ) : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * Complex.I) + (r : ℂ)) * Complex.I =
        (σ : ℂ) + (((x : ℝ) + r : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring_nf
    simp
    ring
  have ha (r : ℝ) : XiExplicitAdmissible
      ((((x : ℝ) : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * Complex.I) + (r : ℂ)) := by
    apply XiExplicitAdmissible_of_one_lt_re
    rw [hadd]
    simpa using hσ
  rw [paperEGCCompleteCorrection_eq_logDeriv,
    ← continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC (ha eps)]
  have hminus := ha (-(eps : ℝ))
  simp only [Complex.ofReal_neg, ← sub_eq_add_neg] at hminus
  rw [← continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hminus,
    paperEGCRayArithmetic_eq_primeFlux _ _ hσ, paperEGCRayArch,
    continuedPrimeArchSourceRelativeTrace, continuedPrimeArchSourceRelativeTrace]
  rw [hadd]
  have hsub := hadd (-(eps : ℝ))
  simp only [Complex.ofReal_neg, ← sub_eq_add_neg] at hsub
  rw [hsub]
  ring

/-- One explicit arithmetic mass pays the full unbounded frequency line. -/
theorem norm_paperEGCRayArithmetic_le (eps x : ℝ) {σ₀ σ : ℝ}
    (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ) :
    ‖paperEGCRayArithmetic eps x σ‖ ≤ (2 : ℝ) ^ (-(σ - σ₀)) *
      (|eps| * ∑' n : ℕ,
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ₀ : ℂ) n‖) := by
  have hg := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ₀ : ℂ)) (by simpa using hσ₀)).smul ((|eps| : ℝ) : ℂ)
  have h := (lSeries_geometric_bound_of_support (b := 2) (by omega) hg
    (s := (σ : ℂ)) (by simpa using hσ)
    (by intro n hn; interval_cases n <;> simp [paperEGCRayCoeff_zero, paperEGCRayCoeff_one])
    (rayCoeff_majorant eps x)).2
  simpa only [paperEGCRayArithmetic, Complex.ofReal_re, Nat.cast_ofNat,
    LSeries.term_smul_apply, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_abs, tsum_mul_left] using h

/-- Exact head deletion: the remaining row begins at the next integer logarithmic node. -/
theorem paperEGCRayArithmetic_sub_first_prime (eps x : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    paperEGCRayArithmetic eps x σ - paperEGCRayCoeff eps x 2 / (2 : ℂ) ^ (σ : ℂ) =
      LSeries (logGridTail 3 (paperEGCRayCoeff eps x)) (σ : ℂ) := by
  have h := (lSeriesSummable_paperEGCRayCoeff eps x hσ).tsum_eq_add_tsum_ite 2
  change LSeries (paperEGCRayCoeff eps x) (σ : ℂ) = _ at h
  have ht : (∑' n : ℕ, if n = 2 then 0 else LSeries.term (paperEGCRayCoeff eps x) (σ : ℂ) n) =
      LSeries (logGridTail 3 (paperEGCRayCoeff eps x)) (σ : ℂ) := by
    apply tsum_congr
    intro n
    by_cases hn : 3 ≤ n
    · have hn2 : n ≠ 2 := by omega
      simp [hn2, LSeries.term, logGridTail, hn]
    · interval_cases n <;> simp_all [LSeries.term, logGridTail, paperEGCRayCoeff_one]
  rw [ht] at h
  simp only [LSeries.term_of_ne_zero (by omega : (2 : ℕ) ≠ 0), Nat.cast_ofNat] at h
  change LSeries (paperEGCRayCoeff eps x) (σ : ℂ) - _ = _
  rw [h]
  ring

/-- Uniform remainder after extracting prime 2. Both the constant and the rate are
independent of the observation frequency `x`. -/
theorem norm_paperEGCRayArithmetic_sub_first_prime_le (eps x : ℝ) {σ₀ σ : ℝ}
    (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ) :
    ‖paperEGCRayArithmetic eps x σ - paperEGCRayCoeff eps x 2 / (2 : ℂ) ^ (σ : ℂ)‖ ≤
      (3 : ℝ) ^ (-(σ - σ₀)) * (|eps| * ∑' n : ℕ,
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ₀ : ℂ) n‖) := by
  rw [paperEGCRayArithmetic_sub_first_prime _ _ (lt_of_lt_of_le hσ₀ hσ)]
  have hg := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ₀ : ℂ)) (by simpa using hσ₀)).smul ((|eps| : ℝ) : ℂ)
  have h := (lSeries_logGridTail_bound (b := 3) (by omega) hg
    (s := (σ : ℂ)) (by simpa using hσ) (rayCoeff_majorant eps x)).2
  simpa only [Complex.ofReal_re, Nat.cast_ofNat, LSeries.term_smul_apply,
    norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, tsum_mul_left] using h

/-- The first nonzero prime survives the completed source ray exactly. -/
theorem tendsto_paperEGCRayArithmetic_first_prime (eps x : ℝ) :
    Tendsto (fun σ : ℝ => (2 : ℂ) ^ (σ : ℂ) * paperEGCRayArithmetic eps x σ)
      atTop (𝓝 (paperEGCRayCoeff eps x 2)) := by
  have ha : LSeries.abscissaOfAbsConv (paperEGCRayCoeff eps x) < ⊤ :=
    lt_of_le_of_lt (lSeriesSummable_paperEGCRayCoeff eps x (σ := 2) (by norm_num)).abscissaOfAbsConv_le
      (EReal.coe_lt_top _)
  simpa only [Nat.cast_one, one_add_one_eq_two, paperEGCRayArithmetic] using
    (LSeries.tendsto_cpow_mul_atTop (n := 1)
      (by intro n hn; interval_cases n <;> simp [paperEGCRayCoeff_zero, paperEGCRayCoeff_one]) ha)

/-- The first prime is a signed arithmetic observation, with its exact shift dependence. -/
theorem paperEGCRayCoeff_centered_two (eps : ℝ) :
    paperEGCRayCoeff eps 0 2 =
      ((-eps * Real.log 2 * Real.sin (eps * Real.log 2) : ℝ) : ℂ) := by
  have hp (t : ℝ) : (2 : ℂ) ^ ((t : ℂ) * Complex.I) =
      (Real.cos (t * Real.log 2) : ℂ) + (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
    have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      simp
    rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog]
    rw [show ((Real.log 2 : ℝ) : ℂ) * ((t : ℂ) * Complex.I) =
      ((t * Real.log 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hi (t : ℝ) : ((2 : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ =
      (Real.cos (t * Real.log 2) : ℂ) - (Real.sin (t * Real.log 2) : ℂ) * Complex.I := by
    rw [← Complex.cpow_neg,
      show -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring, hp]
    simp [neg_mul, sub_eq_add_neg]
  unfold paperEGCRayCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  simp only [Nat.cast_ofNat, zero_add, zero_sub, div_eq_mul_inv]
  rw [hi eps, hi (-eps)]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul]
  ring_nf
  simp

/-- For every prescribed positive small shift, the renormalized actual source is eventually
strictly negative on the centered Euler-safe ray. This does not orient the Xi divisor. -/
theorem eventually_paperEGCRayArithmetic_centered_re_neg {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, (paperEGCRayArithmetic eps 0 σ).re < 0 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have hs : 0 < Real.sin (eps * Real.log 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos heps hl)
    have hle := mul_le_mul_of_nonneg_right heps1 hl.le
    linarith [Real.pi_gt_three]
  have hc : (paperEGCRayCoeff eps 0 2).re < 0 := by
    rw [paperEGCRayCoeff_centered_two, Complex.ofReal_re]
    nlinarith [mul_pos (mul_pos heps hl) hs]
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_paperEGCRayArithmetic_first_prime eps 0)
  filter_upwards [ht.eventually (gt_mem_nhds hc)] with σ hσ
  change ((2 : ℂ) ^ (σ : ℂ) * paperEGCRayArithmetic eps 0 σ).re < 0 at hσ
  have hpow : (2 : ℂ) ^ (σ : ℂ) = (((2 : ℝ) ^ σ : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) σ).symm
  rw [hpow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hσ
  by_contra h
  exact (not_lt_of_ge (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) σ).le
    (le_of_not_gt h))) hσ

end
end RHTower
