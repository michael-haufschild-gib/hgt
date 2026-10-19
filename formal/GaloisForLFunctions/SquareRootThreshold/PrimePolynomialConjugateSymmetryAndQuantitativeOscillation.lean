import GaloisForLFunctions.SquareRootThreshold.PrimeTailCouplingCriterion
import GaloisForLFunctions.SquareRootThreshold.ZetaSmallApertureHeightWindowPositivity

/-!
# Autocorrelation Conjugate Symmetry, Pure Reality, and Quantitative Two-Sided Oscillation of the Prime Polynomial

In `PrimeTailCouplingCriterion`, `exists_lt_re_primePolynomial` showed that for every negative
level `A₀ < 0`, there exists `ξ ∈ ℝ` with `A₀ < (primePolynomial f N ξ).re`, using only the
vanishing of the windowed first moment (`∫ |h_η(−2πξ)|² Π_f(ξ) dξ = 0`). Because a first-moment
argument alone cannot rule out `Π_f ≡ 0` on the support of the window or control imaginary parts,
it could neither prove strict positivity `0 < Re Π_f(ξ)` nor produce a quantitative positive
threshold.

This module resolves this limitation by connecting the autocorrelation involution
`EF.tilde (EF.weilTest f f) = EF.weilTest f f` (`RHTower.WeilSpectral.tilde_weilTest_self`) with
a simultaneous first-and-second windowed moment method:

1. **Autocorrelation Hermitian Symmetry and Pure Reality of `primePolynomial`
   (`weilTest_self_neg_eq_conj`, `primeCoeff_false_eq_conj_true`, `conj_primePolynomial`,
   `im_primePolynomial_eq_zero`, `norm_sq_primePolynomial_eq_re_sq`):**
   For **every** function `f : ℝ → ℂ` (with no regularity or support hypotheses),
   `k_f(−v) = conj(k_f(v))`. Consequently, the `±log n` coefficients of `primePolynomial f N`
   come in exact complex-conjugate pairs `primeCoeff f (n, false) = conj (primeCoeff f (n, true))`,
   so `primePolynomial f N ξ` is purely real at every height `ξ ∈ ℝ` and satisfies
   `‖primePolynomial f N ξ‖² = ((primePolynomial f N ξ).re)²`.

2. **Sub-Prime-Gap Windowed Mean-Zero Law and Windowed Archimedean Cancellation
   (`integral_pairTransform_mul_primePolynomial_shift_eq_zero`,
   `integral_normSq_mul_re_primePolynomial_shift_eq_zero`,
   `integral_pairTransform_mul_archPart_sub_W_eq_zero`):**
   For every `C²` window `η` supported in `[-r, r]` with `2r ≤ log 2` and every centre `ξ₀ ∈ ℝ`,
   all prime frequencies `±log n` (`n ≥ 2`) lie outside `(-2r, 2r)`, so the windowed mean of
   `primePolynomial f N (· + ξ₀)` vanishes identically. For every `C²` profile `f` of arbitrary
   aperture `a`, the height-windowed difference between `archPart f (· + ξ₀)` and
   `zetaZeroConfig.W (heightShift (· + ξ₀) f) (heightShift (· + ξ₀) f)` therefore integrates to `0`.

3. **Quantitative One-Sided Variance Bounds and Two-Sided Oscillation Law
   (`primeVariance_le_mul_primeEnvelope_of_re_le`,
   `primeVariance_le_mul_primeEnvelope_of_neg_le_re`,
   `exists_gt_and_lt_re_primePolynomial_of_lt_primeVariance`):**
   Let `M_f(N) = primeEnvelope f N = Σ_j ‖primeCoeff f j‖`. Since `|Re Π_f(ξ)| ≤ M_f(N)`, if
   `Re Π_f(ξ) ≤ B` everywhere (`B ≥ 0`), then `(B − Re Π_f(ξ))(Re Π_f(ξ) + M_f(N)) ≥ 0`, i.e.
   `(Re Π_f(ξ))² ≤ (M_f(N) − B) Re Π_f(ξ) + B · M_f(N)`. Integrating against a positive window of
   aperture `r ≤ min(1/4, 1/(2N))` annihilates the linear term while evaluating the quadratic term
   to `primeVariance f N` (via pure reality `‖Π_f‖² = (Re Π_f)²`), proving unconditionally:
   `primeVariance f N ≤ B * primeEnvelope f N`.
   Whenever `B * primeEnvelope f N < primeVariance f N` (in particular for `B = 0` whenever
   `primeVariance f N > 0`), `primePolynomial f N` attains both strictly positive values `> B`
   and strictly negative values `< −B`.
-/

open MeasureTheory Complex Set Filter Topology Finset
open scoped Real ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ## §1. Autocorrelation Hermitian Symmetry and Pure Reality of `primePolynomial` -/

/-- **Autocorrelation Hermitian Symmetry (`weilTest_self_neg_eq_conj`):**
For every function `f : ℝ → ℂ` and every lag `v ∈ ℝ`, `k_f(−v) = conj(k_f(v))`. -/
theorem weilTest_self_neg_eq_conj (f : ℝ → ℂ) (v : ℝ) :
    EF.weilTest f f (-v) = conj (EF.weilTest f f v) := by
  have h := congrFun (RHTower.WeilSpectral.tilde_weilTest_self f) (-v)
  simpa [EF.tilde, neg_neg] using h.symm

/-- The negative-frequency prime coefficient `(n, false)` is the complex conjugate of `(n, true)`. -/
theorem primeCoeff_false_eq_conj_true (f : ℝ → ℂ) (n : ℕ) :
    primeCoeff f (n, false) = conj (primeCoeff f (n, true)) := by
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, map_mul,
    Complex.conj_ofReal, weilTest_self_neg_eq_conj]

/-- Each `(n, false)` harmonic in `primePolynomial` is the complex conjugate of the `(n, true)`
harmonic. -/
theorem primeCoeff_mul_cexp_false_eq_conj_true (f : ℝ → ℂ) (n : ℕ) (ξ : ℝ) :
    primeCoeff f (n, false) * cexp (2 * π * I * ξ * primeFreq (n, false)) =
      conj (primeCoeff f (n, true) * cexp (2 * π * I * ξ * primeFreq (n, true))) := by
  rw [map_mul, primeCoeff_false_eq_conj_true, ← Complex.exp_conj]
  congr 2
  simp only [primeFreq, ↓reduceIte, Bool.false_eq_true, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- **Conjugate Invariance of `primePolynomial` (`conj_primePolynomial`):**
For every `f : ℝ → ℂ`, cutoff `N : ℕ`, and height `ξ ∈ ℝ`, `primePolynomial f N ξ` equals its
own complex conjugate. -/
theorem conj_primePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    conj (primePolynomial f N ξ) = primePolynomial f N ξ := by
  unfold primePolynomial expSum
  rw [Finset.sum_product, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fintype.sum_bool, map_add, primeCoeff_mul_cexp_false_eq_conj_true, Complex.conj_conj,
    add_comm]

/-- **Pure Reality of `primePolynomial` (`im_primePolynomial_eq_zero`):**
The imaginary part of `primePolynomial f N ξ` vanishes identically for all `f`, `N`, and `ξ`. -/
theorem im_primePolynomial_eq_zero (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    (primePolynomial f N ξ).im = 0 := by
  have h := congrArg Complex.im (conj_primePolynomial f N ξ)
  rw [Complex.conj_im] at h
  linarith

theorem primePolynomial_eq_ofReal_re (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    primePolynomial f N ξ = ((primePolynomial f N ξ).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [im_primePolynomial_eq_zero]

/-- **Norm-Square Identity (`norm_sq_primePolynomial_eq_re_sq`):**
Because `primePolynomial f N ξ` is purely real, its squared complex norm equals the square of its
real part. -/
theorem norm_sq_primePolynomial_eq_re_sq (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    ‖primePolynomial f N ξ‖ ^ 2 = (primePolynomial f N ξ).re ^ 2 := by
  conv_lhs => rw [primePolynomial_eq_ofReal_re f N ξ]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## §2. Sub-Prime-Gap Windowed Mean-Zero Law and Archimedean Cancellation -/

/-- **Sub-Prime-Gap Windowed Mean-Zero Law
(`integral_pairTransform_mul_primePolynomial_shift_eq_zero`):**
For any `C²` window `η` supported in `[-r, r]` with `2 * r ≤ Real.log 2`, any `f : ℝ → ℂ`,
any cutoff `N : ℕ`, and any height shift `ξ₀ ∈ ℝ`, the windowed mean of
`primePolynomial f N (· + ξ₀)` vanishes identically. -/
theorem integral_pairTransform_mul_primePolynomial_shift_eq_zero
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, pairTransform η ξ * primePolynomial f N (ξ + ξ₀) = 0 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hshift : (fun ξ : ℝ => pairTransform η ξ * primePolynomial f N (ξ + ξ₀)) =
      fun ξ : ℝ => pairTransform η ξ *
        expSum (Finset.Icc 2 N ×ˢ Finset.univ)
          (fun j => primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)) primeFreq ξ := by
    funext ξ
    rw [primePolynomial, expSum_add]
  rw [hshift, integral_pairTransform_mul_expSum hη hηc]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨n, b⟩ := j
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hj
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hj.1)
  have hfar : 2 * r ≤ |primeFreq (n, b)| := by
    cases b <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true, abs_neg] <;>
      rw [abs_of_nonneg (le_trans (Real.log_nonneg (by norm_num)) hlog)] <;> linarith
  rw [weilTest_self_eq_zero_of_le hη hηs hfar, mul_zero]

/-- Real form of the sub-prime-gap windowed mean-zero law. -/
theorem integral_normSq_mul_re_primePolynomial_shift_eq_zero
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re = 0 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have h := congrArg Complex.re
    (integral_pairTransform_mul_primePolynomial_shift_eq_zero hη hηs hr f N ξ₀)
  have hfun : (fun ξ : ℝ => pairTransform η ξ * primePolynomial f N (ξ + ξ₀)) =
      fun ξ : ℝ => ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        (primePolynomial f N (ξ + ξ₀)).re : ℝ) : ℂ) := by
    funext ξ
    conv_lhs =>
      rw [pairTransform_ofReal hη hηc ξ, primePolynomial_eq_ofReal_re f N (ξ + ξ₀)]
    exact (Complex.ofReal_mul _ _).symm
  rw [hfun, integral_complex_ofReal, Complex.ofReal_re, Complex.zero_re] at h
  exact h

/-- **Windowed Archimedean Cancellation (`integral_pairTransform_mul_archPart_sub_W_eq_zero`):**
For any `C²` test `f` supported in `[-a, a]` (of arbitrary aperture `a`) and any `C²` window `η`
supported in `[-r, r]` with `2 * r ≤ Real.log 2`, the height-windowed deviation
`archPart f (ξ + ξ₀) − zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)`
integrates to `0`. -/
theorem integral_pairTransform_mul_archPart_sub_W_eq_zero
    {a r : ℝ} {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r) (hr : 2 * r ≤ Real.log 2) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, pairTransform η ξ *
      (archPart f (ξ + ξ₀) -
        zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)) = 0 := by
  have hcongr : (fun ξ : ℝ => pairTransform η ξ *
      (archPart f (ξ + ξ₀) -
        zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f))) =
      fun ξ : ℝ => pairTransform η ξ * primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀) := by
    funext ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs (ξ + ξ₀), sub_sub_cancel]
  rw [hcongr]
  exact integral_pairTransform_mul_primePolynomial_shift_eq_zero hη hηs hr f _ ξ₀

/-! ## §3. Real Second-Moment Law and Quantitative One-Sided Variance Bounds -/

/-- Prime frequencies in `Finset.Icc 2 N ×ˢ Finset.univ` are `2r`-separated whenever `2rN ≤ 1`. -/
theorem primeFreq_separated_nat {N : ℕ} {r : ℝ} (hN : 2 * r * (N : ℝ) ≤ 1) :
    ∀ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
      ∀ k ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
        j ≠ k → 2 * r ≤ |primeFreq j - primeFreq k| := by
  rcases lt_or_ge N 2 with hlt | hge
  · intro j hj
    simp only [Finset.mem_product, Finset.mem_Icc] at hj
    omega
  · have hX1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hsep := primeFreq_separated hX1 hN
    rwa [Nat.floor_natCast] at hsep

/-- **Real Windowed Second-Moment Law (`integral_normSq_mul_re_primePolynomial_sq_eq`):**
Because `primePolynomial f N` is purely real, its squared real part has exact windowed mean
`‖η‖² * primeVariance f N` whenever `2 * r * N ≤ 1`. -/
theorem integral_normSq_mul_re_primePolynomial_sq_eq
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    {N : ℕ} (hN : 2 * r * (N : ℝ) ≤ 1) (f : ℝ → ℂ) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * primeVariance f N := by
  have hcongr : (fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
      (primePolynomial f N (ξ + ξ₀)).re ^ 2) =
      fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖expSum (Finset.Icc 2 N ×ˢ Finset.univ)
          (fun j => primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)) primeFreq ξ‖ ^ 2 := by
    funext ξ
    rw [← norm_sq_primePolynomial_eq_re_sq, primePolynomial, expSum_add]
  rw [hcongr, integral_normSq_mul_normSq_expSum_of_separated hη hηs _ _ _
    (primeFreq_separated_nat hN), sum_norm_sq_primeCoeff_shift_eq]

/-- The `ℓ¹` prime-coefficient envelope `M_f(N) = Σ_{j ∈ [2, N] × Bool} ‖primeCoeff f j‖`. -/
def primeEnvelope (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖

theorem primeEnvelope_nonneg (f : ℝ → ℂ) (N : ℕ) : 0 ≤ primeEnvelope f N :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem abs_re_primePolynomial_le_primeEnvelope (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    |(primePolynomial f N ξ).re| ≤ primeEnvelope f N :=
  (Complex.abs_re_le_norm _).trans (norm_expSum_le _ _ _ _)

theorem neg_primeEnvelope_le_re_primePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    -primeEnvelope f N ≤ (primePolynomial f N ξ).re :=
  (abs_le.mp (abs_re_primePolynomial_le_primeEnvelope f N ξ)).1

theorem re_primePolynomial_le_primeEnvelope (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    (primePolynomial f N ξ).re ≤ primeEnvelope f N :=
  (abs_le.mp (abs_re_primePolynomial_le_primeEnvelope f N ξ)).2

/-- Pointwise quadratic bound when `(primePolynomial f N ξ).re ≤ B`. -/
theorem re_primePolynomial_sq_le_of_le (f : ℝ → ℂ) (N : ℕ) {B ξ : ℝ}
    (hB : (primePolynomial f N ξ).re ≤ B) :
    (primePolynomial f N ξ).re ^ 2 ≤
      (B - primeEnvelope f N) * (primePolynomial f N ξ).re + B * primeEnvelope f N := by
  have h1 : 0 ≤ primeEnvelope f N + (primePolynomial f N ξ).re := by
    linarith [neg_primeEnvelope_le_re_primePolynomial f N ξ]
  have h2 : 0 ≤ B - (primePolynomial f N ξ).re := sub_nonneg.mpr hB
  have hprod := mul_nonneg h1 h2
  have hexp :
      (primeEnvelope f N + (primePolynomial f N ξ).re) * (B - (primePolynomial f N ξ).re) =
        (B - primeEnvelope f N) * (primePolynomial f N ξ).re + B * primeEnvelope f N -
          (primePolynomial f N ξ).re ^ 2 := by ring
  linarith

/-- Pointwise quadratic bound when `-B ≤ (primePolynomial f N ξ).re`. -/
theorem re_primePolynomial_sq_le_of_neg_le (f : ℝ → ℂ) (N : ℕ) {B ξ : ℝ}
    (hB : -B ≤ (primePolynomial f N ξ).re) :
    (primePolynomial f N ξ).re ^ 2 ≤
      (primeEnvelope f N - B) * (primePolynomial f N ξ).re + B * primeEnvelope f N := by
  have h1 : 0 ≤ primeEnvelope f N - (primePolynomial f N ξ).re := by
    linarith [re_primePolynomial_le_primeEnvelope f N ξ]
  have h2 : 0 ≤ (primePolynomial f N ξ).re + B := by linarith
  have hprod := mul_nonneg h1 h2
  have hexp :
      (primeEnvelope f N - (primePolynomial f N ξ).re) * ((primePolynomial f N ξ).re + B) =
        (primeEnvelope f N - B) * (primePolynomial f N ξ).re + B * primeEnvelope f N -
          (primePolynomial f N ξ).re ^ 2 := by ring
  linarith

/-- Total mass of the window weight `‖paperFT η (-(2 * π * ξ))‖²`. -/
theorem integral_normSq_paperFT_two_pi_eq {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = ∫ t, ‖η t‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have h := weilTest_eq_integral hη hηc (a := r) (fun u hu => by
    by_contra h'
    exact hu (image_eq_zero_of_notMem_tsupport fun ht => h' (abs_le.mpr (hηs ht)))) 0
  rw [weilTest_self_zero] at h
  have h2 : ∫ ξ : ℝ, pairTransform η ξ * cexp (2 * π * I * ξ * ((0 : ℝ) : ℂ)) =
      ((∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1 with ξ
    rw [pairTransform_ofReal hη hηc ξ]
    simp
  rw [h2] at h
  exact_mod_cast h.symm

/-- For every `r > 0`, the window `sinhTest r 1` has strictly positive `L²` energy. -/
theorem integral_sinhTest_sq_pos_of_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ t, ‖((sinhTest r 1 t : ℝ) : ℂ)‖ ^ 2 := by
  set s := sinhTest r 1 with hs
  have hcont : Continuous s := (sinhTest_contDiff _ _).continuous
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ r := sinhTest_supp hr.le
  have hsq : (fun t => ‖((s t : ℝ) : ℂ)‖ ^ 2) = fun t => s t ^ 2 := by
    funext t
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hsq]
  have hcs : HasCompactSupport s :=
    HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun u hu => by
      by_contra h
      exact hu (abs_le.mp (hsupp u h))
  have hint : Integrable fun t => s t ^ 2 :=
    (hcont.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro hcs
      fun t ht => by simp [image_eq_zero_of_notMem_tsupport ht])
  have hnn : 0 ≤ ∫ t, s t ^ 2 := integral_nonneg fun t => sq_nonneg (s t)
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    have hae : (fun t => s t ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (f := fun t => s t ^ 2) (fun t => sq_nonneg (s t)) hint).mp
        h.symm
    have hae' : (fun t => s t * Real.sinh (1 * t)) =ᵐ[volume] 0 := by
      filter_upwards [hae] with t ht
      have : s t = 0 := by simpa using ht
      simp [this]
    have hzero : ∫ t, s t * Real.sinh (1 * t) = 0 := by
      rw [integral_congr_ae hae']
      simp
    have hlb := sinhTest_energy_ge (a := r) (δ := 1) (w := r / 4) one_pos (by linarith)
      (by linarith)
    have hpos : 0 < r / 4 * (r / 4 * r) ^ (5 / 2 : ℝ) *
        Real.sinh (1 * (r - 2 * (r / 4))) ^ 2 := by
      have : 0 < Real.sinh (1 * (r - 2 * (r / 4))) := Real.sinh_pos_iff.mpr (by linarith)
      positivity
    rw [← hs, hzero] at hlb
    linarith

/-- **Quantitative One-Sided Upper Variance Bound (`primeVariance_le_mul_primeEnvelope_of_re_le`):**
For any `f : ℝ → ℂ`, cutoff `N : ℕ`, and `B ∈ ℝ`, if `(primePolynomial f N ξ).re ≤ B` for all
`ξ ∈ ℝ`, then `primeVariance f N ≤ B * primeEnvelope f N`. -/
theorem primeVariance_le_mul_primeEnvelope_of_re_le
    (f : ℝ → ℂ) (N : ℕ) {B : ℝ} (hB : ∀ ξ : ℝ, (primePolynomial f N ξ).re ≤ B) :
    primeVariance f N ≤ B * primeEnvelope f N := by
  set r : ℝ := 1 / (4 * ((N : ℝ) + 1)) with hr_def
  have hr0 : 0 < r := by positivity
  have hrN : 2 * r * (N : ℝ) ≤ 1 := by
    have h1 : 2 * r * (N : ℝ) = (2 * (N : ℝ)) / (4 * ((N : ℝ) + 1)) := by
      rw [hr_def]
      ring
    rw [h1, div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hrlog : 2 * r ≤ Real.log 2 := by
    have h2 : 2 * r ≤ 1 / 2 := by
      have h1 : 2 * r = 2 / (4 * ((N : ℝ) + 1)) := by
        rw [hr_def]
        ring
      rw [h1, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2
    linarith
  set η : ℝ → ℂ := fun u => ((sinhTest r 1 u : ℝ) : ℂ) with hη_def
  have hη : ContDiff ℝ 2 η := sinhTest_ofReal_contDiff r 1
  have hηs : tsupport η ⊆ Icc (-r) r := sinhTest_tsupport_subset hr0.le
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP_def
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP_def]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ, Complex.ofReal_re, hP_def]
  have hQc : Continuous fun ξ => (primePolynomial f N ξ).re :=
    Complex.continuous_re.comp (continuous_expSum _ _ _)
  set M := primeEnvelope f N with hM_def
  have hPQi : Integrable fun ξ => P ξ * (primePolynomial f N ξ).re := by
    refine (hPi.mul_const M).mono' (hPc.mul hQc).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_re_primePolynomial_le_primeEnvelope f N ξ) (sq_nonneg _)
  have hPQ2i : Integrable fun ξ => P ξ * (primePolynomial f N ξ).re ^ 2 := by
    refine (hPi.mul_const (M ^ 2)).mono' (hPc.mul (hQc.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _),
      ← sq_abs ((primePolynomial f N ξ).re)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_re_primePolynomial_le_primeEnvelope f N ξ) 2)
      (sq_nonneg _)
  have hptw : ∀ ξ : ℝ, P ξ * (primePolynomial f N ξ).re ^ 2 ≤
      (B - M) * (P ξ * (primePolynomial f N ξ).re) + (B * M) * P ξ := by
    intro ξ
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hq := mul_le_mul_of_nonneg_left (re_primePolynomial_sq_le_of_le f N (hB ξ)) hP0
    linarith
  have hmono : (∫ ξ : ℝ, P ξ * (primePolynomial f N ξ).re ^ 2) ≤
      ∫ ξ : ℝ, ((B - M) * (P ξ * (primePolynomial f N ξ).re) + (B * M) * P ξ) :=
    integral_mono hPQ2i ((hPQi.const_mul (B - M)).add (hPi.const_mul (B * M))) hptw
  have hvar := integral_normSq_mul_re_primePolynomial_sq_eq hη hηs hrN f 0
  have hmean := integral_normSq_mul_re_primePolynomial_shift_eq_zero hη hηs hrlog f N 0
  simp only [add_zero] at hvar hmean
  change ∫ ξ : ℝ, P ξ * (primePolynomial f N ξ).re ^ 2 = (∫ t, ‖η t‖ ^ 2) * primeVariance f N at hvar
  change ∫ ξ : ℝ, P ξ * (primePolynomial f N ξ).re = 0 at hmean
  have hmass : ∫ ξ : ℝ, P ξ = ∫ t, ‖η t‖ ^ 2 := integral_normSq_paperFT_two_pi_eq hη hηs
  rw [integral_add (hPQi.const_mul (B - M)) (hPi.const_mul (B * M)),
    integral_const_mul, integral_const_mul, hvar, hmean, hmass, mul_zero, zero_add] at hmono
  have hpos : 0 < ∫ t, ‖η t‖ ^ 2 := integral_sinhTest_sq_pos_of_pos hr0
  nlinarith

/-- **Quantitative One-Sided Lower Variance Bound (`primeVariance_le_mul_primeEnvelope_of_neg_le_re`):**
For any `f : ℝ → ℂ`, cutoff `N : ℕ`, and `B ∈ ℝ`, if `-B ≤ (primePolynomial f N ξ).re` for all
`ξ ∈ ℝ`, then `primeVariance f N ≤ B * primeEnvelope f N`. -/
theorem primeVariance_le_mul_primeEnvelope_of_neg_le_re
    (f : ℝ → ℂ) (N : ℕ) {B : ℝ} (hB : ∀ ξ : ℝ, -B ≤ (primePolynomial f N ξ).re) :
    primeVariance f N ≤ B * primeEnvelope f N := by
  set r : ℝ := 1 / (4 * ((N : ℝ) + 1)) with hr_def
  have hr0 : 0 < r := by positivity
  have hrN : 2 * r * (N : ℝ) ≤ 1 := by
    have h1 : 2 * r * (N : ℝ) = (2 * (N : ℝ)) / (4 * ((N : ℝ) + 1)) := by
      rw [hr_def]
      ring
    rw [h1, div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hrlog : 2 * r ≤ Real.log 2 := by
    have h2 : 2 * r ≤ 1 / 2 := by
      have h1 : 2 * r = 2 / (4 * ((N : ℝ) + 1)) := by
        rw [hr_def]
        ring
      rw [h1, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2
    linarith
  set η : ℝ → ℂ := fun u => ((sinhTest r 1 u : ℝ) : ℂ) with hη_def
  have hη : ContDiff ℝ 2 η := sinhTest_ofReal_contDiff r 1
  have hηs : tsupport η ⊆ Icc (-r) r := sinhTest_tsupport_subset hr0.le
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP_def
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP_def]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ, Complex.ofReal_re, hP_def]
  have hQc : Continuous fun ξ => (primePolynomial f N ξ).re :=
    Complex.continuous_re.comp (continuous_expSum _ _ _)
  set M := primeEnvelope f N with hM_def
  have hPQi : Integrable fun ξ => P ξ * (primePolynomial f N ξ).re := by
    refine (hPi.mul_const M).mono' (hPc.mul hQc).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_re_primePolynomial_le_primeEnvelope f N ξ) (sq_nonneg _)
  have hPQ2i : Integrable fun ξ => P ξ * (primePolynomial f N ξ).re ^ 2 := by
    refine (hPi.mul_const (M ^ 2)).mono' (hPc.mul (hQc.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _),
      ← sq_abs ((primePolynomial f N ξ).re)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_re_primePolynomial_le_primeEnvelope f N ξ) 2)
      (sq_nonneg _)
  have hptw : ∀ ξ : ℝ, P ξ * (primePolynomial f N ξ).re ^ 2 ≤
      (M - B) * (P ξ * (primePolynomial f N ξ).re) + (B * M) * P ξ := by
    intro ξ
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hq := mul_le_mul_of_nonneg_left (re_primePolynomial_sq_le_of_neg_le f N (hB ξ)) hP0
    linarith
  have hmono : (∫ ξ : ℝ, P ξ * (primePolynomial f N ξ).re ^ 2) ≤
      ∫ ξ : ℝ, ((M - B) * (P ξ * (primePolynomial f N ξ).re) + (B * M) * P ξ) :=
    integral_mono hPQ2i ((hPQi.const_mul (M - B)).add (hPi.const_mul (B * M))) hptw
  have hvar := integral_normSq_mul_re_primePolynomial_sq_eq hη hηs hrN f 0
  have hmean := integral_normSq_mul_re_primePolynomial_shift_eq_zero hη hηs hrlog f N 0
  simp only [add_zero] at hvar hmean
  change ∫ ξ : ℝ, P ξ * (primePolynomial f N ξ).re ^ 2 = (∫ t, ‖η t‖ ^ 2) * primeVariance f N at hvar
  change ∫ ξ : ℝ, P ξ * (primePolynomial f N ξ).re = 0 at hmean
  have hmass : ∫ ξ : ℝ, P ξ = ∫ t, ‖η t‖ ^ 2 := integral_normSq_paperFT_two_pi_eq hη hηs
  rw [integral_add (hPQi.const_mul (M - B)) (hPi.const_mul (B * M)),
    integral_const_mul, integral_const_mul, hvar, hmean, hmass, mul_zero, zero_add] at hmono
  have hpos : 0 < ∫ t, ‖η t‖ ^ 2 := integral_sinhTest_sq_pos_of_pos hr0
  nlinarith

/-- **Quantitative Two-Sided Oscillation Law for the Prime Polynomial
(`exists_gt_and_lt_re_primePolynomial_of_lt_primeVariance`):**
For every `f : ℝ → ℂ`, cutoff `N : ℕ`, and threshold `B ∈ ℝ` satisfying
`B * primeEnvelope f N < primeVariance f N`, there exist heights `ξ₊, ξ₋ ∈ ℝ` such that
`B < (primePolynomial f N ξ₊).re` and `(primePolynomial f N ξ₋).re < -B`. -/
theorem exists_gt_and_lt_re_primePolynomial_of_lt_primeVariance
    (f : ℝ → ℂ) (N : ℕ) {B : ℝ} (hB : B * primeEnvelope f N < primeVariance f N) :
    (∃ ξ : ℝ, B < (primePolynomial f N ξ).re) ∧
      (∃ ξ : ℝ, (primePolynomial f N ξ).re < -B) := by
  constructor
  · by_contra hcon
    simp only [not_exists, not_lt] at hcon
    linarith [primeVariance_le_mul_primeEnvelope_of_re_le f N hcon]
  · by_contra hcon
    simp only [not_exists, not_lt] at hcon
    linarith [primeVariance_le_mul_primeEnvelope_of_neg_le_re f N hcon]

/-- **Strict Sign-Change Law (`exists_pos_and_neg_re_primePolynomial`):**
Whenever `primeVariance f N > 0`, the prime polynomial `primePolynomial f N` takes both
strictly positive and strictly negative values on `ℝ`. -/
theorem exists_pos_and_neg_re_primePolynomial
    (f : ℝ → ℂ) (N : ℕ) (hV : 0 < primeVariance f N) :
    (∃ ξ : ℝ, 0 < (primePolynomial f N ξ).re) ∧
      (∃ ξ : ℝ, (primePolynomial f N ξ).re < 0) := by
  have h := exists_gt_and_lt_re_primePolynomial_of_lt_primeVariance f N (B := 0) (by linarith)
  simpa using h

/-- **Quantitative Coupled RH Consequence (`exists_gt_re_archPart_of_riemannHypothesis`):**
Under `RiemannHypothesis`, for every `C²` profile `f` supported in `[-a, a]` and every `B ∈ ℝ`
with `B * primeEnvelope f ⌊e^{2a}⌋₊ < primeVariance f ⌊e^{2a}⌋₊`, there exists a height `ξ ∈ ℝ`
at which `B < (archPart f ξ).re`. -/
theorem exists_gt_re_archPart_of_riemannHypothesis
    (hRH : RiemannHypothesis) {a B : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B * primeEnvelope f ⌊Real.exp (2 * a)⌋₊ < primeVariance f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ : ℝ, B < (archPart f ξ).re := by
  obtain ⟨⟨ξ, hξ⟩, -⟩ := exists_gt_and_lt_re_primePolynomial_of_lt_primeVariance f _ hB
  refine ⟨ξ, lt_of_lt_of_le hξ ?_⟩
  exact riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs ξ

end GaloisForLFunctions.SquareRootThreshold

end
