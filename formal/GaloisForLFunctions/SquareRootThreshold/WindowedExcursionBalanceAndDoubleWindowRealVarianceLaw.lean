import GaloisForLFunctions.SquareRootThreshold.PrimePolynomialConjugateSymmetryAndQuantitativeOscillation
import GaloisForLFunctions.SquareRootThreshold.DoubleWindowMinApertureAndPairCorrelationExchange
import GaloisForLFunctions.SquareRootThreshold.KroneckerPeakPersistenceAndWindowedDecorrelationLaw

/-!
# Windowed Excursion Balance, Mandatory Kronecker-Peak Compensation, and the Real Double-Windowed Variance Law

This module connects three previously separate developments in `SquareRootThreshold`:
- the pure reality and sub-prime-gap mean-zero law of `primePolynomial` from
  `PrimePolynomialConjugateSymmetryAndQuantitativeOscillation`,
- the interval persistence of Kronecker peaks and troughs from
  `KroneckerPeakPersistenceAndWindowedDecorrelationLaw`, and
- the minimum-aperture double-windowed Gram decomposition from
  `DoubleWindowMinApertureAndPairCorrelationExchange`.

Combining these components yields three unconditional structural results:

1. **Pure Reality of the Explicit-Formula Deviation and Sub-Prime-Gap Real Mean Conservation
   (`im_archPart_sub_zetaZeroConfig_W_eq_zero`,
   `norm_sq_zetaZeroConfig_W_sub_archPart_eq_re_sub_sq`,
   `integral_normSq_mul_re_archPart_sub_W_shift_eq_zero`):**
   For every `C²` test profile `f : ℝ → ℂ` supported in `[-a, a]` and every height `ξ ∈ ℝ`,
   the explicit-formula deviation `archPart f ξ - zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)`
   is purely real, its squared complex norm equals the square of its real part, and its
   `η`-windowed real mean vanishes identically in every window of aperture `2r ≤ log 2`
   (arbitrarily far beyond the square-root threshold `2r e^{2a} ≤ 1`).

2. **Exact Sub-Prime-Gap Excursion Balance, Threshold `L¹` Lower Bound, and Mandatory
   Excursion Compensation Around Kronecker Peaks and Troughs
   (`integral_normSq_mul_posPart_eq_negPart_primePolynomial`,
   `primeVariance_le_primeEnvelope_mul_integral_abs_re_primePolynomial`,
   `primeVariance_le_two_mul_primeEnvelope_mul_integral_posPart`,
   `primeVariance_le_two_mul_primeEnvelope_mul_integral_negPart`,
   `setIntegral_persistence_le_integral_negPartPrimePolynomial`,
   `setIntegral_trough_persistence_le_integral_posPartPrimePolynomial`,
   `exists_kronecker_peak_and_trough_with_compensating_excursions`):**
   In every height window of aperture `2r ≤ log 2` centered at any `ξ₀ ∈ ℝ`, the positive
   excursion integral `∫ ‖h_η(-2πξ)‖² max(Re Π_f(N, ξ + ξ₀), 0) dξ` and negative excursion
   integral `∫ ‖h_η(-2πξ)‖² max(-Re Π_f(N, ξ + ξ₀), 0) dξ` are equal to each other and to half
   the windowed `L¹` norm. Below the square-root threshold (`2rN ≤ 1`), each is bounded below by
   `((∫ ‖η‖²) / (2 M_f(N))) V_f(N)`. Moreover, at every Kronecker peak center `ξ₀` where
   `Re Π_f > B₁` on `[-δ, δ]`, the negative excursion integral in the window centered at `ξ₀`
   itself must be at least `B₁ ∫_{[-δ, δ]} ‖h_η(-2πξ)‖² dξ` (with no `e^{2a}` beyond-threshold
   inflation factor when `2r ≤ log 2`), and symmetrically at every Kronecker trough center.

3. **Real Double-Windowed Secondary-Aperture Diagonalization and Beyond-Threshold Variance Bounds
   (`doubleWindow_re_primePolynomial_sq_eq_diag`,
   `doubleWindow_re_W_sub_archPart_sq_eq_diag`,
   `abs_doubleWindow_re_primePolynomial_sq_sub_diag_le`,
   `abs_doubleWindow_re_W_sub_archPart_sq_sub_diag_le`):**
   Transfers the complex `min r ρ` double-windowed Gram laws into exact real variance identities
   and bounds for `(Re Π_f)²` and `(Re W_ζ - Re A_f)²`, proving that a secondary averaging window
   of aperture `2ρN ≤ 1` restores exact diagonalization even when the primary window aperture `r`
   is arbitrarily large.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ## §1. Pure Reality of the Explicit-Formula Deviation and Sub-Prime-Gap Mean Conservation -/

/-- Exact identity expressing `archPart f ξ - zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)`
as `primePolynomial f ⌊e^{2a}⌋₊ ξ`. -/
theorem archPart_sub_zetaZeroConfig_W_eq_primePolynomial
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    archPart f ξ - zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f) =
      primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ := by
  rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs ξ, sub_sub_cancel]

/-- The explicit-formula deviation `archPart f ξ - zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)`
has zero imaginary part for every `C²` compactly supported test profile `f` and height `ξ ∈ ℝ`. -/
theorem im_archPart_sub_zetaZeroConfig_W_eq_zero
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (archPart f ξ - zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).im = 0 := by
  rw [archPart_sub_zetaZeroConfig_W_eq_primePolynomial hf hfs ξ]
  exact im_primePolynomial_eq_zero f ⌊Real.exp (2 * a)⌋₊ ξ

/-- Real-part form of the explicit-formula decomposition at height `ξ`. -/
theorem re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (archPart f ξ).re - (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re =
      (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re := by
  have h := congrArg Complex.re (archPart_sub_zetaZeroConfig_W_eq_primePolynomial hf hfs ξ)
  simpa [Complex.sub_re] using h

/-- Because `primePolynomial` is purely real, the squared complex norm of
`zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f) - archPart f ξ` equals the square of the
difference of their real parts. -/
theorem norm_sq_zetaZeroConfig_W_sub_archPart_eq_re_sub_sq
    {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    ‖zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f) - archPart f ξ‖ ^ 2 =
      ((zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re - (archPart f ξ).re) ^ 2 := by
  rw [norm_sub_rev, archPart_sub_zetaZeroConfig_W_eq_primePolynomial hf hfs ξ,
    norm_sq_primePolynomial_eq_re_sq,
    ← re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs ξ]
  ring

/-- **Sub-Prime-Gap Real Windowed Mean Conservation:**
In every height window of aperture `2r ≤ log 2` centered at any `ξ₀ ∈ ℝ` (regardless of how
large the profile support radius `a` is), the windowed mean of
`Re A_f(ξ + ξ₀) - Re W_ζ(S_{ξ+ξ₀} f, S_{ξ+ξ₀} f)` vanishes identically. -/
theorem integral_normSq_mul_re_archPart_sub_W_shift_eq_zero
    {a r : ℝ} {η f : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ((archPart f (ξ + ξ₀)).re -
          (zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)).re) = 0 := by
  have hcongr : (fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
      ((archPart f (ξ + ξ₀)).re -
        (zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f)).re)) =
      fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)).re := by
    funext ξ
    rw [re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs (ξ + ξ₀)]
  rw [hcongr]
  exact integral_normSq_mul_re_primePolynomial_shift_eq_zero hη hηs hr f ⌊Real.exp (2 * a)⌋₊ ξ₀

/-! ## §2. Exact Windowed Excursion Balance, `L¹` Lower Bound, and Kronecker Peak Compensation -/

/-- Positive part `max (Re Π_f(N, ξ)) 0` of the prime polynomial at height `ξ`. -/
def posPartPrimePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℝ :=
  max (primePolynomial f N ξ).re 0

/-- Negative part `max (-Re Π_f(N, ξ)) 0` of the prime polynomial at height `ξ`. -/
def negPartPrimePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℝ :=
  max (-(primePolynomial f N ξ).re) 0

theorem posPartPrimePolynomial_nonneg (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    0 ≤ posPartPrimePolynomial f N ξ :=
  le_max_right _ _

theorem negPartPrimePolynomial_nonneg (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    0 ≤ negPartPrimePolynomial f N ξ :=
  le_max_right _ _

theorem two_mul_posPartPrimePolynomial_eq (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    2 * posPartPrimePolynomial f N ξ =
      |(primePolynomial f N ξ).re| + (primePolynomial f N ξ).re := by
  unfold posPartPrimePolynomial
  rcases le_total 0 (primePolynomial f N ξ).re with h | h
  · rw [max_eq_left h, abs_of_nonneg h]
    ring
  · rw [max_eq_right h, abs_of_nonpos h]
    ring

theorem two_mul_negPartPrimePolynomial_eq (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    2 * negPartPrimePolynomial f N ξ =
      |(primePolynomial f N ξ).re| - (primePolynomial f N ξ).re := by
  unfold negPartPrimePolynomial
  rcases le_total 0 (primePolynomial f N ξ).re with h | h
  · rw [max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · rw [max_eq_left (by linarith), abs_of_nonpos h]
    ring

theorem posPart_sub_negPart_primePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    posPartPrimePolynomial f N ξ - negPartPrimePolynomial f N ξ =
      (primePolynomial f N ξ).re := by
  linarith [two_mul_posPartPrimePolynomial_eq f N ξ, two_mul_negPartPrimePolynomial_eq f N ξ]

theorem posPart_add_negPart_primePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    posPartPrimePolynomial f N ξ + negPartPrimePolynomial f N ξ =
      |(primePolynomial f N ξ).re| := by
  linarith [two_mul_posPartPrimePolynomial_eq f N ξ, two_mul_negPartPrimePolynomial_eq f N ξ]

theorem posPartPrimePolynomial_le_primeEnvelope (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    posPartPrimePolynomial f N ξ ≤ primeEnvelope f N :=
  max_le (re_primePolynomial_le_primeEnvelope f N ξ) (primeEnvelope_nonneg f N)

theorem negPartPrimePolynomial_le_primeEnvelope (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    negPartPrimePolynomial f N ξ ≤ primeEnvelope f N :=
  max_le (by linarith [neg_primeEnvelope_le_re_primePolynomial f N ξ]) (primeEnvelope_nonneg f N)

theorem continuous_normSq_paperFT {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) :
    Continuous fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
    Complex.continuous_ofReal)
  refine h.congr fun ξ => ?_
  simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ, Complex.ofReal_re]

theorem integrable_normSq_paperFT {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) :
    Integrable fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
  simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re]

theorem integrable_normSq_mul_bounded {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ ξ, |g ξ| ≤ M) :
    Integrable fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * g ξ := by
  refine ((integrable_normSq_paperFT hη hηs).mul_const M).mono'
    ((continuous_normSq_paperFT hη hηs).mul hg).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM ξ) (sq_nonneg _)

theorem continuous_re_primePolynomial_shift (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    Continuous fun ξ : ℝ => (primePolynomial f N (ξ + ξ₀)).re :=
  (Complex.continuous_re.comp (continuous_expSum _ _ _)).comp (continuous_id.add continuous_const)

/-- Twice the windowed positive excursion integral equals the windowed `L¹` integral of
`Re Π_f(N, · + ξ₀)` whenever `2r ≤ log 2`. -/
theorem two_mul_integral_normSq_mul_posPartPrimePolynomial_eq
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    2 * (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀)) =
      ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| := by
  have hre : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re :=
    integrable_normSq_mul_bounded hη hηs (continuous_re_primePolynomial_shift f N ξ₀)
      fun ξ => abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)
  have habs : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| :=
    integrable_normSq_mul_bounded hη hηs (continuous_abs.comp (continuous_re_primePolynomial_shift f N ξ₀))
      fun ξ => by
        rw [abs_abs]
        exact abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)
  rw [← integral_const_mul]
  have hcongr : (fun ξ : ℝ => 2 * (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
      posPartPrimePolynomial f N (ξ + ξ₀))) =
      fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| +
        ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re := by
    funext ξ
    calc 2 * (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀))
        = ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (2 * posPartPrimePolynomial f N (ξ + ξ₀)) := by
          ring
      _ = ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| +
            ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re := by
          rw [two_mul_posPartPrimePolynomial_eq]
          ring
  rw [hcongr, integral_add habs hre,
    integral_normSq_mul_re_primePolynomial_shift_eq_zero hη hηs hr f N ξ₀, add_zero]

/-- Twice the windowed negative excursion integral equals the windowed `L¹` integral of
`Re Π_f(N, · + ξ₀)` whenever `2r ≤ log 2`. -/
theorem two_mul_integral_normSq_mul_negPartPrimePolynomial_eq
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    2 * (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀)) =
      ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| := by
  have hre : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re :=
    integrable_normSq_mul_bounded hη hηs (continuous_re_primePolynomial_shift f N ξ₀)
      fun ξ => abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)
  have habs : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| :=
    integrable_normSq_mul_bounded hη hηs (continuous_abs.comp (continuous_re_primePolynomial_shift f N ξ₀))
      fun ξ => by
        rw [abs_abs]
        exact abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)
  rw [← integral_const_mul]
  have hcongr : (fun ξ : ℝ => 2 * (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
      negPartPrimePolynomial f N (ξ + ξ₀))) =
      fun ξ : ℝ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| -
        ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re := by
    funext ξ
    calc 2 * (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀))
        = ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (2 * negPartPrimePolynomial f N (ξ + ξ₀)) := by
          ring
      _ = ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| -
            ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re := by
          rw [two_mul_negPartPrimePolynomial_eq]
          ring
  rw [hcongr, integral_sub habs hre,
    integral_normSq_mul_re_primePolynomial_shift_eq_zero hη hηs hr f N ξ₀, sub_zero]

/-- **Exact Sub-Prime-Gap Excursion Balance:**
In every window of aperture `2r ≤ log 2` centered at any height `ξ₀ ∈ ℝ`, the positive and
negative excursion integrals of `primePolynomial f N (· + ξ₀)` are equal. -/
theorem integral_normSq_mul_posPart_eq_negPart_primePolynomial
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀)) =
      ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀) := by
  linarith [two_mul_integral_normSq_mul_posPartPrimePolynomial_eq hη hηs hr f N ξ₀,
    two_mul_integral_normSq_mul_negPartPrimePolynomial_eq hη hηs hr f N ξ₀]

/-- **Threshold Windowed `L¹` Lower Bound:**
Whenever `2rN ≤ 1`, the windowed `L¹` integral of `Re Π_f(N, · + ξ₀)` centered at any `ξ₀ ∈ ℝ`
is bounded below by `(∫ ‖η‖²) * primeVariance f N / primeEnvelope f N`. -/
theorem primeVariance_le_primeEnvelope_mul_integral_abs_re_primePolynomial
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    {N : ℕ} (hN : 2 * r * (N : ℝ) ≤ 1) (f : ℝ → ℂ) (ξ₀ : ℝ) :
    (∫ t, ‖η t‖ ^ 2) * primeVariance f N ≤
      primeEnvelope f N *
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| := by
  have hsq : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * (primePolynomial f N (ξ + ξ₀)).re ^ 2 :=
    integrable_normSq_mul_bounded hη hηs ((continuous_re_primePolynomial_shift f N ξ₀).pow 2)
      fun ξ => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)) 2
  have habs : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * |(primePolynomial f N (ξ + ξ₀)).re| :=
    integrable_normSq_mul_bounded hη hηs (continuous_abs.comp (continuous_re_primePolynomial_shift f N ξ₀))
      fun ξ => by
        rw [abs_abs]
        exact abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)
  rw [← integral_normSq_mul_re_primePolynomial_sq_eq hη hηs hN f ξ₀, ← integral_const_mul]
  refine integral_mono hsq (habs.const_mul (primeEnvelope f N)) fun ξ => ?_
  have hle : (primePolynomial f N (ξ + ξ₀)).re ^ 2 ≤
      primeEnvelope f N * |(primePolynomial f N (ξ + ξ₀)).re| := by
    calc (primePolynomial f N (ξ + ξ₀)).re ^ 2
        = |(primePolynomial f N (ξ + ξ₀)).re| * |(primePolynomial f N (ξ + ξ₀)).re| := by
          rw [← sq, sq_abs]
      _ ≤ primeEnvelope f N * |(primePolynomial f N (ξ + ξ₀)).re| :=
          mul_le_mul_of_nonneg_right
            (abs_re_primePolynomial_le_primeEnvelope f N (ξ + ξ₀)) (abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖paperFT η (-(2 * π * (ξ : ℂ)))‖)
  linarith

/-- **Threshold Windowed Positive-Excursion Lower Bound:**
In every window with `2r ≤ log 2` and `2rN ≤ 1` centered at any height `ξ₀ ∈ ℝ`,
`(∫ ‖η‖²) V_f(N) ≤ 2 M_f(N) ∫ ‖h_η(-2πξ)‖² posPartPrimePolynomial f N (ξ + ξ₀) dξ`. -/
theorem primeVariance_le_two_mul_primeEnvelope_mul_integral_posPart
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) {N : ℕ} (hN : 2 * r * (N : ℝ) ≤ 1) (f : ℝ → ℂ) (ξ₀ : ℝ) :
    (∫ t, ‖η t‖ ^ 2) * primeVariance f N ≤
      2 * primeEnvelope f N *
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀) := by
  have h1 := primeVariance_le_primeEnvelope_mul_integral_abs_re_primePolynomial hη hηs hN f ξ₀
  have h2 := two_mul_integral_normSq_mul_posPartPrimePolynomial_eq hη hηs hr f N ξ₀
  linarith [congrArg (fun x => primeEnvelope f N * x) h2]

/-- **Threshold Windowed Negative-Excursion Lower Bound:**
In every window with `2r ≤ log 2` and `2rN ≤ 1` centered at any height `ξ₀ ∈ ℝ`,
`(∫ ‖η‖²) V_f(N) ≤ 2 M_f(N) ∫ ‖h_η(-2πξ)‖² negPartPrimePolynomial f N (ξ + ξ₀) dξ`. -/
theorem primeVariance_le_two_mul_primeEnvelope_mul_integral_negPart
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) {N : ℕ} (hN : 2 * r * (N : ℝ) ≤ 1) (f : ℝ → ℂ) (ξ₀ : ℝ) :
    (∫ t, ‖η t‖ ^ 2) * primeVariance f N ≤
      2 * primeEnvelope f N *
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀) := by
  rw [← integral_normSq_mul_posPart_eq_negPart_primePolynomial hη hηs hr f N ξ₀]
  exact primeVariance_le_two_mul_primeEnvelope_mul_integral_posPart hη hηs hr hN f ξ₀

/-- **Mandatory Negative Excursion Compensation Around Any Positive Persistence Interval:**
Whenever `B₁ ≤ Re Π_f(N, τ + ξ₀)` for all `τ ∈ [-δ, δ]`, any window `η` with `2r ≤ log 2`
centered at `ξ₀` must observe a negative excursion integral at least
`B₁ ∫_{[-δ, δ]} ‖h_η(-2πξ)‖² dξ`. -/
theorem setIntegral_persistence_le_integral_negPartPrimePolynomial
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) {ξ₀ δ B₁ : ℝ}
    (hpers : ∀ τ ∈ Icc (-δ) δ, B₁ ≤ (primePolynomial f N (τ + ξ₀)).re) :
    B₁ * (∫ ξ in Icc (-δ) δ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
      ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀) := by
  rw [← integral_normSq_mul_posPart_eq_negPart_primePolynomial hη hηs hr f N ξ₀,
    ← integral_const_mul]
  have hpos_int : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀) :=
    integrable_normSq_mul_bounded hη hηs
      ((continuous_re_primePolynomial_shift f N ξ₀).max continuous_const)
      fun ξ => by
        rw [abs_of_nonneg (posPartPrimePolynomial_nonneg f N (ξ + ξ₀))]
        exact posPartPrimePolynomial_le_primeEnvelope f N (ξ + ξ₀)
  have hset_le :
      (∫ ξ in Icc (-δ) δ, B₁ * ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
        ∫ ξ in Icc (-δ) δ,
          ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀) := by
    refine setIntegral_mono_on
      ((integrable_normSq_paperFT hη hηs).const_mul B₁).integrableOn
      hpos_int.integrableOn measurableSet_Icc fun ξ hξ => ?_
    have hle : B₁ ≤ posPartPrimePolynomial f N (ξ + ξ₀) :=
      (hpers ξ hξ).trans (le_max_left _ _)
    have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖paperFT η (-(2 * π * (ξ : ℂ)))‖)
    linarith
  refine hset_le.trans (setIntegral_le_integral hpos_int (Eventually.of_forall fun ξ => ?_))
  exact mul_nonneg (sq_nonneg _) (posPartPrimePolynomial_nonneg f N (ξ + ξ₀))

/-- **Mandatory Positive Excursion Compensation Around Any Negative Persistence Interval:**
Whenever `Re Π_f(N, τ + ξ₁) ≤ -B₁` for all `τ ∈ [-δ, δ]`, any window `η` with `2r ≤ log 2`
centered at `ξ₁` must observe a positive excursion integral at least
`B₁ ∫_{[-δ, δ]} ‖h_η(-2πξ)‖² dξ`. -/
theorem setIntegral_trough_persistence_le_integral_posPartPrimePolynomial
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) {ξ₁ δ B₁ : ℝ}
    (hpers : ∀ τ ∈ Icc (-δ) δ, (primePolynomial f N (τ + ξ₁)).re ≤ -B₁) :
    B₁ * (∫ ξ in Icc (-δ) δ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
      ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₁) := by
  rw [integral_normSq_mul_posPart_eq_negPart_primePolynomial hη hηs hr f N ξ₁,
    ← integral_const_mul]
  have hneg_int : Integrable fun ξ : ℝ =>
      ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₁) :=
    integrable_normSq_mul_bounded hη hηs
      ((continuous_re_primePolynomial_shift f N ξ₁).neg.max continuous_const)
      fun ξ => by
        rw [abs_of_nonneg (negPartPrimePolynomial_nonneg f N (ξ + ξ₁))]
        exact negPartPrimePolynomial_le_primeEnvelope f N (ξ + ξ₁)
  have hset_le :
      (∫ ξ in Icc (-δ) δ, B₁ * ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
        ∫ ξ in Icc (-δ) δ,
          ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₁) := by
    refine setIntegral_mono_on
      ((integrable_normSq_paperFT hη hηs).const_mul B₁).integrableOn
      hneg_int.integrableOn measurableSet_Icc fun ξ hξ => ?_
    have hle : B₁ ≤ negPartPrimePolynomial f N (ξ + ξ₁) :=
      (show B₁ ≤ -(primePolynomial f N (ξ + ξ₁)).re by linarith [hpers ξ hξ]).trans
        (le_max_left _ _)
    have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖paperFT η (-(2 * π * (ξ : ℂ)))‖)
    linarith
  refine hset_le.trans (setIntegral_le_integral hneg_int (Eventually.of_forall fun ξ => ?_))
  exact mul_nonneg (sq_nonneg _) (negPartPrimePolynomial_nonneg f N (ξ + ξ₁))

/-- **Joint Kronecker Peak/Trough Persistence and Compensating Excursion Theorem:**
For every `B₁ < B < primeOnlyEnvelope f N - primePowerTailEnvelope f N` and every `C²` window `η`
supported in `[-r, r]` with `2r ≤ log 2`, there exist a Kronecker peak center `ξ₀ ∈ ℝ` and a
Kronecker trough center `ξ₁ ∈ ℝ` such that on `[-δ, δ]` (`δ = primePersistenceRadius f N (B - B₁)`):
1. `Re Π_f(N, τ + ξ₀) > B₁` on `[-δ, δ]` and the negative excursion integral centered at `ξ₀`
   is at least `B₁ ∫_{[-δ, δ]} ‖h_η(-2πξ)‖² dξ`;
2. `Re Π_f(N, τ + ξ₁) < -B₁` on `[-δ, δ]` and the positive excursion integral centered at `ξ₁`
   is at least `B₁ ∫_{[-δ, δ]} ‖h_η(-2πξ)‖² dξ`. -/
theorem exists_kronecker_peak_and_trough_with_compensating_excursions
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r)
    (hr : 2 * r ≤ Real.log 2) (f : ℝ → ℂ) (N : ℕ) {B₁ B : ℝ}
    (hB₁ : B₁ < B)
    (hB : B < primeOnlyEnvelope f N - primePowerTailEnvelope f N) :
    (∃ ξ₀ : ℝ,
      B < (primePolynomial f N ξ₀).re ∧
      (∀ τ ∈ Icc (-primePersistenceRadius f N (B - B₁))
          (primePersistenceRadius f N (B - B₁)),
        B₁ < (primePolynomial f N (τ + ξ₀)).re) ∧
      B₁ * (∫ ξ in Icc (-primePersistenceRadius f N (B - B₁))
          (primePersistenceRadius f N (B - B₁)),
          ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀) ∧
      ((∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₀)) =
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₀))) ∧
    (∃ ξ₁ : ℝ,
      (primePolynomial f N ξ₁).re < -B ∧
      (∀ τ ∈ Icc (-primePersistenceRadius f N (B - B₁))
          (primePersistenceRadius f N (B - B₁)),
        (primePolynomial f N (τ + ξ₁)).re < -B₁) ∧
      B₁ * (∫ ξ in Icc (-primePersistenceRadius f N (B - B₁))
          (primePersistenceRadius f N (B - B₁)),
          ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2) ≤
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₁) ∧
      ((∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * posPartPrimePolynomial f N (ξ + ξ₁)) =
        ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * negPartPrimePolynomial f N (ξ + ξ₁))) := by
  obtain ⟨⟨ξ₀, hξ₀, hint₀⟩, ⟨ξ₁, hξ₁, hint₁⟩⟩ :=
    exists_interval_gt_and_lt_re_primePolynomial f N hB₁ hB
  refine ⟨⟨ξ₀, hξ₀, hint₀,
    setIntegral_persistence_le_integral_negPartPrimePolynomial hη hηs hr f N
      (fun τ hτ => le_of_lt (hint₀ τ hτ)),
    integral_normSq_mul_posPart_eq_negPart_primePolynomial hη hηs hr f N ξ₀⟩,
    ⟨ξ₁, hξ₁, hint₁,
    setIntegral_trough_persistence_le_integral_posPartPrimePolynomial hη hηs hr f N
      (fun τ hτ => le_of_lt (hint₁ τ hτ)),
    integral_normSq_mul_posPart_eq_negPart_primePolynomial hη hηs hr f N ξ₁⟩⟩

/-! ## §3. Real Double-Windowed Secondary-Aperture Diagonalization & Beyond-Threshold Variance Bounds -/

/-- The complex centred double-windowed mean square of `primePolynomial f N` equals the complex
coercion of the real double-windowed mean square of `(primePolynomial f N (ξ + (ξ₀ + T))).re ^ 2`. -/
theorem doubleWindow_primePolynomial_complex_eq_ofReal
    {η ω : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    (f : ℝ → ℂ) (N : ℕ) (T : ℝ) :
    ∫ ξ₀ : ℝ, pairTransform ω ξ₀ *
        ∫ ξ : ℝ, pairTransform η ξ *
          (expSum (Finset.Icc 2 N ×ˢ Finset.univ) (primeCoeff f) primeFreq (ξ + (ξ₀ + T)) *
            conj (expSum (Finset.Icc 2 N ×ˢ Finset.univ) (primeCoeff f) primeFreq (ξ + (ξ₀ + T)))) =
      ((∫ ξ₀ : ℝ, ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
          ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
            (primePolynomial f N (ξ + (ξ₀ + T))).re ^ 2 : ℝ) : ℂ) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hωc := hasCompactSupport_of_tsupport_subset_Icc hωs
  rw [← integral_complex_ofReal]
  congr 1 with ξ₀
  have hinner : (∫ ξ : ℝ, pairTransform η ξ *
      (expSum (Finset.Icc 2 N ×ˢ Finset.univ) (primeCoeff f) primeFreq (ξ + (ξ₀ + T)) *
        conj (expSum (Finset.Icc 2 N ×ˢ Finset.univ) (primeCoeff f) primeFreq (ξ + (ξ₀ + T))))) =
      ((∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        (primePolynomial f N (ξ + (ξ₀ + T))).re ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1 with ξ
    change pairTransform η ξ *
        (primePolynomial f N (ξ + (ξ₀ + T)) * conj (primePolynomial f N (ξ + (ξ₀ + T)))) = _
    rw [pairTransform_ofReal hη hηc ξ, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_sq_primePolynomial_eq_re_sq, Complex.ofReal_mul]
  rw [hinner, pairTransform_ofReal hω hωc ξ₀, Complex.ofReal_mul]

/-- Whenever `2 * min r ρ * N ≤ 1`, the prime-frequency neighbour set at scale `min r ρ` is empty. -/
theorem closeSet_primeFreq_min_empty {r ρ : ℝ} {N : ℕ} (hN : 2 * min r ρ * (N : ℝ) ≤ 1) :
    ∀ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
      closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq (min r ρ) j = ∅ := by
  intro j hj
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  simp only [closeSet, Finset.mem_filter] at hk
  have hsep := primeFreq_separated_nat hN j hj k hk.1 hk.2.1.symm
  linarith [hk.2.2]

/-- **Real Double-Windowed Secondary-Aperture Diagonalization for `primePolynomial`:**
Even when the primary window aperture `r` exceeds the square-root threshold, if the minimum
aperture satisfies `2 * min r ρ * N ≤ 1`, the centred real double-windowed mean square of
`Re Π_f(N, ξ + (ξ₀ + T))` equals the exact product diagonal `(∫ ‖η‖²) (∫ ‖ω‖²) V_f(N)`. -/
theorem doubleWindow_re_primePolynomial_sq_eq_diag
    {η ω : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    {N : ℕ} (hN : 2 * min r ρ * (N : ℝ) ≤ 1) (f : ℝ → ℂ) (T : ℝ) :
    ∫ ξ₀ : ℝ, ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          (primePolynomial f N (ξ + (ξ₀ + T))).re ^ 2) =
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f N := by
  have h := doubleWindow_centred_expSum_eq_diag_of_closeSet_empty hη hω hηs hωs
    (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) (primeCoeff f) primeFreq T
    (closeSet_primeFreq_min_empty hN)
  rw [doubleWindow_primePolynomial_complex_eq_ofReal hη hω hηs hωs f N T] at h
  have hvar : ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ ^ 2 =
      primeVariance f N := by
    simpa [mul_zero, Complex.exp_zero, mul_one] using sum_norm_sq_primeCoeff_shift_eq f N 0
  have hrhs : ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ t, ‖ω t‖ ^ 2 : ℝ) : ℂ) *
      ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ((‖primeCoeff f j‖ ^ 2 : ℝ) : ℂ) =
      (((∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f N : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum, hvar]
    push_cast
    rfl
  rw [hrhs] at h
  exact Complex.ofReal_injective h

/-- **Real Double-Windowed Secondary-Aperture Diagonalization for `Re W_ζ - Re A_f`:**
When `2 * min r ρ * ⌊e^{2a}⌋₊ ≤ 1`, the centred real double-windowed mean square of
`Re W_ζ(S_{ξ+(ξ₀+T)} f, S_{ξ+(ξ₀+T)} f) - Re A_f(ξ + (ξ₀ + T))` equals
`(∫ ‖η‖²) (∫ ‖ω‖²) V_f(⌊e^{2a}⌋₊)`. -/
theorem doubleWindow_re_W_sub_archPart_sq_eq_diag
    {a r ρ : ℝ} {η ω f : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω)
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hN : 2 * min r ρ * (⌊Real.exp (2 * a)⌋₊ : ℝ) ≤ 1) (T : ℝ) :
    ∫ ξ₀ : ℝ, ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          ((zetaZeroConfig.W (heightShift (ξ + (ξ₀ + T)) f)
              (heightShift (ξ + (ξ₀ + T)) f)).re -
            (archPart f (ξ + (ξ₀ + T))).re) ^ 2) =
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ := by
  have hcongr : (fun ξ₀ : ℝ => ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
      (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ((zetaZeroConfig.W (heightShift (ξ + (ξ₀ + T)) f)
            (heightShift (ξ + (ξ₀ + T)) f)).re -
          (archPart f (ξ + (ξ₀ + T))).re) ^ 2)) =
      fun ξ₀ : ℝ => ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + (ξ₀ + T))).re ^ 2) := by
    funext ξ₀
    congr 2
    funext ξ
    congr 1
    rw [← re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs (ξ + (ξ₀ + T))]
    ring
  rw [hcongr]
  exact doubleWindow_re_primePolynomial_sq_eq_diag hη hω hηs hωs hN f T

/-- **Beyond-Threshold Real Double-Windowed Variance Deviation Bound for `primePolynomial`:**
For any apertures `r, ρ ≥ 0` with `min r ρ ≤ log 2` and `(N : ℝ) ≤ X`, the deviation of the
centred real double-windowed mean square of `Re Π_f(N, ξ + (ξ₀ + T))` from its diagonal is at most
`(∫ ‖η‖²) (∫ ‖ω‖²) X (e^{2 min(r,ρ)} - e^{-2 min(r,ρ)}) V_f(N)`. -/
theorem abs_doubleWindow_re_primePolynomial_sq_sub_diag_le
    {η ω f : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ X : ℝ} {N : ℕ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hmin2 : min r ρ ≤ Real.log 2) (hNX : (N : ℝ) ≤ X)
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ) (T : ℝ) :
    |(∫ ξ₀ : ℝ, ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          (primePolynomial f N (ξ + (ξ₀ + T))).re ^ 2)) -
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f N| ≤
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) *
        (X * (Real.exp (2 * min r ρ) - Real.exp (-(2 * min r ρ))) * primeVariance f N) := by
  have hsplit := integral_pairTransform_mul_integral_windowed_centred_eq_diag_add_closeSet
    hη hω hηs hωs (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) (primeCoeff f) primeFreq T
  rw [doubleWindow_primePolynomial_complex_eq_ofReal hη hω hηs hωs f N T] at hsplit
  have hvar : ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ ^ 2 =
      primeVariance f N := by
    simpa [mul_zero, Complex.exp_zero, mul_one] using sum_norm_sq_primeCoeff_shift_eq f N 0
  have hdiag : ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ t, ‖ω t‖ ^ 2 : ℝ) : ℂ) *
      ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ((‖primeCoeff f j‖ ^ 2 : ℝ) : ℂ) =
      (((∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f N : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum, hvar]
    push_cast
    rfl
  rw [hdiag] at hsplit
  have hsub : (((∫ ξ₀ : ℝ, ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          (primePolynomial f N (ξ + (ξ₀ + T))).re ^ 2)) -
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f N : ℝ) : ℂ) =
      ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
        ∑ k ∈ closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq (min r ρ) j,
          primeCoeff f j * conj (primeCoeff f k) *
            EF.weilTest η η (primeFreq j - primeFreq k) *
            EF.weilTest ω ω (primeFreq j - primeFreq k) *
            cexp (2 * π * I * T * ((primeFreq j - primeFreq k : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sub, hsplit]
    ring
  have hnorm := congrArg norm hsub
  rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hnorm]
  exact norm_doubleWindow_primeFreq_offDiag_le hη hω hr hρ hmin2 hNX hηs hωs T

/-- **Beyond-Threshold Real Double-Windowed Variance Deviation Bound for `Re W_ζ - Re A_f`:**
For any `C²` profile `f` supported in `[-a, a]` and windows `η, ω` with `0 ≤ r, ρ` and
`min r ρ ≤ log 2`, the deviation of the centred real double-windowed mean square of
`Re W_ζ - Re A_f` from its diagonal is at most
`(∫ ‖η‖²) (∫ ‖ω‖²) e^{2a} (e^{2 min(r,ρ)} - e^{-2 min(r,ρ)}) V_f(⌊e^{2a}⌋₊)`. -/
theorem abs_doubleWindow_re_W_sub_archPart_sq_sub_diag_le
    {a r ρ : ℝ} {η ω f : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω)
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hmin2 : min r ρ ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (T : ℝ) :
    |(∫ ξ₀ : ℝ, ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          ((zetaZeroConfig.W (heightShift (ξ + (ξ₀ + T)) f)
              (heightShift (ξ + (ξ₀ + T)) f)).re -
            (archPart f (ξ + (ξ₀ + T))).re) ^ 2)) -
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊| ≤
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) *
        (Real.exp (2 * a) * (Real.exp (2 * min r ρ) - Real.exp (-(2 * min r ρ))) *
          primeVariance f ⌊Real.exp (2 * a)⌋₊) := by
  have hcongr : (fun ξ₀ : ℝ => ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
      (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ((zetaZeroConfig.W (heightShift (ξ + (ξ₀ + T)) f)
            (heightShift (ξ + (ξ₀ + T)) f)).re -
          (archPart f (ξ + (ξ₀ + T))).re) ^ 2)) =
      fun ξ₀ : ℝ => ‖paperFT ω (-(2 * π * (ξ₀ : ℂ)))‖ ^ 2 *
        (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
          (primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + (ξ₀ + T))).re ^ 2) := by
    funext ξ₀
    congr 2
    funext ξ
    congr 1
    rw [← re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial hf hfs (ξ + (ξ₀ + T))]
    ring
  rw [hcongr]
  exact abs_doubleWindow_re_primePolynomial_sq_sub_diag_le hη hω hr hρ hmin2
    (Nat.floor_le (Real.exp_pos (2 * a)).le) hηs hωs T

end GaloisForLFunctions.SquareRootThreshold

end
