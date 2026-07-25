import GaloisForLFunctions.RHTower.XiGaussianTestFunction
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect

/-!
# The Gaussian source contour approximates the Gaussian heat moment

The rectangle synthesis law of `XiGuinandWeilSpectralRectangle` is general in its test function:
for any entire `g` and any finite packet of divisor copies there is an admissible rectangle on which

`rectIntegral (g * continuedPrimeArchSourceRelativeTrace) = 2 pi i * sum over enclosed copies of g`.

Instantiating it at the centered Gaussian--Hermite test `z ^ (2n) * exp (-t z^2)` turns the
right-hand side into a partial sum of `xiGaussianHeatMoment n t`, whose summability is already in
the corpus.  Cofinality of admissible rectangles then gives: **the normalized prime--archimedean
contour of the Gaussian test approximates the Gaussian heat moment to arbitrary accuracy.**

In the centered coordinate the test's estimates read off the two proved in `XiGaussianTestFunction`
with the roles of the axes exchanged: the strip bound there is a bound on `|Im z| <= R`, and its
decay variable is `Re z`, so it kills the rectangle's left and right edges; the vertical-line
integrability there is integrability along `Re z` at fixed `Im z`, i.e. along the horizontal edges.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The centered Gaussian–Hermite test: the coordinate in which the Xi divisor lives. -/
def xiGaussianTestC (t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  z ^ (2 * n) * Complex.exp (-(t : ℂ) * z ^ 2)

theorem differentiable_xiGaussianTestC (t : ℝ) (n : ℕ) :
    Differentiable ℂ (xiGaussianTestC t n) := by
  unfold xiGaussianTestC
  fun_prop

theorem analyticOnNhd_xiGaussianTestC (t : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ (xiGaussianTestC t n) Set.univ := fun z _ =>
  ((differentiable_xiGaussianTestC t n).differentiableOn (s := Set.univ)).analyticOnNhd
    isOpen_univ z (Set.mem_univ z)

/-- On the divisor the centered test is exactly the Gaussian heat monomial. -/
theorem xiGaussianTestC_spectralPoint (t : ℝ) (n : ℕ) (q : XiZeroCopy) :
    xiGaussianTestC t n (xiSpectralPoint q) =
      (xiSpectralPoint q ^ 2) ^ n * xiGaussianHeatTerm t q := by
  rw [xiGaussianTestC, xiGaussianHeatTerm, pow_mul]

/-- **The Gaussian source contour reproduces the enclosed divisor values.**  Instantiation of the
general rectangle synthesis law at the centered Gaussian–Hermite test. -/
theorem exists_admissible_rectIntegral_gaussianSource_eq_xiZeroCopy_sum
    (F : Finset XiZeroCopy) (t : ℝ) (n : ℕ) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ F, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
      rectIntegral (fun z => xiGaussianTestC t n z *
          continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
        2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiGaussianTestC t n (xiSpectralPoint q) :=
  exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing F
    (analyticOnNhd_xiGaussianTestC t n)

/-- **The normalized Gaussian source contour approximates the Gaussian heat moment.**  For every
accuracy there is an admissible rectangle whose normalized prime--archimedean contour integral of
the Gaussian test lies within that accuracy of `xiGaussianHeatMoment n t`. -/
theorem exists_admissible_gaussianSource_contour_approximates_heatMoment
    {t : ℝ} (ht : 0 < t) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist ((2 * Real.pi * I)⁻¹ *
          rectIntegral (fun z => xiGaussianTestC t n z *
            continuedPrimeArchSourceRelativeTrace z) z₁ z₂)
        (xiGaussianHeatMoment n t) < epsilon := by
  classical
  set f : XiZeroCopy → ℂ := fun q =>
    (xiSpectralPoint q ^ 2) ^ n * xiGaussianHeatTerm t q with hf
  have hsum : Summable f := summable_xiGaussianHeatMonomialTerm ht n
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨F, hF⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    exists_admissible_rectIntegral_gaussianSource_eq_xiZeroCopy_sum F t n
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    simp [hpi0, Complex.I_ne_zero]
  have hnorm : (2 * Real.pi * I : ℂ)⁻¹ *
      rectIntegral (fun z => xiGaussianTestC t n z *
        continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f q := by
    rw [hcontour, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
    exact Finset.sum_congr rfl fun q _ => xiGaussianTestC_spectralPoint t n q
  rw [hnorm, xiGaussianHeatMoment]
  have hsubset : F ⊆ xiZeroCopyClosedRectangle z₁ z₂ := fun q hq => hcontains q hq
  exact hF _ hsubset

end

end RHTower
