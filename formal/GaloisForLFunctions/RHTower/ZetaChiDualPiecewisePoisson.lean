import GaloisForLFunctions.RHTower.PoissonSummationPiecewise

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- Complex finite-interval Poisson summation, retaining the complete symmetric
Fourier tail as a limit. This applies to actual complex dual amplitudes. -/
theorem tendsto_complex_piecewise_cosTransform {a b u : ℝ} (hab : a ≤ b) (hu : 0 < u)
    (hna : ∀ k : ℤ, a / u ≠ (k : ℝ)) (hnb : ∀ k : ℤ, b / u ≠ (k : ℝ))
    {h h' h'' : ℝ → ℂ}
    (hd1 : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hd2 : ∀ x ∈ Icc a b, HasDerivAt h' (h'' x) x)
    (hc2 : ContinuousOn h'' (Icc a b)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((2 / u : ℝ) : ℂ) * ∫ t in a..b, h t *
          ((Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) : ℝ) : ℂ)) atTop
      (𝓝 ((∑ m ∈ Finset.Ioc ⌊a / u⌋ ⌊b / u⌋, h ((m : ℝ) * u)) -
        ((1 / u : ℝ) : ℂ) * ∫ t in a..b, h t)) := by
  have hh : ContinuousOn h (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun x hx => (hd1 x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable h volume a b := hh.intervalIntegrable
  have hIntR {f : ℝ → ℂ} (hf : IntervalIntegrable f volume a b) :
      (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re := by
    simpa only [RCLike.re_to_complex] using (intervalIntegral.intervalIntegral_re hf).symm
  have hIntI {f : ℝ → ℂ} (hf : IntervalIntegrable f volume a b) :
      (∫ x in a..b, f x).im = ∫ x in a..b, (f x).im := by
    simpa only [RCLike.im_to_complex] using (intervalIntegral.intervalIntegral_im hf).symm
  have hiw (n : ℕ) : IntervalIntegrable (fun t : ℝ => h t *
      ((Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) : ℝ) : ℂ)) volume a b :=
    (hh.mul (by fun_prop)).intervalIntegrable
  have hr := GaloisForLFunctions.RHTower.tendsto_sum_cosTransform hab hu hna hnb
    (h := fun x => (h x).re) (h' := fun x => (h' x).re) (h'' := fun x => (h'' x).re)
    (fun x hx => Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd1 x hx))
    (fun x hx => Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hd2 x hx))
    (Complex.continuous_re.comp_continuousOn hc2)
  have him := GaloisForLFunctions.RHTower.tendsto_sum_cosTransform hab hu hna hnb
    (h := fun x => (h x).im) (h' := fun x => (h' x).im) (h'' := fun x => (h'' x).im)
    (fun x hx => Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hd1 x hx))
    (fun x hx => Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hd2 x hx))
    (Complex.continuous_im.comp_continuousOn hc2)
  have hwr (n : ℕ) :
      (∫ t in a..b, h t * ((Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) : ℝ) : ℂ)).re =
        ∫ t in a..b, (h t).re * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) := by
    rw [hIntR (hiw n)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hwi (n : ℕ) :
      (∫ t in a..b, h t * ((Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) : ℝ) : ℂ)).im =
        ∫ t in a..b, (h t).im * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) := by
    rw [hIntI (hiw n)]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add]
  let F : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N,
    ((2 / u : ℝ) : ℂ) * ∫ t in a..b,
      h t * ((Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) : ℝ) : ℂ)
  let L : ℂ := (∑ m ∈ Finset.Ioc ⌊a / u⌋ ⌊b / u⌋, h ((m : ℝ) * u)) -
    ((1 / u : ℝ) : ℂ) * ∫ t in a..b, h t
  have hFr : Tendsto (fun N => (F N).re) atTop (𝓝 L.re) := by
    simpa only [F, L, Complex.re_sum, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hwr,
      hIntR hi] using hr
  have hFi : Tendsto (fun N => (F N).im) atTop (𝓝 L.im) := by
    simpa only [F, L, Complex.im_sum, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hwi,
      hIntI hi] using him
  have hlim := hFr.ofReal.add (hFi.ofReal.mul_const I)
  simpa only [Complex.re_add_im] using hlim

end RHTower
