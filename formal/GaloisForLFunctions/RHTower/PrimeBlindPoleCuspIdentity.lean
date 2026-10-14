import GaloisForLFunctions.RHTower.DilationAutocorrelationPeriodization

/-!
# The pole term of prime-blind positivity is the cusp value of the twisted kernel

Let `f` be continuous and supported in `[α, β]` with `0 < α ≤ β`.  Its prime-blind positivity test
has Mellin data `|𝓜f(½+it)|²` and kernel the dilation autocorrelation
`A_f(r) = ∫_0^∞ f(y) f(ry) dy` (`dilationAutocorr`).  The pole term of that test is
`2 𝓜f(1) 𝓜f(0) = 2 (∫ f)(∫ f(y)/y dy)`.

**Theorem** (`halfLineCosTransform_dilationAutocorr_zero`, `cosDilationKernel_zero_eq`).
`C A_f(0) = Ψ_f(0) = 2 (∫_0^∞ f)(∫_0^∞ f(y)/y dy)`,
where `C` is the half-line cosine transform and `Ψ_f = Cf ⋆ f` is the cosine–dilation kernel.

So three quantities coincide:
* the pole term of prime-blind positivity;
* the value at the cusp `x = 0` of the twisted kernel `C A_f`, whose Mellin data are
  `e^{2iθ(t)} |𝓜f(½+it)|²` (`θ` the Riemann–Siegel phase);
* the zeroth Farey coefficient `a₀ = Ψ_f(0)` of the null-face (Ξ²-divisible) test built from the
  same `f`.

**Consequence for spectra near the half-Gram points.**
* *The twist defect.*  The defect `C A_f − ι(C A_f)` (`ι g(x) = g(1/x)/x`) has Mellin data
  `2i sin(2θ(t)) |𝓜f(½+it)|²` on the critical line.  Concentrating the spectrum near the half-Gram
  points `θ ∈ (π/2)ℤ` makes this regular part small.
* *Its cusp value.*  As `x → 0`, `ι(C A_f)(x) = (C A_f)(1/x)/x → 0`, while `(C A_f)(x) → C A_f(0)`,
  which is the pole term.  The singular part of the defect at the cusp is therefore exactly the
  pole term, and spectral concentration cannot shrink it.
* *Dichotomy.*  A prime-blind test with negligible pole term has archimedean part about
  `(log T/2π)·mass` at spectral height `T`, so prime-blind positivity holds trivially and no
  off-line zero is detected.  A test that can detect an off-line zero needs a large negative pole
  term, and then the defect at the cusp is large.
* *Verdict.*  In neither case does a perturbed Mayer equation arise with a small perturbation where
  the Riemann-hypothesis content lies.  This is the zero-slack principle in its cusp form.
-/

open MeasureTheory Set Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-- **The mass of the dilation autocorrelation**: `∫_0^∞ A_f = (∫_0^∞ f)(∫_0^∞ f(y)/y dy)`. -/
theorem integral_Ioi_dilationAutocorr (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ r in Ioi (0 : ℝ), dilationAutocorr f r =
      (∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y := by
  unfold dilationAutocorr
  set F : ℝ × ℝ → ℝ := fun p => f p.2 * f (p.1 * p.2) with hF
  have hFc : Continuous F := by
    simp only [hF]
    exact (hf.comp continuous_snd).mul (hf.comp (continuous_fst.mul continuous_snd))
  have hFs : HasCompactSupport F := by
    refine HasCompactSupport.intro ((isCompact_Icc (a := α / β) (b := β / α)).prod
      (isCompact_Icc (a := α) (b := β))) fun p hp => ?_
    by_contra hne
    simp only [hF] at hne
    have h1 : f p.2 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : f (p.2 * p.1) ≠ 0 := fun h => hne (by rw [mul_comm p.1 p.2, h, mul_zero])
    obtain ⟨hy, hr⟩ := ratio_mem_Icc_of_support hα hαβ hsupp h1 h2
    exact hp ⟨hr, hy⟩
  have hint : Integrable (Function.uncurry fun r y => f y * f (r * y))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    exact (hFc.integrable_of_hasCompactSupport hFs).restrict
  rw [integral_integral_swap hint]
  have hin : ∀ y ∈ Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), f y * f (r * y) =
      f y / y * ∫ w in Ioi (0 : ℝ), f w := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [integral_const_mul, integral_comp_mul_right_Ioi (fun w => f w) 0 hy0, zero_mul,
      smul_eq_mul]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_mul_const]
  ring

/-- **The cusp value of the twisted kernel**: `C A_f(0) = 2 (∫ f)(∫ f(y)/y dy)`. -/
theorem halfLineCosTransform_dilationAutocorr_zero (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    halfLineCosTransform (dilationAutocorr f) 0 =
      2 * (∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y := by
  unfold halfLineCosTransform
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [integral_Ioi_dilationAutocorr hf hα hαβ hsupp]
  ring

/-- **The zeroth Farey coefficient of the null-face kernel**: `Ψ_f(0) = 2 (∫ f)(∫ f(y)/y dy)`. -/
theorem cosDilationKernel_zero_eq (f : ℝ → ℝ) :
    cosDilationKernel f 0 = 2 * (∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y := by
  unfold cosDilationKernel
  have hC : halfLineCosTransform f 0 = 2 * ∫ y in Ioi (0 : ℝ), f y := by
    unfold halfLineCosTransform
    simp only [mul_zero, Real.cos_zero, mul_one]
  simp only [zero_div, hC]
  have e : ∀ y : ℝ, f y * (2 * ∫ z in Ioi (0 : ℝ), f z) / y =
      (2 * ∫ z in Ioi (0 : ℝ), f z) * (f y / y) := fun y => by ring
  simp_rw [e]
  rw [integral_const_mul]

/-- **The pole term, the cusp value and the zeroth null-face coefficient coincide**:
`C A_f(0) = Ψ_f(0)`. -/
theorem halfLineCosTransform_dilationAutocorr_zero_eq_cosDilationKernel_zero (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    halfLineCosTransform (dilationAutocorr f) 0 = cosDilationKernel f 0 := by
  rw [halfLineCosTransform_dilationAutocorr_zero hf hα hαβ hsupp, cosDilationKernel_zero_eq]

end

end RHTower
