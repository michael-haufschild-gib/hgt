import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds

/-!
# The Laplace transform of a measure and its behaviour under convolution

The Laplace transform `laplace μ s = ∫⁻ x, exp (-(s x)) dμ` of a measure on `ℝ` turns the
convolution monoid structure into ordinary multiplication.  On top of the abstract
"multiplicative kernel" calculus of `ConvolutionAtomBounds`
(`lintegral_conv_of_multiplicative`, `lintegral_convPow_of_multiplicative`), the exponential
kernel `x ↦ exp (-(s x))` is the concrete multiplicative kernel, giving:

* `laplace_conv` — convolution ↦ product;
* `laplace_convPow` — the transform of an `n`-fold convolution power is the `n`-th power;
* `InfinitelyDivisible.exists_laplace_root` — infinite divisibility forces the transform to be a
  perfect `n`-th power at every argument and every order.

This last statement is the transform-side skeleton of the Lévy–Khintchine / Steutel–van Harn
analysis of infinitely divisible laws on the half line.
-/

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The **Laplace transform** of a measure on `ℝ`, valued in `ℝ≥0∞`:
`laplace μ s = ∫⁻ x, exp (-(s x)) dμ`.  For `s ≥ 0` and `μ` carried by `[0, ∞)` this is the
classical Laplace–Stieltjes transform. -/
noncomputable def laplace (μ : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ

/-- The Laplace kernel `x ↦ exp (-(s x))` (as an `ℝ≥0∞`-valued function) is measurable. -/
lemma measurable_laplaceKernel (s : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x)))) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
    ((continuous_const.mul continuous_id).neg)).measurable

/-- The Laplace kernel is multiplicative on the additive group:
`exp (-(s (x + y))) = exp (-(s x)) · exp (-(s y))`. -/
lemma laplaceKernel_mul (s x y : ℝ) :
    ENNReal.ofReal (Real.exp (-(s * (x + y)))) =
      ENNReal.ofReal (Real.exp (-(s * x))) * ENNReal.ofReal (Real.exp (-(s * y))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  ring_nf

@[simp] lemma laplaceKernel_zero (s : ℝ) :
    ENNReal.ofReal (Real.exp (-(s * 0))) = 1 := by simp [Real.exp_zero]

/-- **The Laplace transform sends convolution to multiplication.** -/
theorem laplace_conv (μ ν : Measure ℝ) [SFinite ν] (s : ℝ) :
    laplace (μ ∗ ν) s = laplace μ s * laplace ν s :=
  lintegral_conv_of_multiplicative (measurable_laplaceKernel s)
    (fun x y => laplaceKernel_mul s x y) μ ν

/-- **The Laplace transform of an `n`-fold convolution power is the `n`-th power.** -/
theorem laplace_convPow (μ : Measure ℝ) [SFinite μ] (s : ℝ) (n : ℕ) :
    laplace (convPow μ n) s = (laplace μ s) ^ n :=
  lintegral_convPow_of_multiplicative (measurable_laplaceKernel s)
    (fun x y => laplaceKernel_mul s x y) (laplaceKernel_zero s) μ n

/-- The Laplace transform of the point mass at `0` is constantly `1`. -/
@[simp] theorem laplace_dirac_zero (s : ℝ) : laplace (Measure.dirac 0) s = 1 := by
  simp [laplace, lintegral_dirac' _ (measurable_laplaceKernel s)]

/-- **Infinite divisibility forces the Laplace transform to be a perfect `n`-th power at every
argument and every order.**  If `μ` is infinitely divisible then for each `s` and each `n ≥ 1`
there is `r : ℝ≥0∞` — the Laplace transform of the `n`-th convolution root of `μ` — with
`laplace μ s = r ^ n`.  This is the transform-side skeleton of the Lévy–Khintchine /
Steutel–van Harn analysis. -/
theorem InfinitelyDivisible.exists_laplace_root {μ : Measure ℝ} (hμ : InfinitelyDivisible μ)
    (s : ℝ) {n : ℕ} (hn : 0 < n) : ∃ r : ℝ≥0∞, laplace μ s = r ^ n := by
  obtain ⟨ν, hνp, hν⟩ := hμ n hn
  haveI := hνp
  exact ⟨laplace ν s, by rw [hν, laplace_convPow]⟩

/-- The Laplace transform of a point mass: `laplace δₐ s = exp (-(s a))`. -/
theorem laplace_dirac (a s : ℝ) :
    laplace (Measure.dirac a) s = ENNReal.ofReal (Real.exp (-(s * a))) := by
  rw [laplace, lintegral_dirac' _ (measurable_laplaceKernel s)]

/-- At `s = 0` the Laplace transform is the total mass: `laplace μ 0 = μ univ`. -/
theorem laplace_zero (μ : Measure ℝ) : laplace μ 0 = μ Set.univ := by
  simp only [laplace, zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, lintegral_one]

/-- The Laplace transform of a probability measure at `0` equals `1`. -/
@[simp] theorem laplace_zero_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    laplace μ 0 = 1 := by rw [laplace_zero, measure_univ]

/-- **Boundedness on the half line.**  For a probability measure carried by `[0, ∞)` and `s ≥ 0`,
the Laplace transform is at most `1`. -/
theorem laplace_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 ≤ s)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) : laplace μ s ≤ 1 := by
  calc laplace μ s ≤ ∫⁻ _, 1 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hμ] with x hx
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal
          ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr (mul_nonneg hs hx)))
    _ = 1 := by rw [lintegral_one, measure_univ]

/-- **Antitonicity on the half line.**  For a measure carried by `[0, ∞)`, the Laplace transform
is antitone in `s`. -/
theorem laplace_antitone (μ : Measure ℝ) {s t : ℝ} (hst : s ≤ t)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) : laplace μ t ≤ laplace μ s := by
  apply lintegral_mono_ae
  filter_upwards [hμ] with x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simp only [neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_right hst hx

/-- **Strict positivity.**  The Laplace transform of a probability measure is positive at every
argument (the exponential kernel is everywhere positive).  This is what lets one pass to
`-log laplace` in the Bernstein-function analysis. -/
theorem laplace_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) : 0 < laplace μ s := by
  rw [laplace, pos_iff_ne_zero, Ne, lintegral_eq_zero_iff (measurable_laplaceKernel s)]
  intro h
  have hf : ∀ᵐ _x ∂μ, False := by
    filter_upwards [h] with x hx
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    exact absurd hx (not_le.mpr (Real.exp_pos _))
  exact absurd (ae_iff.mp hf) (by simp)

/-- The **cumulant** (log-Laplace) transform `logLaplace μ s = -log (laplace μ s)`.  On the domain
where `laplace μ` lands in `(0, 1]` this is a nonnegative function vanishing at `0`; it turns the
multiplicative Laplace picture into an additive one, and is the object on which the Bernstein /
Lévy–Khintchine analysis of infinitely divisible laws is carried out. -/
noncomputable def logLaplace (μ : Measure ℝ) (s : ℝ) : ℝ :=
  -Real.log (laplace μ s).toReal

/-- The cumulant of a probability measure vanishes at `0`. -/
@[simp] theorem logLaplace_zero_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    logLaplace μ 0 = 0 := by
  rw [logLaplace, laplace_zero_prob, ENNReal.toReal_one, Real.log_one, neg_zero]

/-- **Nonnegativity of the cumulant** on the half line: for a probability measure carried by
`[0, ∞)` and `s ≥ 0`, `0 ≤ logLaplace μ s`. -/
theorem logLaplace_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 ≤ s)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) : 0 ≤ logLaplace μ s := by
  rw [logLaplace, neg_nonneg]
  apply Real.log_nonpos ENNReal.toReal_nonneg
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (laplace_le_one μ hs hμ)

/-- **The cumulant is additive under convolution.**  For probability measures whose Laplace
transforms are finite at `s`, `logLaplace (μ ∗ ν) s = logLaplace μ s + logLaplace ν s`. -/
theorem logLaplace_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : ℝ) (hμfin : laplace μ s ≠ ∞) (hνfin : laplace ν s ≠ ∞) :
    logLaplace (μ ∗ ν) s = logLaplace μ s + logLaplace ν s := by
  rw [logLaplace, logLaplace, logLaplace, laplace_conv, ENNReal.toReal_mul,
    Real.log_mul, neg_add]
  · exact ne_of_gt (ENNReal.toReal_pos (laplace_pos μ s).ne' hμfin)
  · exact ne_of_gt (ENNReal.toReal_pos (laplace_pos ν s).ne' hνfin)

/-- **Infinite divisibility makes the cumulant divisible by every `n`.**  If `μ` is infinitely
divisible then at each `s` and each order `n ≥ 1` there is `c : ℝ` — the cumulant of the `n`-th
convolution root — with `logLaplace μ s = n * c`.  This is the additive Lévy shadow of
`exists_laplace_root`, and holds with no domain restriction: the identity `-log (rⁿ) = n · (-log r)`
is unconditional. -/
theorem InfinitelyDivisible.exists_logLaplace_root {μ : Measure ℝ} (hμ : InfinitelyDivisible μ)
    (s : ℝ) {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, logLaplace μ s = n * c := by
  obtain ⟨r, hr⟩ := hμ.exists_laplace_root s hn
  refine ⟨-Real.log r.toReal, ?_⟩
  rw [logLaplace, hr, ENNReal.toReal_pow, Real.log_pow]
  ring

/-- **Laplace transform of a convolution-power mixture.**  For a mixture `∑ₘ cₘ · Q^{∗m}` the
transform is the power series `∑ₘ cₘ · (laplace Q s)ᵐ`. -/
theorem laplace_convPowMixture (c : ℕ → ℝ≥0∞) (Q : Measure ℝ) [SFinite Q] (s : ℝ) :
    laplace (convPowMixture c Q) s = ∑' m, c m * (laplace Q s) ^ m := by
  rw [laplace, convPowMixture, lintegral_sum_measure]
  refine tsum_congr (fun m => ?_)
  rw [lintegral_smul_measure]
  congr 1
  exact laplace_convPow Q s m

/-- The scaled real exponential series `∑ₘ e^{-λ} aᵐ / m!`, lifted through `ENNReal.ofReal`, equals
`e^{-λ} · eᵃ`. -/
theorem tsum_ofReal_poisson_scaled (lam a : ℝ) (ha : 0 ≤ a) :
    ∑' m : ℕ, ENNReal.ofReal (Real.exp (-lam) * a ^ m / m.factorial)
      = ENNReal.ofReal (Real.exp (-lam) * Real.exp a) := by
  have hsum : Summable (fun m : ℕ => Real.exp (-lam) * a ^ m / m.factorial) := by
    simp_rw [mul_div_assoc]
    exact (Real.summable_pow_div_factorial a).mul_left _
  have hnn : ∀ m : ℕ, 0 ≤ Real.exp (-lam) * a ^ m / m.factorial := fun m => by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  congr 1
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- **Explicit Laplace transform of the compound Poisson law:**
`laplace (compoundPoisson λ Q) s = exp (λ · ((laplace Q s) − 1))`.  The compound Poisson mixture's
transform is the exponential of `λ` times the shifted `Q`-transform. -/
theorem laplace_compoundPoisson (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ) [SFinite Q] (s : ℝ)
    (hfin : laplace Q s ≠ ∞) :
    laplace (compoundPoisson lam Q) s
      = ENNReal.ofReal (Real.exp (lam * ((laplace Q s).toReal - 1))) := by
  rw [compoundPoisson, laplace_convPowMixture]
  set L' := (laplace Q s).toReal with hL'
  have hLeq : laplace Q s = ENNReal.ofReal L' := (ENNReal.ofReal_toReal hfin).symm
  have hL'nn : 0 ≤ L' := ENNReal.toReal_nonneg
  have key : ∀ m : ℕ,
      ENNReal.ofReal (Real.exp (-lam) * lam ^ m / m.factorial) * (laplace Q s) ^ m
        = ENNReal.ofReal (Real.exp (-lam) * (lam * L') ^ m / m.factorial) := by
    intro m
    rw [hLeq, ← ENNReal.ofReal_pow hL'nn, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow]; ring
  simp_rw [key]
  rw [tsum_ofReal_poisson_scaled lam (lam * L') (mul_nonneg hlam hL'nn)]
  congr 1
  rw [← Real.exp_add]
  congr 1; ring

/-- **The compound Poisson cumulant is the explicit closed form `λ · (1 − (laplace Q s))`.**  This
is a concrete Bernstein-type cumulant: a nonnegative multiple of `1 −` (a completely monotone
transform), exhibiting the compound Poisson law's infinite divisibility on the transform side. -/
theorem logLaplace_compoundPoisson (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ) [SFinite Q] (s : ℝ)
    (hfin : laplace Q s ≠ ∞) :
    logLaplace (compoundPoisson lam Q) s = lam * (1 - (laplace Q s).toReal) := by
  rw [logLaplace, laplace_compoundPoisson lam hlam Q s hfin,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]
  ring

/-- On the half line the compound Poisson cumulant is nonnegative. -/
theorem logLaplace_compoundPoisson_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ)
    [IsProbabilityMeasure Q] {s : ℝ} (hs : 0 ≤ s) (hQ : ∀ᵐ x ∂Q, 0 ≤ x) :
    0 ≤ logLaplace (compoundPoisson lam Q) s := by
  have hfin : laplace Q s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (laplace_le_one Q hs hQ)
  rw [logLaplace_compoundPoisson lam hlam Q s hfin]
  apply mul_nonneg hlam
  rw [sub_nonneg, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (laplace_le_one Q hs hQ)

end GaloisForLFunctions.HTGeometry
