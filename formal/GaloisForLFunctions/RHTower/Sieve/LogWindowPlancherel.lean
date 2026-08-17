import GaloisForLFunctions.RHTower.Sieve.GallagherLemma
import GaloisForLFunctions.RHTower.Sieve.LogWindowKernel
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Plancherel for a logarithmic short-interval sum

Write `S(u) = ∑_{u < log n ≤ u + δ} a_n`.  Each summand is the indicator of an interval of length
`δ` in the logarithmic variable, so the Fourier integral of `S` factors as one common kernel times
the Dirichlet polynomial at the reflected frequency:

```text
𝓕 S (w) = K_δ(w) · ∑_n a_n n^{-2πiw},
K_δ(w) = (e^{2πiwδ} - 1) / (2πiw),
‖K_δ(w)‖ = |sin(πδw)| / (π|w|).
```

Plancherel therefore turns the mean square of `S` over the whole line into an *exact* spectral
integral,

```text
∫_ℝ |S(u)|² du = ∫_ℝ ‖K_δ(w)‖² · |∑_n a_n n^{2πiw}|² dw ,
```

with no error term.  The two elementary bounds `‖K_δ(w)‖² ≤ δ²` and `‖K_δ(w)‖² ≤ 1/(πw)²` then give
the majorant `min(δ², (πw)^{-2})` that short-interval arguments consume: the window length caps the
low frequencies, and the inverse square caps the tail.

This is the sharp form of Gallagher's reduction.  The inequality version in
`GallagherSplitIntegral` pays for its convenience with a term proportional to the *sup* of the
Dirichlet polynomial, which is useless once the window is short; the identity here has no such term.
-/

open MeasureTheory Finset Complex
open scoped FourierTransform

namespace RHTower.Sieve

noncomputable section

/-- The window sum, written as a sum of constant indicators. -/
theorem logWindowSum_eq_sum_indicator (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ) :
    logWindowSum a s δ u = ∑ n ∈ s, Set.indicator (logWindow δ n) (fun _ => a n) u := by
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : u ∈ logWindow δ n
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]

theorem memLp_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (δ : ℝ) (p : ENNReal) :
    MemLp (logWindowSum a s δ) p (volume : Measure ℝ) := by
  have h : ∀ n ∈ s, MemLp (Set.indicator (logWindow δ n) (fun _ => a n)) p
      (volume : Measure ℝ) := fun n _ =>
    memLp_indicator_const p (measurableSet_logWindow δ n) (a n)
      (Or.inr (volume_logWindow_ne_top δ n))
  have hsum := memLp_finsetSum' (μ := (volume : Measure ℝ)) (p := p) s h
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun u => ?_) hsum
  rw [Finset.sum_apply]
  exact (logWindowSum_eq_sum_indicator a s δ u).symm

theorem integrable_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (δ : ℝ) :
    Integrable (logWindowSum a s δ) (volume : Measure ℝ) :=
  memLp_one_iff_integrable.mp (memLp_logWindowSum a s δ 1)

/-- The common spectral factor of a logarithmic window of length `δ`. -/
def logWindowKernel (δ w : ℝ) : ℂ :=
  (Complex.exp (((2 * Real.pi * w * δ : ℝ) : ℂ) * Complex.I) - 1) /
    (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)

/-- The Fourier integral of one window indicator. -/
theorem integral_exp_mul_indicator_logWindow (c : ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) {w : ℝ}
    (hw : w ≠ 0) :
    (∫ v : ℝ, Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
        Set.indicator (logWindow δ n) (fun _ => c) v)
      = Complex.exp (((2 * Real.pi * -(w * Real.log n) : ℝ) : ℂ) * Complex.I) *
        (logWindowKernel δ w * c) := by
  have hle : Real.log n - δ ≤ Real.log n := by linarith
  have hcne : (-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    simp [Complex.I_ne_zero, hw, hpi]
  have hrw : ∀ v : ℝ,
      Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
          Set.indicator (logWindow δ n) (fun _ => c) v
        = Set.indicator (logWindow δ n)
            (fun v => Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) * (v : ℂ)) * c)
            v := by
    intro v
    by_cases hv : v ∈ logWindow δ n
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      congr 2
      push_cast
      ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]
  calc (∫ v : ℝ, Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
          Set.indicator (logWindow δ n) (fun _ => c) v)
      = ∫ v : ℝ, Set.indicator (logWindow δ n)
          (fun v => Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) * (v : ℂ)) * c)
          v := integral_congr_ae (Filter.Eventually.of_forall hrw)
    _ = ∫ v in logWindow δ n,
          Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) * (v : ℂ)) * c := by
        rw [integral_indicator (measurableSet_logWindow δ n)]
    _ = ∫ v in (Real.log n - δ)..(Real.log n),
          Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) * (v : ℂ)) * c := by
        rw [logWindow, integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hle]
    _ = ((Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) * ((Real.log n : ℝ) : ℂ))
            - Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) *
                (((Real.log n - δ : ℝ)) : ℂ)))
          / (-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I))) * c := by
        rw [intervalIntegral.integral_mul_const, integral_exp_mul_complex hcne]
    _ = Complex.exp (((2 * Real.pi * -(w * Real.log n) : ℝ) : ℂ) * Complex.I) *
          (logWindowKernel δ w * c) := by
        have hsplit :
            Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) *
                (((Real.log n - δ : ℝ)) : ℂ))
              = Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) *
                  ((Real.log n : ℝ) : ℂ))
                * Complex.exp (((2 * Real.pi * w * δ : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        have hphase :
            Complex.exp (((2 * Real.pi * -(w * Real.log n) : ℝ) : ℂ) * Complex.I)
              = Complex.exp ((-(((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) *
                  ((Real.log n : ℝ) : ℂ)) := by
          congr 1
          push_cast
          ring
        rw [hsplit, hphase, logWindowKernel]
        field_simp
        ring


/-- The modulus of `e^{iθ} - 1`. -/
theorem norm_exp_ofReal_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hexp : Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - 1
      = (((Real.cos θ - 1 : ℝ)) : ℂ) + (((Real.sin θ : ℝ)) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hpyth := Real.sin_sq_add_cos_sq (θ / 2)
  have hdouble := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hdouble
  have hval : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    have hsq : |Real.sin (θ / 2)| ^ 2 = Real.sin (θ / 2) ^ 2 := sq_abs _
    have hpythθ := Real.sin_sq_add_cos_sq θ
    nlinarith [hpyth, hdouble, hpythθ, hsq]
  rw [hexp, Complex.norm_add_mul_I, hval]
  exact Real.sqrt_sq (by positivity)

/-- The modulus of the window kernel. -/
theorem norm_logWindowKernel (δ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    ‖logWindowKernel δ w‖ = |Real.sin (Real.pi * δ * w)| / (Real.pi * |w|) := by
  have hnum : ‖Complex.exp (((2 * Real.pi * w * δ : ℝ) : ℂ) * Complex.I) - 1‖
      = 2 * |Real.sin (Real.pi * δ * w)| := by
    have harg : 2 * Real.pi * w * δ / 2 = Real.pi * δ * w := by ring
    rw [norm_exp_ofReal_mul_I_sub_one, harg]
  have hden : ‖((2 * Real.pi * w : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi * |w| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hwabs : (0 : ℝ) < |w| := abs_pos.mpr hw
  rw [logWindowKernel, norm_div, hnum, hden]
  field_simp

/-- The spectral weight of a window of length `δ`: the squared modulus of its kernel. -/
theorem normSq_logWindowKernel (δ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    ‖logWindowKernel δ w‖ ^ 2
      = Real.sin (Real.pi * δ * w) ^ 2 / (Real.pi * w) ^ 2 := by
  rw [norm_logWindowKernel δ hw, div_pow, sq_abs]
  congr 1
  rw [mul_pow, mul_pow, sq_abs]

theorem normSq_logWindowKernel_neg (δ : ℝ) (w : ℝ) :
    ‖logWindowKernel δ (-w)‖ ^ 2 = ‖logWindowKernel δ w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hw
  · norm_num
  · have hwneg : -w ≠ 0 := neg_ne_zero.mpr hw
    rw [normSq_logWindowKernel δ hw, normSq_logWindowKernel δ hwneg]
    rw [show Real.pi * δ * -w = -(Real.pi * δ * w) by ring, Real.sin_neg]
    rw [show Real.pi * -w = -(Real.pi * w) by ring]
    ring

/-- **The spectral weight never exceeds the square of the window length.** -/
theorem normSq_logWindowKernel_le_sq (δ : ℝ) (w : ℝ) :
    ‖logWindowKernel δ w‖ ^ 2 ≤ δ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [logWindowKernel]
    positivity
  · rw [normSq_logWindowKernel δ hw]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hwabs : (0 : ℝ) < |w| := abs_pos.mpr hw
    have hden : (0 : ℝ) < (Real.pi * w) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hsin : |Real.sin (Real.pi * δ * w)| ≤ |Real.pi * δ * w| := Real.abs_sin_le_abs
    have hsq : Real.sin (Real.pi * δ * w) ^ 2 ≤ (Real.pi * δ * w) ^ 2 := by
      have h1 : Real.sin (Real.pi * δ * w) ^ 2 = |Real.sin (Real.pi * δ * w)| ^ 2 := (sq_abs _).symm
      have h2 : (Real.pi * δ * w) ^ 2 = |Real.pi * δ * w| ^ 2 := (sq_abs _).symm
      rw [h1, h2]
      nlinarith [hsin, abs_nonneg (Real.sin (Real.pi * δ * w)), abs_nonneg (Real.pi * δ * w)]
    nlinarith [hsq]

/-- **The spectral weight decays like the inverse square of the frequency.** -/
theorem normSq_logWindowKernel_le_inv_sq (δ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    ‖logWindowKernel δ w‖ ^ 2 ≤ 1 / (Real.pi * w) ^ 2 := by
  rw [normSq_logWindowKernel δ hw]
  have hden : (0 : ℝ) < (Real.pi * w) ^ 2 := by positivity
  gcongr
  exact Real.sin_sq_le_one _


theorem integrable_exp_mul_indicator_logWindow (c : ℂ) (δ : ℝ) (n : ℕ) (w : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
      Set.indicator (logWindow δ n) (fun _ => c) v) (volume : Measure ℝ) := by
  have hg : Integrable (Set.indicator (logWindow δ n) (fun _ => (‖c‖ : ℝ)))
      (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 (measurableSet_logWindow δ n) (‖c‖ : ℝ)
        (Or.inr (volume_logWindow_ne_top δ n)))
  refine Integrable.mono' hg ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).aestronglyMeasurable
    · exact (stronglyMeasurable_const.indicator
        (measurableSet_logWindow δ n)).aestronglyMeasurable
  · filter_upwards with v
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    by_cases hv : v ∈ logWindow δ n
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, norm_zero]

/-- **The Fourier transform of a logarithmic window sum.**  The window contributes one common
kernel factor, and the arithmetic content is the Dirichlet polynomial at the reflected
frequency. -/
theorem fourier_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {w : ℝ}
    (hw : w ≠ 0) :
    𝓕 (logWindowSum a s δ) w = logWindowKernel δ w * logPoly a s (-w) := by
  have hpoint : ∀ v : ℝ,
      (Real.fourierChar (-(inner ℝ v w : ℝ))) • logWindowSum a s δ v
        = ∑ n ∈ s, Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
            Set.indicator (logWindow δ n) (fun _ => a n) v := by
    intro v
    rw [logWindowSum_eq_sum_indicator, Circle.smul_def, Real.fourierChar_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
  calc 𝓕 (logWindowSum a s δ) w
      = ∫ v : ℝ, (Real.fourierChar (-(inner ℝ v w : ℝ))) • logWindowSum a s δ v :=
        Real.fourier_eq (logWindowSum a s δ) w
    _ = ∫ v : ℝ, ∑ n ∈ s, Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
          Set.indicator (logWindow δ n) (fun _ => a n) v :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ n ∈ s, ∫ v : ℝ, Complex.exp (((2 * Real.pi * -(w * v) : ℝ) : ℂ) * Complex.I) *
          Set.indicator (logWindow δ n) (fun _ => a n) v :=
        integral_finsetSum s fun n _ => integrable_exp_mul_indicator_logWindow (a n) δ n w
    _ = ∑ n ∈ s, Complex.exp (((2 * Real.pi * -(w * Real.log n) : ℝ) : ℂ) * Complex.I) *
          (logWindowKernel δ w * a n) :=
        Finset.sum_congr rfl fun n _ =>
          integral_exp_mul_indicator_logWindow (a n) hδ n hw
    _ = logWindowKernel δ w * logPoly a s (-w) := by
        rw [logPoly, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have hcast : ((2 * Real.pi * -(w * Real.log n) : ℝ) : ℂ)
            = ((2 * Real.pi * (-w * Real.log n) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hcast]
        ring

/-- **Plancherel for a logarithmic short-interval sum.**  The mean square of the window sum over the
whole line is the spectral integral of the Dirichlet polynomial against the window kernel: an
identity, with no error term. -/
theorem integral_normSq_logWindowSum_eq (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      = ∫ w : ℝ, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2 := by
  have hP := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
      (integrable_logWindowSum a s δ) (memLp_logWindowSum a s δ 2)
  rw [← hP]
  have hae : (fun w : ℝ => ‖𝓕 (logWindowSum a s δ) w‖ ^ 2)
      =ᵐ[(volume : Measure ℝ)]
        fun w : ℝ => ‖logWindowKernel δ (-w)‖ ^ 2 * ‖logPoly a s (-w)‖ ^ 2 := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with w hw
    rw [fourier_logWindowSum a s hδ hw, norm_mul, mul_pow, normSq_logWindowKernel_neg]
  rw [integral_congr_ae hae]
  exact integral_neg_eq_self
    (fun w : ℝ => ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2) volume

/-- The spectral density of a logarithmic window sum is integrable. -/
theorem integrable_normSq_logWindowKernel_mul_logPoly (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    Integrable (fun w : ℝ => ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2)
      (volume : Measure ℝ) := by
  have hF := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier
      (integrable_logWindowSum a s δ) (memLp_logWindowSum a s δ 2)
  have hrefl : Integrable
      (fun w : ℝ => ‖logWindowKernel δ (-w)‖ ^ 2 * ‖logPoly a s (-w)‖ ^ 2)
      (volume : Measure ℝ) := by
    refine hF.congr ?_
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with w hw
    rw [fourier_logWindowSum a s hδ hw, norm_mul, mul_pow, normSq_logWindowKernel_neg]
  simpa using hrefl.comp_neg

/-- **The mean square of a logarithmic window sum, against any spectral majorant.** -/
theorem integral_normSq_logWindowSum_le_of_majorant (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) {g : ℝ → ℝ} (hg : Integrable g (volume : Measure ℝ))
    (hbound : ∀ w : ℝ, ‖logWindowKernel δ w‖ ^ 2 * ‖logPoly a s w‖ ^ 2 ≤ g w) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2) ≤ ∫ w : ℝ, g w := by
  rw [integral_normSq_logWindowSum_eq a s hδ]
  exact integral_mono (integrable_normSq_logWindowKernel_mul_logPoly a s hδ) hg hbound

/-- The spectral weight is bounded by the square of the window length and by the inverse square of
the frequency simultaneously. -/
theorem normSq_logWindowKernel_le_min (δ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    ‖logWindowKernel δ w‖ ^ 2 ≤ min (δ ^ 2) (1 / (Real.pi * w) ^ 2) :=
  le_min (normSq_logWindowKernel_le_sq δ w) (normSq_logWindowKernel_le_inv_sq δ hw)

end

end RHTower.Sieve
