import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# The half-line Wiener–Hopf transgression of an integrable kernel

Zero extension turns the retarded half-line operator `T₋ f (x) = ∫_0^∞ k(x − L) f(L) dL` into an
ordinary line convolution, so Young's `L¹ ⋆ L² → L²` inequality bounds it by `‖k‖₁‖f‖₂`.  The
advanced operator `T₊ f (x) = ∫_0^∞ k(x + L) f(L) dL` is its reflection when the kernel is even,
and therefore obeys the same bound; the even and odd halves `C` and `S` inherit it.

* `RHTower.halfLineConvMinus`, `RHTower.halfLineConvPlus`;
* `RHTower.halfLineConvPlus_eq_halfLineConvMinus_neg`;
* `RHTower.lintegral_enorm_sq_halfLineConvMinus_le`,
  `RHTower.lintegral_enorm_sq_halfLineConvPlus_le`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RHTower

/-- The retarded half-line transgression `T₋`. -/
def halfLineConvMinus (k f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ L in Ioi (0 : ℝ), k (x - L) * f L

/-- The advanced half-line transgression `T₊`. -/
def halfLineConvPlus (k f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ L in Ioi (0 : ℝ), k (x + L) * f L

/-- The even half `C = (T₋ + T₊)/2`. -/
def halfLineConvEven (k f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (halfLineConvMinus k f x + halfLineConvPlus k f x) / 2

/-- The odd half `S = (T₋ − T₊)/2`. -/
def halfLineConvOdd (k f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (halfLineConvMinus k f x - halfLineConvPlus k f x) / 2

/-- **Equation (3): the advanced operator is the reflection of the retarded one.** -/
theorem halfLineConvPlus_eq_halfLineConvMinus_neg {k : ℝ → ℂ}
    (hk : ∀ x : ℝ, k (-x) = k x) (f : ℝ → ℂ) (x : ℝ) :
    halfLineConvPlus k f x = halfLineConvMinus k f (-x) := by
  rw [halfLineConvPlus, halfLineConvMinus]
  refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
  rw [show -x - L = -(x + L) by ring, hk]

/-- `C f` is even. -/
theorem halfLineConvEven_neg {k : ℝ → ℂ} (hk : ∀ x : ℝ, k (-x) = k x) (f : ℝ → ℂ) (x : ℝ) :
    halfLineConvEven k f (-x) = halfLineConvEven k f x := by
  rw [halfLineConvEven, halfLineConvEven,
    halfLineConvPlus_eq_halfLineConvMinus_neg hk f x,
    halfLineConvPlus_eq_halfLineConvMinus_neg hk f (-x), neg_neg]
  ring

/-- `S f` is odd. -/
theorem halfLineConvOdd_neg {k : ℝ → ℂ} (hk : ∀ x : ℝ, k (-x) = k x) (f : ℝ → ℂ) (x : ℝ) :
    halfLineConvOdd k f (-x) = -halfLineConvOdd k f x := by
  rw [halfLineConvOdd, halfLineConvOdd,
    halfLineConvPlus_eq_halfLineConvMinus_neg hk f x,
    halfLineConvPlus_eq_halfLineConvMinus_neg hk f (-x), neg_neg]
  ring

/-! ### The `L²` bound -/

/-- Zero extension of a half-line datum. -/
def zeroExtend (f : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator f

theorem halfLineConvMinus_eq_lineConv (k f : ℝ → ℂ) (x : ℝ) :
    halfLineConvMinus k f x = ∫ L : ℝ, k (x - L) * zeroExtend f L := by
  rw [halfLineConvMinus, ← MeasureTheory.integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (.of_forall fun L => ?_)
  by_cases hL : L ∈ Ioi (0 : ℝ)
  · simp [zeroExtend, Set.indicator_of_mem hL]
  · simp [zeroExtend, Set.indicator_of_notMem hL]

/-- **Theorem 1, the `L²` bound.**  The retarded half-line transgression obeys Young's
`L¹ ⋆ L² → L²` inequality. -/
theorem lintegral_enorm_sq_halfLineConvMinus_le {k f : ℝ → ℂ}
    (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ x, ‖halfLineConvMinus k f x‖ₑ ^ 2)
      ≤ (∫⁻ y, ‖k y‖ₑ) ^ 2 * ∫⁻ L in Ioi (0 : ℝ), ‖f L‖ₑ ^ 2 := by
  have hfe : Measurable (zeroExtend f) := hf.indicator measurableSet_Ioi
  have hbound : ∀ x : ℝ,
      ‖halfLineConvMinus k f x‖ₑ ≤ ∫⁻ y, ‖k y‖ₑ * ‖zeroExtend f (x - y)‖ₑ := by
    intro x
    rw [halfLineConvMinus_eq_lineConv]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    have hcongr : (∫⁻ L, ‖k (x - L) * zeroExtend f L‖ₑ)
        = ∫⁻ L, ‖k (x - L)‖ₑ * ‖zeroExtend f L‖ₑ :=
      lintegral_congr fun L => enorm_mul _ _
    rw [hcongr]
    have hsub := MeasureTheory.lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun L : ℝ => ‖k (x - L)‖ₑ * ‖zeroExtend f L‖ₑ) x
    rw [← hsub]
    refine le_of_eq (lintegral_congr fun y => ?_)
    rw [show x - (x - y) = y by ring]
  have hmain := GaloisForLFunctions.HTGeometry.lintegral_enorm_sq_le_of_convolution_bound
    hk.enorm hfe.enorm hbound
  refine le_trans hmain (le_of_eq ?_)
  congr 1
  rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [zeroExtend, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [zeroExtend, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- **Theorem 1 for the advanced operator.** -/
theorem lintegral_enorm_sq_halfLineConvPlus_le {k f : ℝ → ℂ}
    (hkeven : ∀ x : ℝ, k (-x) = k x) (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ x, ‖halfLineConvPlus k f x‖ₑ ^ 2)
      ≤ (∫⁻ y, ‖k y‖ₑ) ^ 2 * ∫⁻ L in Ioi (0 : ℝ), ‖f L‖ₑ ^ 2 := by
  have hrefl : (∫⁻ x, ‖halfLineConvPlus k f x‖ₑ ^ 2)
      = ∫⁻ x, ‖halfLineConvMinus k f x‖ₑ ^ 2 := by
    have hcongr : (fun x : ℝ => ‖halfLineConvPlus k f x‖ₑ ^ 2)
        = fun x : ℝ => ‖halfLineConvMinus k f (-x)‖ₑ ^ 2 := by
      funext x
      rw [halfLineConvPlus_eq_halfLineConvMinus_neg hkeven]
    rw [hcongr]
    exact MeasureTheory.lintegral_neg_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => ‖halfLineConvMinus k f x‖ₑ ^ 2)
  rw [hrefl]
  exact lintegral_enorm_sq_halfLineConvMinus_le hk hf

/-! ### Theorem 2: the exact boundary defect -/

/-- Half-line integration by parts for the retarded kernel: differentiating the kernel costs
exactly the endpoint trace at the origin. -/
theorem halfLineConvMinus_deriv {k kp f fp : ℝ → ℂ} (x : ℝ)
    (hk : ∀ y : ℝ, HasDerivAt k (kp y) y)
    (hf : ∀ L : ℝ, HasDerivAt f (fp L) L)
    (hint₁ : IntegrableOn (fun L : ℝ => kp (x - L) * f L) (Ioi (0 : ℝ)))
    (hint₂ : IntegrableOn (fun L : ℝ => k (x - L) * fp L) (Ioi (0 : ℝ)))
    (hlim : Filter.Tendsto (fun L : ℝ => k (x - L) * f L) Filter.atTop (nhds 0)) :
    halfLineConvMinus k fp x = -(k x * f 0) + halfLineConvMinus kp f x := by
  have hFderiv : ∀ L : ℝ, HasDerivAt (fun L : ℝ => k (x - L) * f L)
      (k (x - L) * fp L - kp (x - L) * f L) L := by
    intro L
    have hshift : HasDerivAt (fun L : ℝ => x - L) (-1) L := by
      simpa using (hasDerivAt_id L).const_sub x
    have hcomp : HasDerivAt (fun L : ℝ => k (x - L)) (-(kp (x - L))) L := by
      simpa [Function.comp_def] using (hk (x - L)).scomp L hshift
    have h := hcomp.mul (hf L)
    have heq : (-(kp (x - L))) * f L + k (x - L) * fp L
        = k (x - L) * fp L - kp (x - L) * f L := by ring
    rwa [heq] at h
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun L : ℝ => k (x - L) * f L)
    (f' := fun L : ℝ => k (x - L) * fp L - kp (x - L) * f L) (a := (0 : ℝ))
    ((hFderiv 0).continuousAt.continuousWithinAt)
    (fun L _ => hFderiv L) (hint₂.sub hint₁) hlim
  rw [MeasureTheory.integral_sub hint₂ hint₁] at hmain
  rw [halfLineConvMinus, halfLineConvMinus]
  simp only [sub_zero, zero_sub] at hmain
  linear_combination hmain

/-- Half-line integration by parts for the advanced kernel. -/
theorem halfLineConvPlus_deriv {k kp f fp : ℝ → ℂ} (x : ℝ)
    (hk : ∀ y : ℝ, HasDerivAt k (kp y) y)
    (hf : ∀ L : ℝ, HasDerivAt f (fp L) L)
    (hint₁ : IntegrableOn (fun L : ℝ => kp (x + L) * f L) (Ioi (0 : ℝ)))
    (hint₂ : IntegrableOn (fun L : ℝ => k (x + L) * fp L) (Ioi (0 : ℝ)))
    (hlim : Filter.Tendsto (fun L : ℝ => k (x + L) * f L) Filter.atTop (nhds 0)) :
    halfLineConvPlus k fp x = -(k x * f 0) - halfLineConvPlus kp f x := by
  have hFderiv : ∀ L : ℝ, HasDerivAt (fun L : ℝ => k (x + L) * f L)
      (kp (x + L) * f L + k (x + L) * fp L) L := by
    intro L
    have hshift : HasDerivAt (fun L : ℝ => x + L) 1 L := by
      simpa using (hasDerivAt_id L).const_add x
    have hcomp : HasDerivAt (fun L : ℝ => k (x + L)) (kp (x + L)) L := by
      simpa [Function.comp_def] using (hk (x + L)).scomp L hshift
    exact hcomp.mul (hf L)
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun L : ℝ => k (x + L) * f L)
    (f' := fun L : ℝ => kp (x + L) * f L + k (x + L) * fp L) (a := (0 : ℝ))
    ((hFderiv 0).continuousAt.continuousWithinAt)
    (fun L _ => hFderiv L) (hint₁.add hint₂) hlim
  rw [MeasureTheory.integral_add hint₁ hint₂] at hmain
  rw [halfLineConvPlus, halfLineConvPlus]
  simp only [add_zero, zero_sub] at hmain
  linear_combination hmain

/-- **Equation (4), first identity: `∂_x C f = S (f')`.**  Differentiating the kernel of the even
half is the odd half applied to the derivative: the two endpoint traces cancel. -/
theorem halfLineConvEven_kernelDeriv {k kp f fp : ℝ → ℂ} (x : ℝ)
    (hk : ∀ y : ℝ, HasDerivAt k (kp y) y)
    (hf : ∀ L : ℝ, HasDerivAt f (fp L) L)
    (hm₁ : IntegrableOn (fun L : ℝ => kp (x - L) * f L) (Ioi (0 : ℝ)))
    (hm₂ : IntegrableOn (fun L : ℝ => k (x - L) * fp L) (Ioi (0 : ℝ)))
    (hmlim : Filter.Tendsto (fun L : ℝ => k (x - L) * f L) Filter.atTop (nhds 0))
    (hp₁ : IntegrableOn (fun L : ℝ => kp (x + L) * f L) (Ioi (0 : ℝ)))
    (hp₂ : IntegrableOn (fun L : ℝ => k (x + L) * fp L) (Ioi (0 : ℝ)))
    (hplim : Filter.Tendsto (fun L : ℝ => k (x + L) * f L) Filter.atTop (nhds 0)) :
    halfLineConvEven kp f x = halfLineConvOdd k fp x := by
  rw [halfLineConvEven, halfLineConvOdd,
    halfLineConvMinus_deriv x hk hf hm₁ hm₂ hmlim,
    halfLineConvPlus_deriv x hk hf hp₁ hp₂ hplim]
  ring

/-- **Equation (4), second identity: `∂_x S f = k · f 0 + C (f')`.**  Differentiating the kernel of
the odd half adds the two endpoint traces, producing the rank-one theta defect. -/
theorem halfLineConvOdd_kernelDeriv {k kp f fp : ℝ → ℂ} (x : ℝ)
    (hk : ∀ y : ℝ, HasDerivAt k (kp y) y)
    (hf : ∀ L : ℝ, HasDerivAt f (fp L) L)
    (hm₁ : IntegrableOn (fun L : ℝ => kp (x - L) * f L) (Ioi (0 : ℝ)))
    (hm₂ : IntegrableOn (fun L : ℝ => k (x - L) * fp L) (Ioi (0 : ℝ)))
    (hmlim : Filter.Tendsto (fun L : ℝ => k (x - L) * f L) Filter.atTop (nhds 0))
    (hp₁ : IntegrableOn (fun L : ℝ => kp (x + L) * f L) (Ioi (0 : ℝ)))
    (hp₂ : IntegrableOn (fun L : ℝ => k (x + L) * fp L) (Ioi (0 : ℝ)))
    (hplim : Filter.Tendsto (fun L : ℝ => k (x + L) * f L) Filter.atTop (nhds 0)) :
    halfLineConvOdd kp f x = k x * f 0 + halfLineConvEven k fp x := by
  rw [halfLineConvOdd, halfLineConvEven,
    halfLineConvMinus_deriv x hk hf hm₁ hm₂ hmlim,
    halfLineConvPlus_deriv x hk hf hp₁ hp₂ hplim]
  ring

/-! ### Theorem 4: the exact `L²` wall for the canonical input -/

/-- The canonical half-line input `f_λ(L) = exp(−λL)` of equation (7). -/
def canonicalHalfLineInput (lam : ℂ) (L : ℝ) : ℂ := Complex.exp (-(lam * (L : ℂ)))

theorem norm_canonicalHalfLineInput (lam : ℂ) (L : ℝ) :
    ‖canonicalHalfLineInput lam L‖ = Real.exp (-(lam.re * L)) := by
  rw [canonicalHalfLineInput, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

/-- **Equation (13): the exact `L²` norm of the canonical input.**  It is finite precisely because
`re λ > 0`, i.e. precisely on the half `re ρ > 1/2`. -/
theorem integral_norm_sq_canonicalHalfLineInput {lam : ℂ} (h : 0 < lam.re) :
    (∫ L : ℝ in Ioi (0 : ℝ), ‖canonicalHalfLineInput lam L‖ ^ 2) = 1 / (2 * lam.re) := by
  have hpos : 0 < 2 * lam.re := by linarith
  set a : ℝ := 2 * lam.re with ha
  have hfun : ∀ L : ℝ, ‖canonicalHalfLineInput lam L‖ ^ 2 = Real.exp (-(a * L)) := by
    intro L
    rw [norm_canonicalHalfLineInput, ← Real.exp_nat_mul]
    congr 1
    rw [ha]
    ring
  have hFderiv : ∀ L : ℝ,
      HasDerivAt (fun L : ℝ => -(Real.exp (-(a * L)) / a)) (Real.exp (-(a * L))) L := by
    intro L
    have hinner : HasDerivAt (fun L : ℝ => -(a * L)) (-a) L := by
      simpa [neg_mul] using (hasDerivAt_id L).const_mul (-a)
    have hexp : HasDerivAt (fun L : ℝ => Real.exp (-(a * L)))
        (Real.exp (-(a * L)) * (-a)) L := hinner.exp
    have := (hexp.div_const a).neg
    have heq : -(Real.exp (-(a * L)) * (-a) / a) = Real.exp (-(a * L)) := by
      field_simp
    rwa [heq] at this
  have hlim : Filter.Tendsto (fun L : ℝ => -(Real.exp (-(a * L)) / a)) Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun L : ℝ => Real.exp (-(a * L))) Filter.atTop (nhds 0) := by
      have hmul : Filter.Tendsto (fun L : ℝ => -(a * L)) Filter.atTop Filter.atBot := by
        have h1 : Filter.Tendsto (fun L : ℝ => a * L) Filter.atTop Filter.atTop :=
          Filter.Tendsto.const_mul_atTop hpos Filter.tendsto_id
        exact Filter.tendsto_neg_atTop_atBot.comp h1
      exact Real.tendsto_exp_atBot.comp hmul
    simpa using (hexp.div_const a).neg
  have hint : IntegrableOn (fun L : ℝ => Real.exp (-(a * L))) (Ioi (0 : ℝ)) := by
    simpa using (exp_neg_integrableOn_Ioi (0 : ℝ) hpos)
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun L : ℝ => -(Real.exp (-(a * L)) / a))
    (f' := fun L : ℝ => Real.exp (-(a * L))) (a := (0 : ℝ))
    ((hFderiv 0).continuousAt.continuousWithinAt) (fun L _ => hFderiv L) hint hlim
  have hcongr : (∫ L : ℝ in Ioi (0 : ℝ), ‖canonicalHalfLineInput lam L‖ ^ 2)
      = ∫ L : ℝ in Ioi (0 : ℝ), Real.exp (-(a * L)) :=
    MeasureTheory.integral_congr_ae (.of_forall hfun)
  rw [hcongr, hmain]
  simp [ha]

end RHTower
