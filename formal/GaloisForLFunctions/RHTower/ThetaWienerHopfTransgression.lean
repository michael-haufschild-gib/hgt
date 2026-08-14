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


/-! ### Theorem 3: the zero specialization is the reflection fold -/

/-- The physical reflection-fold primitive attached to a kernel and a spectral parameter. -/
def foldPrimitive (lam : ℂ) (k : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(lam * (x : ℂ))) * ∫ y in Iio x, Complex.exp (lam * (y : ℂ)) * k y

theorem halfLineConvPlus_eq_lineConv (k f : ℝ → ℂ) (x : ℝ) :
    halfLineConvPlus k f x = ∫ L : ℝ, k (x + L) * zeroExtend f L := by
  rw [halfLineConvPlus, ← MeasureTheory.integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (.of_forall fun L => ?_)
  by_cases hL : L ∈ Ioi (0 : ℝ)
  · simp [zeroExtend, Set.indicator_of_mem hL]
  · simp [zeroExtend, Set.indicator_of_notMem hL]

/-- **Equation `(8)`.**  The retarded transgression of the canonical exponential input is the
reflection-fold primitive. -/
theorem halfLineConvMinus_canonicalHalfLineInput (k : ℝ → ℂ) (lam : ℂ) (x : ℝ) :
    halfLineConvMinus k (canonicalHalfLineInput lam) x = foldPrimitive lam k x := by
  have hshift := integral_sub_left_eq_self
    (fun y : ℝ => k y * zeroExtend (canonicalHalfLineInput lam) (x - y)) volume x
  have hcongr : ∀ L : ℝ,
      k (x - L) * zeroExtend (canonicalHalfLineInput lam) L
        = k (x - L) * zeroExtend (canonicalHalfLineInput lam) (x - (x - L)) := by
    intro L
    congr 2
    ring
  rw [halfLineConvMinus_eq_lineConv]
  simp only [hcongr]
  rw [hshift]
  have hind : ∀ y : ℝ, k y * zeroExtend (canonicalHalfLineInput lam) (x - y)
      = (Iio x).indicator
        (fun y : ℝ => Complex.exp (-(lam * (x : ℂ))) * (Complex.exp (lam * (y : ℂ)) * k y)) y := by
    intro y
    by_cases hy : y ∈ Iio x
    · have hxy : x - y ∈ Ioi (0 : ℝ) := by
        simp only [Set.mem_Iio] at hy
        simp only [Set.mem_Ioi]
        linarith
      rw [Set.indicator_of_mem hy, zeroExtend, Set.indicator_of_mem hxy,
        canonicalHalfLineInput]
      have hexp : Complex.exp (-(lam * ((x - y : ℝ) : ℂ)))
          = Complex.exp (-(lam * (x : ℂ))) * Complex.exp (lam * (y : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    · have hxy : x - y ∉ Ioi (0 : ℝ) := by
        simp only [Set.mem_Iio, not_lt] at hy
        simp only [Set.mem_Ioi, not_lt]
        linarith
      rw [Set.indicator_of_notMem hy, zeroExtend, Set.indicator_of_notMem hxy, mul_zero]
  simp only [hind]
  rw [MeasureTheory.integral_indicator measurableSet_Iio,
    MeasureTheory.integral_const_mul, foldPrimitive]

/-- The advanced transgression of the canonical exponential input, before the zero condition. -/
theorem halfLineConvPlus_canonicalHalfLineInput_eq (k : ℝ → ℂ) (lam : ℂ) (x : ℝ) :
    halfLineConvPlus k (canonicalHalfLineInput lam) x
      = Complex.exp (lam * (x : ℂ)) * ∫ y in Ioi x, Complex.exp (-(lam * (y : ℂ))) * k y := by
  have hshift := integral_add_left_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => k y * zeroExtend (canonicalHalfLineInput lam) (y - x)) x
  have hcongr : ∀ L : ℝ,
      k (x + L) * zeroExtend (canonicalHalfLineInput lam) L
        = k (x + L) * zeroExtend (canonicalHalfLineInput lam) (x + L - x) := by
    intro L
    congr 2
    ring
  rw [halfLineConvPlus_eq_lineConv]
  simp only [hcongr]
  rw [hshift]
  have hind : ∀ y : ℝ, k y * zeroExtend (canonicalHalfLineInput lam) (y - x)
      = (Ioi x).indicator
        (fun y : ℝ => Complex.exp (lam * (x : ℂ))
          * (Complex.exp (-(lam * (y : ℂ))) * k y)) y := by
    intro y
    by_cases hy : y ∈ Ioi x
    · have hxy : y - x ∈ Ioi (0 : ℝ) := by
        simp only [Set.mem_Ioi] at hy ⊢
        linarith
      rw [Set.indicator_of_mem hy, zeroExtend, Set.indicator_of_mem hxy,
        canonicalHalfLineInput]
      have hexp : Complex.exp (-(lam * ((y - x : ℝ) : ℂ)))
          = Complex.exp (lam * (x : ℂ)) * Complex.exp (-(lam * (y : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    · have hxy : y - x ∉ Ioi (0 : ℝ) := by
        simp only [Set.mem_Ioi, not_lt] at hy ⊢
        linarith
      rw [Set.indicator_of_notMem hy, zeroExtend, Set.indicator_of_notMem hxy, mul_zero]
  simp only [hind]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_const_mul]

/-- **Equation `(9)`.**  When the reflected theta transform vanishes at the spectral parameter, the
advanced transgression of the canonical input is minus the reflected fold primitive. -/
theorem halfLineConvPlus_canonicalHalfLineInput (k : ℝ → ℂ) (lam : ℂ) (x : ℝ)
    (hint : Integrable (fun y : ℝ => Complex.exp (-(lam * (y : ℂ))) * k y))
    (hvanish : (∫ y : ℝ, Complex.exp (-(lam * (y : ℂ))) * k y) = 0) :
    halfLineConvPlus k (canonicalHalfLineInput lam) x = -foldPrimitive (-lam) k x := by
  have hsplit := MeasureTheory.integral_add_compl (μ := (volume : Measure ℝ))
    (f := fun y : ℝ => Complex.exp (-(lam * (y : ℂ))) * k y) (s := Iio x)
    measurableSet_Iio hint
  rw [hvanish] at hsplit
  have hcompl : (Iio x)ᶜ = Ici x := by
    ext y
    simp
  rw [hcompl] at hsplit
  have hIci : (∫ y in Ici x, Complex.exp (-(lam * (y : ℂ))) * k y)
      = ∫ y in Ioi x, Complex.exp (-(lam * (y : ℂ))) * k y := by
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [hIci] at hsplit
  rw [halfLineConvPlus_canonicalHalfLineInput_eq, foldPrimitive]
  have hIoi : (∫ y in Ioi x, Complex.exp (-(lam * (y : ℂ))) * k y)
      = -∫ y in Iio x, Complex.exp (-(lam * (y : ℂ))) * k y := by
    linear_combination hsplit
  rw [hIoi]
  have hneg : ∀ y : ℝ, Complex.exp (-(lam * (y : ℂ))) = Complex.exp ((-lam) * (y : ℂ)) := by
    intro y
    congr 1
    ring
  simp only [hneg]
  have hx : Complex.exp (lam * (x : ℂ)) = Complex.exp (-((-lam) * (x : ℂ))) := by
    congr 1
    ring
  rw [hx]
  ring

/-- **Equation `(10)`, even half.**  The even transgression of the canonical input is the even
reflection fold. -/
theorem halfLineConvEven_canonicalHalfLineInput (k : ℝ → ℂ) (lam : ℂ) (x : ℝ)
    (hint : Integrable (fun y : ℝ => Complex.exp (-(lam * (y : ℂ))) * k y))
    (hvanish : (∫ y : ℝ, Complex.exp (-(lam * (y : ℂ))) * k y) = 0) :
    halfLineConvEven k (canonicalHalfLineInput lam) x
      = (foldPrimitive lam k x - foldPrimitive (-lam) k x) / 2 := by
  rw [halfLineConvEven, halfLineConvMinus_canonicalHalfLineInput,
    halfLineConvPlus_canonicalHalfLineInput k lam x hint hvanish]
  ring

/-- **Equation `(10)`, odd half.**  The odd transgression of the canonical input is the odd
reflection fold. -/
theorem halfLineConvOdd_canonicalHalfLineInput (k : ℝ → ℂ) (lam : ℂ) (x : ℝ)
    (hint : Integrable (fun y : ℝ => Complex.exp (-(lam * (y : ℂ))) * k y))
    (hvanish : (∫ y : ℝ, Complex.exp (-(lam * (y : ℂ))) * k y) = 0) :
    halfLineConvOdd k (canonicalHalfLineInput lam) x
      = (foldPrimitive lam k x + foldPrimitive (-lam) k x) / 2 := by
  rw [halfLineConvOdd, halfLineConvMinus_canonicalHalfLineInput,
    halfLineConvPlus_canonicalHalfLineInput k lam x hint hvanish]
  ring


/-! ### Equations `(11)` and `(12)`: the folded first- and second-order systems -/

theorem hasDerivAt_canonicalHalfLineInput (lam : ℂ) (L : ℝ) :
    HasDerivAt (canonicalHalfLineInput lam) (-lam * canonicalHalfLineInput lam L) L := by
  have hbase : HasDerivAt (fun L : ℝ => ((L : ℝ) : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
  have hinner : HasDerivAt (fun y : ℝ => -(lam * ((y : ℝ) : ℂ))) (-(lam * 1)) L :=
    (hbase.const_mul lam).neg
  have hexp := hinner.cexp
  have hval : Complex.exp (-(lam * ((L : ℝ) : ℂ))) * -(lam * 1)
      = -lam * canonicalHalfLineInput lam L := by
    rw [canonicalHalfLineInput]
    ring
  rw [hval] at hexp
  exact hexp

theorem halfLineConvMinus_const_mul (k f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    halfLineConvMinus k (fun L => c * f L) x = c * halfLineConvMinus k f x := by
  rw [halfLineConvMinus, halfLineConvMinus, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (.of_forall fun L => ?_)
  ring

theorem halfLineConvPlus_const_mul (k f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    halfLineConvPlus k (fun L => c * f L) x = c * halfLineConvPlus k f x := by
  rw [halfLineConvPlus, halfLineConvPlus, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (.of_forall fun L => ?_)
  ring

theorem halfLineConvEven_const_mul (k f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    halfLineConvEven k (fun L => c * f L) x = c * halfLineConvEven k f x := by
  rw [halfLineConvEven, halfLineConvEven, halfLineConvMinus_const_mul,
    halfLineConvPlus_const_mul]
  ring

theorem halfLineConvOdd_const_mul (k f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    halfLineConvOdd k (fun L => c * f L) x = c * halfLineConvOdd k f x := by
  rw [halfLineConvOdd, halfLineConvOdd, halfLineConvMinus_const_mul,
    halfLineConvPlus_const_mul]
  ring

variable {k kp : ℝ → ℂ} {lam : ℂ}

/-- **Equation `(11)`, first identity.**  Differentiating the kernel of the even fold multiplies the
odd fold by `-λ`. -/
theorem halfLineConvEven_kernelDeriv_canonical (x : ℝ)
    (hk : ∀ y : ℝ, HasDerivAt k (kp y) y)
    (hm₁ : IntegrableOn (fun L : ℝ => kp (x - L) * canonicalHalfLineInput lam L) (Ioi (0 : ℝ)))
    (hm₂ : IntegrableOn
      (fun L : ℝ => k (x - L) * (-lam * canonicalHalfLineInput lam L)) (Ioi (0 : ℝ)))
    (hmlim : Filter.Tendsto (fun L : ℝ => k (x - L) * canonicalHalfLineInput lam L)
      Filter.atTop (nhds 0))
    (hp₁ : IntegrableOn (fun L : ℝ => kp (x + L) * canonicalHalfLineInput lam L) (Ioi (0 : ℝ)))
    (hp₂ : IntegrableOn
      (fun L : ℝ => k (x + L) * (-lam * canonicalHalfLineInput lam L)) (Ioi (0 : ℝ)))
    (hplim : Filter.Tendsto (fun L : ℝ => k (x + L) * canonicalHalfLineInput lam L)
      Filter.atTop (nhds 0)) :
    halfLineConvEven kp (canonicalHalfLineInput lam) x
      = -lam * halfLineConvOdd k (canonicalHalfLineInput lam) x := by
  have h := halfLineConvEven_kernelDeriv (k := k) (kp := kp)
    (f := canonicalHalfLineInput lam)
    (fp := fun L => -lam * canonicalHalfLineInput lam L) x hk
    (fun L => hasDerivAt_canonicalHalfLineInput lam L) hm₁ hm₂ hmlim hp₁ hp₂ hplim
  rw [h, halfLineConvOdd_const_mul]

/-- **Equation `(11)`, second identity.**  Differentiating the kernel of the odd fold produces the
rank-one theta source plus `-λ` times the even fold. -/
theorem halfLineConvOdd_kernelDeriv_canonical (x : ℝ)
    (hk : ∀ y : ℝ, HasDerivAt k (kp y) y)
    (hm₁ : IntegrableOn (fun L : ℝ => kp (x - L) * canonicalHalfLineInput lam L) (Ioi (0 : ℝ)))
    (hm₂ : IntegrableOn
      (fun L : ℝ => k (x - L) * (-lam * canonicalHalfLineInput lam L)) (Ioi (0 : ℝ)))
    (hmlim : Filter.Tendsto (fun L : ℝ => k (x - L) * canonicalHalfLineInput lam L)
      Filter.atTop (nhds 0))
    (hp₁ : IntegrableOn (fun L : ℝ => kp (x + L) * canonicalHalfLineInput lam L) (Ioi (0 : ℝ)))
    (hp₂ : IntegrableOn
      (fun L : ℝ => k (x + L) * (-lam * canonicalHalfLineInput lam L)) (Ioi (0 : ℝ)))
    (hplim : Filter.Tendsto (fun L : ℝ => k (x + L) * canonicalHalfLineInput lam L)
      Filter.atTop (nhds 0)) :
    halfLineConvOdd kp (canonicalHalfLineInput lam) x
      = k x - lam * halfLineConvEven k (canonicalHalfLineInput lam) x := by
  have h := halfLineConvOdd_kernelDeriv (k := k) (kp := kp)
    (f := canonicalHalfLineInput lam)
    (fp := fun L => -lam * canonicalHalfLineInput lam L) x hk
    (fun L => hasDerivAt_canonicalHalfLineInput lam L) hm₁ hm₂ hmlim hp₁ hp₂ hplim
  rw [h, halfLineConvEven_const_mul]
  have h0 : canonicalHalfLineInput lam 0 = 1 := by
    simp [canonicalHalfLineInput]
  rw [h0]
  ring


/-- The differentiability, integrability and decay conditions that make half-line integration by
parts valid for a kernel pair at a point, against the canonical exponential input. -/
structure KernelPairAdmissible (k kp : ℝ → ℂ) (lam : ℂ) (x : ℝ) : Prop where
  /-- `kp` is the derivative of `k`. -/
  deriv : ∀ y : ℝ, HasDerivAt k (kp y) y
  /-- The retarded derivative-kernel pairing is integrable. -/
  intMinus₁ :
    IntegrableOn (fun L : ℝ => kp (x - L) * canonicalHalfLineInput lam L) (Ioi (0 : ℝ))
  /-- The retarded kernel pairing with the input derivative is integrable. -/
  intMinus₂ : IntegrableOn
    (fun L : ℝ => k (x - L) * (-lam * canonicalHalfLineInput lam L)) (Ioi (0 : ℝ))
  /-- The retarded boundary term decays. -/
  limMinus : Filter.Tendsto (fun L : ℝ => k (x - L) * canonicalHalfLineInput lam L)
    Filter.atTop (nhds 0)
  /-- The advanced derivative-kernel pairing is integrable. -/
  intPlus₁ :
    IntegrableOn (fun L : ℝ => kp (x + L) * canonicalHalfLineInput lam L) (Ioi (0 : ℝ))
  /-- The advanced kernel pairing with the input derivative is integrable. -/
  intPlus₂ : IntegrableOn
    (fun L : ℝ => k (x + L) * (-lam * canonicalHalfLineInput lam L)) (Ioi (0 : ℝ))
  /-- The advanced boundary term decays. -/
  limPlus : Filter.Tendsto (fun L : ℝ => k (x + L) * canonicalHalfLineInput lam L)
    Filter.atTop (nhds 0)

theorem KernelPairAdmissible.even_kernelDeriv {k kp : ℝ → ℂ} {lam : ℂ} {x : ℝ}
    (h : KernelPairAdmissible k kp lam x) :
    halfLineConvEven kp (canonicalHalfLineInput lam) x
      = -lam * halfLineConvOdd k (canonicalHalfLineInput lam) x :=
  halfLineConvEven_kernelDeriv_canonical x h.deriv h.intMinus₁ h.intMinus₂ h.limMinus
    h.intPlus₁ h.intPlus₂ h.limPlus

theorem KernelPairAdmissible.odd_kernelDeriv {k kp : ℝ → ℂ} {lam : ℂ} {x : ℝ}
    (h : KernelPairAdmissible k kp lam x) :
    halfLineConvOdd kp (canonicalHalfLineInput lam) x
      = k x - lam * halfLineConvEven k (canonicalHalfLineInput lam) x :=
  halfLineConvOdd_kernelDeriv_canonical x h.deriv h.intMinus₁ h.intMinus₂ h.limMinus
    h.intPlus₁ h.intPlus₂ h.limPlus

/-- **Equation `(12)`, even half.**  The even fold satisfies the forced second-order equation whose
source is the theta kernel itself. -/
theorem halfLineConvEven_kernelSecondDeriv {k kp kpp : ℝ → ℂ} {lam : ℂ} {x : ℝ}
    (h₁ : KernelPairAdmissible k kp lam x) (h₂ : KernelPairAdmissible kp kpp lam x) :
    halfLineConvEven kpp (canonicalHalfLineInput lam) x
      = lam ^ 2 * halfLineConvEven k (canonicalHalfLineInput lam) x - lam * k x := by
  rw [h₂.even_kernelDeriv, h₁.odd_kernelDeriv]
  ring

/-- **Equation `(12)`, odd half.**  The odd fold satisfies the forced second-order equation whose
source is the derivative of the theta kernel. -/
theorem halfLineConvOdd_kernelSecondDeriv {k kp kpp : ℝ → ℂ} {lam : ℂ} {x : ℝ}
    (h₁ : KernelPairAdmissible k kp lam x) (h₂ : KernelPairAdmissible kp kpp lam x) :
    halfLineConvOdd kpp (canonicalHalfLineInput lam) x
      = lam ^ 2 * halfLineConvOdd k (canonicalHalfLineInput lam) x + kp x := by
  rw [h₂.odd_kernelDeriv, h₁.even_kernelDeriv]
  ring

/-! ### Equation `(14)`: the trichotomy at the critical line -/

theorem integrableOn_norm_sq_canonicalHalfLineInput {lam : ℂ} (h : 0 < lam.re) :
    IntegrableOn (fun L : ℝ => ‖canonicalHalfLineInput lam L‖ ^ 2) (Ioi (0 : ℝ)) := by
  have hEq : ∀ L : ℝ, ‖canonicalHalfLineInput lam L‖ ^ 2 = Real.exp (-(2 * lam.re) * L) := by
    intro L
    rw [norm_canonicalHalfLineInput, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hint : IntegrableOn (fun L : ℝ => Real.exp (-(2 * lam.re) * L)) (Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  refine hint.congr_fun ?_ measurableSet_Ioi
  intro L _
  exact (hEq L).symm

/-- **Equation `(14)`, the wall.**  At or left of the critical line the canonical input leaves
`L²`: its square modulus is bounded below by one on the whole half-line. -/
theorem not_integrableOn_norm_sq_canonicalHalfLineInput {lam : ℂ} (h : lam.re ≤ 0) :
    ¬ IntegrableOn (fun L : ℝ => ‖canonicalHalfLineInput lam L‖ ^ 2) (Ioi (0 : ℝ)) := by
  intro hcon
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.mono hcon aestronglyMeasurable_const ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
    have hL0 : (0 : ℝ) < L := hL
    rw [norm_canonicalHalfLineInput]
    have hexp : (1 : ℝ) ≤ Real.exp (-(lam.re * L)) := by
      refine Real.one_le_exp ?_
      nlinarith
    have hnn : (0 : ℝ) ≤ Real.exp (-(lam.re * L)) := (Real.exp_pos _).le
    rw [norm_one, Real.norm_of_nonneg (by positivity)]
    nlinarith
  rw [MeasureTheory.integrableOn_const_iff] at hone
  rcases hone with hone | hone
  · simp at hone
  · rw [Real.volume_Ioi] at hone
    exact absurd hone (by simp)

/-- On the critical line the canonical input is bounded and oscillatory. -/
theorem norm_canonicalHalfLineInput_eq_one {lam : ℂ} (h : lam.re = 0) (L : ℝ) :
    ‖canonicalHalfLineInput lam L‖ = 1 := by
  rw [norm_canonicalHalfLineInput, h]
  simp

/-- Left of the critical line the canonical input grows without bound. -/
theorem tendsto_norm_canonicalHalfLineInput_atTop {lam : ℂ} (h : lam.re < 0) :
    Filter.Tendsto (fun L : ℝ => ‖canonicalHalfLineInput lam L‖) Filter.atTop Filter.atTop := by
  have hEq : ∀ L : ℝ, ‖canonicalHalfLineInput lam L‖ = Real.exp ((-lam.re) * L) := by
    intro L
    rw [norm_canonicalHalfLineInput]
    congr 1
    ring
  simp only [hEq]
  exact Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop (by linarith))


/-! ### The corollary: the elementary positive consumer -/

/-- The Neumann shape `c_λ(L) = cosh(λL)` of equation `(16)`. -/
def neumannShape (lam : ℂ) (L : ℝ) : ℂ := Complex.cosh (lam * (L : ℂ))

/-- The Dirichlet shape `s_λ(L) = sinh(λL)/λ`, with `s_0(L) = L`, of equation `(16)`. -/
def dirichletShape (lam : ℂ) (L : ℝ) : ℂ :=
  if lam = 0 then (L : ℂ) else Complex.sinh (lam * (L : ℂ)) / lam

theorem hasDerivAt_neumannShape (lam : ℂ) (L : ℝ) :
    HasDerivAt (neumannShape lam) (lam * Complex.sinh (lam * (L : ℂ))) L := by
  have hbase : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
  have hinner : HasDerivAt (fun y : ℝ => lam * ((y : ℝ) : ℂ)) (lam * 1) L := hbase.const_mul lam
  have hcomp := (Complex.hasDerivAt_cosh (lam * (L : ℂ))).scomp L hinner
  have hval : (lam * 1) • Complex.sinh (lam * (L : ℂ)) = lam * Complex.sinh (lam * (L : ℂ)) := by
    rw [smul_eq_mul, mul_one]
  rw [hval] at hcomp
  exact hcomp

theorem hasDerivAt_neumannShapeDeriv (lam : ℂ) (L : ℝ) :
    HasDerivAt (fun y : ℝ => lam * Complex.sinh (lam * (y : ℂ)))
      (lam ^ 2 * neumannShape lam L) L := by
  have hbase : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
  have hinner : HasDerivAt (fun y : ℝ => lam * ((y : ℝ) : ℂ)) (lam * 1) L := hbase.const_mul lam
  have hcomp := (Complex.hasDerivAt_sinh (lam * (L : ℂ))).scomp L hinner
  have hmul := hcomp.const_mul lam
  have hval : lam * ((lam * 1) • Complex.cosh (lam * (L : ℂ)))
      = lam ^ 2 * neumannShape lam L := by
    rw [smul_eq_mul, neumannShape]
    ring
  rw [hval] at hmul
  exact hmul

@[simp] theorem neumannShape_zero (lam : ℂ) : neumannShape lam 0 = 1 := by
  simp [neumannShape]

@[simp] theorem neumannShapeDeriv_zero (lam : ℂ) :
    lam * Complex.sinh (lam * ((0 : ℝ) : ℂ)) = 0 := by
  simp

theorem hasDerivAt_dirichletShape (lam : ℂ) (L : ℝ) :
    HasDerivAt (dirichletShape lam) (neumannShape lam L) L := by
  by_cases hlam : lam = 0
  · subst hlam
    have hbase : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
    have hfun : dirichletShape 0 = fun y : ℝ => ((y : ℝ) : ℂ) := by
      funext y
      simp [dirichletShape]
    rw [hfun, neumannShape]
    simpa using hbase
  · have hbase : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
    have hinner : HasDerivAt (fun y : ℝ => lam * ((y : ℝ) : ℂ)) (lam * 1) L := hbase.const_mul lam
    have hcomp := (Complex.hasDerivAt_sinh (lam * (L : ℂ))).scomp L hinner
    have hdiv := hcomp.div_const lam
    have hfun : dirichletShape lam = fun y : ℝ => Complex.sinh (lam * ((y : ℝ) : ℂ)) / lam := by
      funext y
      simp [dirichletShape, hlam]
    have hval : (lam * 1) • Complex.cosh (lam * (L : ℂ)) / lam = neumannShape lam L := by
      rw [smul_eq_mul, mul_one, neumannShape]
      field_simp
    rw [hfun]
    rw [hval] at hdiv
    exact hdiv

@[simp] theorem dirichletShape_zero (lam : ℂ) : dirichletShape lam 0 = 0 := by
  by_cases hlam : lam = 0 <;> simp [dirichletShape, hlam]

/-- **Equation `(17)`.**  The Neumann shape solves `-y'' = -λ²y` with `y(0) = 1`, `y'(0) = 0`, and
the Dirichlet shape solves the same equation with `y(0) = 0`, `y'(0) = 1`. -/
theorem dirichletShape_secondDeriv (lam : ℂ) (L : ℝ) :
    HasDerivAt (neumannShape lam) (lam ^ 2 * dirichletShape lam L) L := by
  by_cases hlam : lam = 0
  · subst hlam
    have hfun : neumannShape 0 = fun _ : ℝ => (1 : ℂ) := by
      funext y
      simp [neumannShape]
    rw [hfun]
    simpa using (hasDerivAt_const L (1 : ℂ))
  · have h := hasDerivAt_neumannShape lam L
    have hval : lam * Complex.sinh (lam * (L : ℂ)) = lam ^ 2 * dirichletShape lam L := by
      rw [dirichletShape, if_neg hlam]
      field_simp
    rwa [hval] at h

/-- On the critical line the Neumann shape is bounded. -/
theorem norm_neumannShape_le_one {lam : ℂ} (h : lam.re = 0) (L : ℝ) :
    ‖neumannShape lam L‖ ≤ 1 := by
  set b : ℝ := lam.im with hb
  have hlam : lam = (b : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [h, hb]
  have hval : neumannShape lam L = ((Real.cos (b * L) : ℝ) : ℂ) := by
    rw [neumannShape, hlam]
    rw [show ((b : ℂ) * Complex.I) * (L : ℂ) = ((b * L : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos]
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- Off the critical line the Neumann shape grows exponentially, so it is not tempered. -/
theorem tendsto_norm_neumannShape_atTop {lam : ℂ} (h : 0 < lam.re) :
    Filter.Tendsto (fun L : ℝ => ‖neumannShape lam L‖) Filter.atTop Filter.atTop := by
  have hlow : ∀ L : ℝ, 0 ≤ L →
      (Real.exp (lam.re * L) - Real.exp (-(lam.re * L))) / 2 ≤ ‖neumannShape lam L‖ := by
    intro L _
    have hcosh : neumannShape lam L
        = (Complex.exp (lam * (L : ℂ)) + Complex.exp (-(lam * (L : ℂ)))) / 2 := by
      rw [neumannShape]
      exact Complex.ext rfl rfl
    rw [hcosh, norm_div, Complex.norm_ofNat]
    have h1 : ‖Complex.exp (lam * (L : ℂ))‖ = Real.exp (lam.re * L) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    have h2 : ‖Complex.exp (-(lam * (L : ℂ)))‖ = Real.exp (-(lam.re * L)) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    have h3 : ‖Complex.exp (lam * (L : ℂ))‖ - ‖Complex.exp (-(lam * (L : ℂ)))‖
        ≤ ‖Complex.exp (lam * (L : ℂ)) + Complex.exp (-(lam * (L : ℂ)))‖ := by
      have := norm_sub_norm_le (Complex.exp (lam * (L : ℂ)))
        (-Complex.exp (-(lam * (L : ℂ))))
      simpa [sub_neg_eq_add] using this
    rw [h1, h2] at h3
    linarith [h3]
  have hexp1 : Filter.Tendsto (fun L : ℝ => Real.exp (lam.re * L)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop h)
  have hgrow : Filter.Tendsto (fun L : ℝ => (Real.exp (lam.re * L) + (-1)) / 2)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_atTop_add_const_right _ (-1) hexp1).atTop_div_const (by norm_num)
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hgrow
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with L hL
  have h2 : Real.exp (-(lam.re * L)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  linarith [hlow L hL]

end RHTower
