import GaloisForLFunctions.HTGeometry.MultiplicativeConvolutionDomain

/-!
# Lemma 5.1: the positive multiplicative measure algebra is a domain

The finite complex measures on `[0, 1]` without atom at `0` — the finite complex measures on
`(0, 1]` — form a subring `M((0,1])` of the convolution ring.

* The Mellin transform `z ↦ ⟨c, x^z⟩` is multiplicative under `⊠` and holomorphic on
  `Re z > 0`: the integrand `x^z` has `z`-derivative `x^z log x`, dominated by `1/a` on
  `Re z ≥ a > 0`.
* On the connected half-plane a product of holomorphic functions vanishes only if one factor
  does (identity theorem).
* A measure carried by `(0, 1]` is determined by its moments of order `n ≥ 1`: the measures
  `x dμ` share all moments.
* **Lemma 5.1**: `M((0,1])` has no zero divisors, hence is an integral domain.
* **Lemma 5.2**: over an integral domain, `∏ (T + aᵢ) = ∏ (T + bᵢ)` forces `{aᵢ} = {bᵢ}`.
-/

open MeasureTheory Complex Set Filter Topology Polynomial
open scoped ENNReal NNReal unitInterval

noncomputable section

namespace GaloisForLFunctions.HTGeometry.MeasureConvolution

/-! ### No atom at `0` -/

theorem ofMeasure_apply (μ : Measure I) [IsFiniteMeasure μ] {S : Set I} (hS : MeasurableSet S) :
    ofMeasure μ S = ((μ S).toReal : ℂ) := by
  rw [ofMeasure, SignedMeasure.toComplexMeasure_apply,
    Measure.toSignedMeasure_apply_measurable hS, measureReal_def]
  rfl

theorem jordan_singleton_zero (s : SignedMeasure I) (h : s {0} = 0) :
    s.toJordanDecomposition.posPart {0} = 0 ∧ s.toJordanDecomposition.negPart {0} = 0 := by
  have hs := congrArg (fun t : SignedMeasure I => t {0})
    (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
  simp only [JordanDecomposition.toSignedMeasure, FunLike.coe_sub, Pi.sub_apply,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton _), h,
    measureReal_def] at hs
  obtain ⟨S, hSm, hP, hN⟩ := s.toJordanDecomposition.mutuallySingular
  by_cases h0 : (0 : I) ∈ S
  · have hp : s.toJordanDecomposition.posPart {0} = 0 :=
      measure_mono_null (singleton_subset_iff.2 h0) hP
    rw [hp, ENNReal.toReal_zero, zero_sub, neg_eq_zero, ENNReal.toReal_eq_zero_iff] at hs
    exact ⟨hp, hs.resolve_right (measure_ne_top _ _)⟩
  · have hn : s.toJordanDecomposition.negPart {0} = 0 :=
      measure_mono_null (singleton_subset_iff.2 h0) hN
    rw [hn, ENNReal.toReal_zero, sub_zero, ENNReal.toReal_eq_zero_iff] at hs
    exact ⟨hs.resolve_right (measure_ne_top _ _), hn⟩

theorem jordanPart_singleton_zero {c : ComplexMeasure I} (h : c ({0} : Set I) = 0) (a : Fin 4) :
    jordanPart c a ({0} : Set I) = 0 := by
  have hre : ComplexMeasure.re c {0} = 0 := by
    rw [ComplexMeasure.re_apply, VectorMeasure.mapRange_apply, h]; rfl
  have him : ComplexMeasure.im c {0} = 0 := by
    rw [ComplexMeasure.im_apply, VectorMeasure.mapRange_apply, h]; rfl
  fin_cases a
  · exact (jordan_singleton_zero _ hre).1
  · exact (jordan_singleton_zero _ hre).2
  · exact (jordan_singleton_zero _ him).1
  · exact (jordan_singleton_zero _ him).2

theorem mconv_singleton_zero (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ({0} : Set I) = 0) (hν : ν ({0} : Set I) = 0) : (μ ∗ₘ ν) ({0} : Set I) = 0 := by
  rw [Measure.mconv, Measure.map_apply measurable_mul (measurableSet_singleton 0)]
  refine measure_mono_null (t := ({0} ×ˢ univ) ∪ (univ ×ˢ {0})) (fun p hp => ?_) ?_
  · simp only [mem_preimage, mem_singleton_iff] at hp
    have : (p.1 : ℝ) * p.2 = 0 := by
      have := congrArg Subtype.val hp
      rwa [Set.Icc.coe_mul] at this
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl ⟨Subtype.ext h, mem_univ _⟩
    · exact Or.inr ⟨mem_univ _, Subtype.ext h⟩
  · refine measure_union_null ?_ ?_ <;> rw [Measure.prod_prod] <;> simp [hμ, hν]

/-! ### The subring `M((0,1])` -/

theorem toMeasure_add (c d : ConvMeasure) :
    (c + d).toMeasure = c.toMeasure + d.toMeasure := rfl

theorem toMeasure_neg (c : ConvMeasure) : (-c).toMeasure = -c.toMeasure := rfl

theorem toMeasure_mul (c d : ConvMeasure) : (c * d).toMeasure = conv c.toMeasure d.toMeasure :=
  rfl

theorem toMeasure_one : (1 : ConvMeasure).toMeasure = ofMeasure (Measure.dirac (1 : I)) := rfl

theorem toMeasure_zero : (0 : ConvMeasure).toMeasure = 0 := rfl

theorem conv_singleton_zero {c d : ComplexMeasure I} (hc : c ({0} : Set I) = 0)
    (hd : d ({0} : Set I) = 0) : conv c d ({0} : Set I) = 0 := by
  rw [conv, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [FunLike.coe_smul, Pi.smul_apply, ofMeasure_apply _ (measurableSet_singleton 0),
    mconv_singleton_zero _ _ (jordanPart_singleton_zero hc _) (jordanPart_singleton_zero hd _)]
  simp

/-- **`M((0,1])`**: finite complex measures on `[0, 1]` without atom at `0`. -/
def positiveSupport : Subring ConvMeasure where
  carrier := {c | c.toMeasure ({0} : Set I) = 0}
  mul_mem' := by
    intro c d hc hd
    change (c * d).toMeasure ({0} : Set I) = 0
    rw [toMeasure_mul]
    exact conv_singleton_zero hc hd
  one_mem' := by
    change (1 : ConvMeasure).toMeasure ({0} : Set I) = 0
    rw [toMeasure_one, ofMeasure_apply _ (measurableSet_singleton 0), Measure.dirac_apply' _
      (measurableSet_singleton 0), indicator_of_notMem]
    · simp
    · simp only [mem_singleton_iff]
      exact fun h => by simpa using congrArg Subtype.val h
  add_mem' := by
    intro c d hc hd
    change (c + d).toMeasure ({0} : Set I) = 0
    rw [toMeasure_add, FunLike.coe_add, Pi.add_apply]
    rw [show c.toMeasure ({0} : Set I) = 0 from hc, show d.toMeasure ({0} : Set I) = 0 from hd,
      add_zero]
  zero_mem' := by
    change (0 : ConvMeasure).toMeasure ({0} : Set I) = 0
    rw [toMeasure_zero]; rfl
  neg_mem' := by
    intro c hc
    change (-c).toMeasure ({0} : Set I) = 0
    rw [toMeasure_neg, FunLike.coe_neg, Pi.neg_apply]
    rw [show c.toMeasure ({0} : Set I) = 0 from hc, neg_zero]

/-! ### The Mellin transform -/

/-- The Mellin test function `x ↦ x^z`. -/
def mellinTest (z : ℂ) (x : I) : ℂ := ((x : ℝ) : ℂ) ^ z

theorem isTest_mellinTest {z : ℂ} (hz : 0 < z.re) : IsTest (mellinTest z) := by
  refine ⟨((Complex.continuous_ofReal_cpow_const hz).comp continuous_subtype_val).measurable, 1,
    fun x => ?_⟩
  rw [mellinTest, Complex.norm_cpow_eq_rpow_re_of_nonneg x.2.1 hz.ne']
  exact Real.rpow_le_one x.2.1 x.2.2 hz.le

theorem isMultiplicative_mellinTest (z : ℂ) : IsMultiplicative (mellinTest z) := fun x y => by
  simp only [mellinTest, Set.Icc.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg x.2.1 y.2.1 z

/-- The Mellin transform `z ↦ ⟨c, x^z⟩`. -/
def mellin (c : ComplexMeasure I) (z : ℂ) : ℂ := pair c (mellinTest z)

theorem mellin_conv (c d : ComplexMeasure I) {z : ℂ} (hz : 0 < z.re) :
    mellin (conv c d) z = mellin c z * mellin d z :=
  pair_conv c d (isTest_mellinTest hz) (isMultiplicative_mellinTest z)

theorem mellin_natCast (c : ComplexMeasure I) (n : ℕ) : mellin c n = momentSeq c n := by
  have : mellinTest (n : ℂ) = powTest n := by
    funext x; simp only [mellinTest, powTest, Complex.cpow_natCast]
  rw [mellin, momentSeq, this]

theorem rpow_mul_neg_log_le {x a : ℝ} (hx0 : 0 < x) (ha : 0 < a) :
    x ^ a * (-Real.log x) ≤ 1 / a := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (-a))
  rw [Real.log_rpow hx0] at h
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hmul : x ^ a * x ^ (-a) = 1 := by
    rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
  rw [le_div_iff₀ ha]
  have : x ^ a * (-a * Real.log x) ≤ x ^ a * (x ^ (-a) - 1) := mul_le_mul_of_nonneg_left h hxa.le
  rw [mul_sub, hmul, mul_one] at this
  nlinarith

/-- The `z`-derivative `x^z log x` of the Mellin kernel is bounded by `1/a` on `Re z ≥ a`. -/
theorem norm_mellin_deriv_le {x : I} (hx : (x : ℝ) ≠ 0) {z : ℂ} {a : ℝ} (ha : 0 < a)
    (hz : a ≤ z.re) : ‖mellinTest z x * Complex.log ((x : ℝ) : ℂ)‖ ≤ 1 / a := by
  have hx0 : 0 < (x : ℝ) := lt_of_le_of_ne x.2.1 (Ne.symm hx)
  rw [norm_mul, mellinTest, Complex.norm_cpow_eq_rpow_re_of_pos hx0, ← Complex.ofReal_log hx0.le,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hx0.le x.2.2)]
  calc (x : ℝ) ^ z.re * -Real.log x ≤ (x : ℝ) ^ a * -Real.log x :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hx0 x.2.2 hz)
          (neg_nonneg.2 (Real.log_nonpos hx0.le x.2.2))
    _ ≤ 1 / a := rpow_mul_neg_log_le hx0 ha

/-- The Mellin transform of a finite measure without atom at `0` is holomorphic on `Re z > 0`. -/
theorem differentiableOn_integral_mellinTest (μ : Measure I) [IsFiniteMeasure μ]
    (hμ : μ ({0} : Set I) = 0) :
    DifferentiableOn ℂ (fun z => ∫ x, mellinTest z x ∂μ) {z | 0 < z.re} := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.re := hz₀
  set a := z₀.re / 2 with ha_def
  have ha : 0 < a := by positivity
  have hae : ∀ᵐ (x : I) ∂μ, (x : ℝ) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hμ
    simp only [ne_eq, not_not, mem_setOf_eq] at hx
    exact Subtype.ext hx
  have hball : ∀ z ∈ Metric.ball z₀ a, a ≤ z.re := fun z hz => by
    have h1 : |z.re - z₀.re| < a := by
      have := Complex.abs_re_le_norm (z - z₀)
      rw [Metric.mem_ball, dist_eq_norm] at hz
      simp only [Complex.sub_re] at this
      linarith
    rw [abs_lt] at h1
    linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z x => mellinTest z x) (F' := fun z x => mellinTest z x * Complex.log ((x : ℝ) : ℂ))
    (x₀ := z₀) (bound := fun _ => 1 / a) (Metric.ball_mem_nhds z₀ ha)
    (Eventually.of_forall fun z => by
      refine (Measurable.aestronglyMeasurable ?_)
      exact (Complex.measurable_ofReal.comp measurable_subtype_coe).pow_const z)
    ((isTest_mellinTest hz₀').integrable μ)
    ((((Complex.measurable_ofReal.comp measurable_subtype_coe).pow_const z₀).mul
      (Complex.measurable_log.comp
        (Complex.measurable_ofReal.comp measurable_subtype_coe))).aestronglyMeasurable)
    (by
      filter_upwards [hae] with x hx z hz
      exact norm_mellin_deriv_le hx ha (hball z hz))
    (integrable_const _)
    (by
      filter_upwards [hae] with x hx z _
      exact (Complex.hasStrictDerivAt_const_cpow (Or.inl (by exact_mod_cast hx))).hasDerivAt)
  exact hderiv.2.differentiableAt.differentiableWithinAt

theorem isOpen_rightHalfPlane : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane : IsPreconnected {z : ℂ | 0 < z.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected

theorem analyticOnNhd_mellin {c : ComplexMeasure I} (hc : c ({0} : Set I) = 0) :
    AnalyticOnNhd ℂ (mellin c) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_rightHalfPlane
  have : mellin c = fun z => ∑ a, jordanWeight a * ∫ x, mellinTest z x ∂jordanPart c a := rfl
  rw [this]
  exact DifferentiableOn.fun_sum fun a _ => (differentiableOn_integral_mellinTest _
    (jordanPart_singleton_zero hc a)).const_mul _

/-- On a connected open set, a product of holomorphic functions vanishes only if a factor does. -/
theorem eqOn_zero_or_eqOn_zero_of_mul {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hU : IsOpen U) (hUc : IsPreconnected U)
    (h : ∀ z ∈ U, f z * g z = 0) : EqOn f 0 U ∨ EqOn g 0 U := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hf0, hg0⟩ := hcon
  obtain ⟨z₀, hz₀, hfz₀⟩ : ∃ z₀ ∈ U, f z₀ ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hf0 fun z hz => hall z hz
  have hnear : ∀ᶠ z in 𝓝 z₀, f z ≠ 0 ∧ z ∈ U :=
    ((hf z₀ hz₀).continuousAt.eventually_ne hfz₀).and (hU.mem_nhds hz₀)
  have hgnear : ∀ᶠ z in 𝓝 z₀, g z = 0 := hnear.mono fun z hz =>
    (mul_eq_zero.1 (h z hz.2)).resolve_left hz.1
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, g z = 0 :=
    (hgnear.filter_mono nhdsWithin_le_nhds).frequently
  exact hg0 (hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hfreq)

/-! ### Determinacy on `(0, 1]` -/

/-- A finite measure on `[0, 1]` without atom at `0` is determined by its moments of order
`n ≥ 1`. -/
theorem measure_eq_of_moments_succ_eq (μ ν : Measure I) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ({0} : Set I) = 0) (hν : ν ({0} : Set I) = 0)
    (h : ∀ n : ℕ, ∫ x, (x : ℝ) ^ (n + 1) ∂μ = ∫ x, (x : ℝ) ^ (n + 1) ∂ν) : μ = ν := by
  let f : I → ℝ≥0 := fun x => Real.toNNReal x
  have hf : Measurable f := measurable_subtype_coe.real_toNNReal
  have hfin : ∀ ρ : Measure I, [IsFiniteMeasure ρ] → IsFiniteMeasure (ρ.withDensity
      fun x => (f x : ℝ≥0∞)) := fun ρ _ => by
    refine isFiniteMeasure_withDensity ?_
    refine ne_top_of_le_ne_top (measure_ne_top ρ univ) ?_
    calc ∫⁻ x, (f x : ℝ≥0∞) ∂ρ ≤ ∫⁻ _, 1 ∂ρ := lintegral_mono fun x => by
          simp only [f, ENNReal.coe_le_one_iff]
          exact Real.toNNReal_le_one.2 x.2.2
      _ = ρ univ := by simp
  have hmom : ∀ (ρ : Measure I) [IsFiniteMeasure ρ] (n : ℕ),
      ∫ x, (x : ℝ) ^ n ∂(ρ.withDensity fun x => (f x : ℝ≥0∞)) = ∫ x, (x : ℝ) ^ (n + 1) ∂ρ := by
    intro ρ _ n
    rw [integral_withDensity_eq_integral_smul hf]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [f, NNReal.smul_def, Real.coe_toNNReal _ x.2.1, smul_eq_mul, pow_succ]
    ring
  haveI := hfin μ
  haveI := hfin ν
  have hw : μ.withDensity (fun x => (f x : ℝ≥0∞)) = ν.withDensity (fun x => (f x : ℝ≥0∞)) :=
    measure_eq_of_moments_eq _ _ fun n => by rw [hmom μ n, hmom ν n, h]
  let g : I → ℝ≥0∞ := fun x => ((f x : ℝ≥0∞))⁻¹
  have hg : Measurable g := (measurable_coe_nnreal_ennreal.comp hf).inv
  have hrec : ∀ ρ : Measure I, ρ ({0} : Set I) = 0 →
      (ρ.withDensity fun x => (f x : ℝ≥0∞)).withDensity g = ρ := fun ρ hρ => by
    rw [← withDensity_mul ρ hf.coe_nnreal_ennreal hg]
    conv_rhs => rw [← withDensity_one (μ := ρ)]
    refine withDensity_congr_ae ?_
    have hae : ∀ᵐ (x : I) ∂ρ, (x : ℝ) ≠ 0 := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hρ
      simp only [ne_eq, not_not, mem_setOf_eq] at hx
      exact Subtype.ext hx
    filter_upwards [hae] with x hx
    have hx0 : 0 < (x : ℝ) := lt_of_le_of_ne x.2.1 (Ne.symm hx)
    have hfx : (f x : ℝ≥0∞) ≠ 0 := by
      simp only [f, ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]; exact hx0
    simp only [Pi.mul_apply, g, Pi.one_apply]
    exact ENNReal.mul_inv_cancel hfx ENNReal.coe_ne_top
  rw [← hrec μ hμ, ← hrec ν hν, hw]

/-- A complex measure without atom at `0` whose moments of order `n ≥ 1` vanish is zero. -/
theorem eq_zero_of_momentSeq_succ {c : ComplexMeasure I} (hc : c ({0} : Set I) = 0)
    (h : ∀ n : ℕ, momentSeq c (n + 1) = 0) : c = 0 := by
  have hre : jordanPart c 0 = jordanPart c 1 :=
    measure_eq_of_moments_succ_eq _ _ (jordanPart_singleton_zero hc 0)
      (jordanPart_singleton_zero hc 1) fun n => (ofReal_integral_jordan_eq c _ (h n)).1
  have him : jordanPart c 2 = jordanPart c 3 :=
    measure_eq_of_moments_succ_eq _ _ (jordanPart_singleton_zero hc 2)
      (jordanPart_singleton_zero hc 3) fun n => (ofReal_integral_jordan_eq c _ (h n)).2
  apply ComplexMeasure.equivSignedMeasure.injective
  refine Prod.ext ?_ ?_
  · change ComplexMeasure.re c = ComplexMeasure.re 0
    simp only [re_eq_jordan, hre, sub_self, map_zero]
  · change ComplexMeasure.im c = ComplexMeasure.im 0
    simp only [im_eq_jordan, him, sub_self, map_zero]

/-! ### Lemma 5.1 -/

instance : NoZeroDivisors positiveSupport where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro c d hcd
    have hc : (c : ConvMeasure).toMeasure ({0} : Set I) = 0 := c.2
    have hd : (d : ConvMeasure).toMeasure ({0} : Set I) = 0 := d.2
    have hprod : conv (c : ConvMeasure) (d : ConvMeasure) = 0 := by
      have := congrArg Subtype.val hcd
      exact this
    have hmul : ∀ z ∈ {z : ℂ | 0 < z.re}, mellin (c : ConvMeasure) z * mellin (d : ConvMeasure) z
        = 0 := fun z hz => by
      rw [← mellin_conv _ _ hz, hprod]
      exact pair_zero (isTest_mellinTest hz)
    have hzero : ∀ e : positiveSupport, EqOn (mellin (e : ConvMeasure)) 0 {z : ℂ | 0 < z.re} →
        e = 0 := fun e he => by
      apply Subtype.ext
      refine eq_zero_of_momentSeq_succ e.2 fun n => ?_
      have hpos : ((n + 1 : ℕ) : ℂ) ∈ {z : ℂ | 0 < z.re} := by
        show (0 : ℝ) < ((n + 1 : ℕ) : ℂ).re
        rw [Complex.natCast_re]; positivity
      exact (mellin_natCast (e : ConvMeasure).toMeasure (n + 1)).symm.trans (he hpos)
    rcases eqOn_zero_or_eqOn_zero_of_mul (analyticOnNhd_mellin hc) (analyticOnNhd_mellin hd)
      isOpen_rightHalfPlane isPreconnected_rightHalfPlane hmul with h | h
    · exact Or.inl (hzero c h)
    · exact Or.inr (hzero d h)

theorem momentSeq_one_ne_zero : (1 : ConvMeasure) ≠ 0 := by
  intro h
  have := congrArg (fun c => momentSeq c 0) h
  simp only [momentSeq_one, Pi.one_apply] at this
  rw [show momentSeq (0 : ConvMeasure) 0 = 0 from pair_zero (isTest_powTest 0)] at this
  exact one_ne_zero this

instance : Nontrivial ConvMeasure := ⟨⟨1, 0, momentSeq_one_ne_zero⟩⟩

/-- **Lemma 5.1**: the multiplicative convolution algebra of finite complex measures on `(0, 1]`
is an integral domain. -/
instance : IsDomain positiveSupport := NoZeroDivisors.to_isDomain _

/-! ### Lemma 5.2 -/

/-- **Lemma 5.2**: over an integral domain, `∏ (T + aᵢ) = ∏ (T + bᵢ)` forces `{aᵢ} = {bᵢ}`. -/
theorem multiset_eq_of_prod_X_add_C_eq {R : Type*} [CommRing R] [IsDomain R] (a b : Multiset R)
    (h : (a.map fun r => X + C r).prod = (b.map fun r => X + C r).prod) : a = b := by
  have hroots : ∀ s : Multiset R, ((s.map fun r => X + C r).prod).roots = s.map Neg.neg := by
    intro s
    have : (s.map fun r => X + C r) = (s.map Neg.neg).map fun r => X - C r := by
      rw [Multiset.map_map]
      congr 1
      funext r
      simp [sub_eq_add_neg]
    rw [this, roots_multiset_prod_X_sub_C]
  have := congrArg Polynomial.roots h
  rw [hroots, hroots] at this
  exact Multiset.map_injective neg_injective this

end GaloisForLFunctions.HTGeometry.MeasureConvolution
