import GaloisForLFunctions.RHTower.HedenmalmThetaSeriesExpansion

/-!
# The Hilbert--Schmidt energy of the source inverse

In the intrinsic quantile coordinate the source inverse is `i M_q C`, whose integral kernel against
Lebesgue measure on `(0,1)` is

`K(t,u) = i q(t) (1_{u ≤ t} - t)`.

Its Hilbert--Schmidt energy is computed here in closed form: the inner slice integrates to
`t(1-t)`, so

`∬ |K|² = ∫₀¹ q(t)² t(1-t) dt = M ∫_ℝ p(x)(1-p(x)) / k(x) dx`,

the exact theta-tail expression of the source card.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmHilbertSchmidt

open HedenmalmQuantile

/-- The pinned kernel slice `u ↦ 1_{u ≤ t} - t`. -/
def pinnedKernelSlice (t u : ℝ) : ℝ := (if u ≤ t then (1 : ℝ) else 0) - t

/-- **The inner slice energy.**  The pinned kernel slice has energy `t(1-t)` on the unit
interval. -/
theorem integral_pinnedKernelSlice_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ u in Ioo (0 : ℝ) 1, pinnedKernelSlice t u ^ 2 = t * (1 - t) := by
  have hsplit : Ioo (0 : ℝ) 1 = Ioc 0 t ∪ Ioo t 1 := by
    ext u
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_or_gt u t with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h0, h⟩ | ⟨h, h1⟩)
      · exact ⟨h0, lt_of_le_of_lt h ht.2⟩
      · exact ⟨lt_trans ht.1 h, h1⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioo t 1) := by
    rw [Set.disjoint_left]
    rintro u ⟨_, hu⟩ ⟨hu', _⟩
    exact absurd hu (not_le.mpr hu')
  have hbdd : ∀ u : ℝ, ‖pinnedKernelSlice t u ^ 2‖ ≤ 1 := by
    intro u
    rw [pinnedKernelSlice]
    by_cases h : u ≤ t <;> simp only [h, if_true, if_false] <;>
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] <;> nlinarith [ht.1, ht.2]
  have hmeas : AEStronglyMeasurable (fun u => pinnedKernelSlice t u ^ 2) volume := by
    refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.pow_const ?_ 2
    refine Measurable.sub ?_ measurable_const
    exact (measurable_const.ite (measurableSet_le measurable_id measurable_const)
      measurable_const)
  have hint : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ ⊤ →
      IntegrableOn (fun u => pinnedKernelSlice t u ^ 2) s volume := by
    intro s hs hfin
    refine Measure.integrableOn_of_bounded (M := (1 : ℝ)) hfin hmeas ?_
    filter_upwards with u
    exact hbdd u
  have h1 : IntegrableOn (fun u => pinnedKernelSlice t u ^ 2) (Ioc 0 t) volume :=
    hint _ measurableSet_Ioc (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have h2 : IntegrableOn (fun u => pinnedKernelSlice t u ^ 2) (Ioo t 1) volume :=
    hint _ measurableSet_Ioo (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioo h1 h2]
  have hleft : ∫ u in Ioc (0 : ℝ) t, pinnedKernelSlice t u ^ 2 = t * (1 - t) ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 - t) ^ 2) fun u hu => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero, smul_eq_mul,
        ENNReal.toReal_ofReal ht.1.le]
    · rw [pinnedKernelSlice, if_pos hu.2]
  have hright : ∫ u in Ioo t (1 : ℝ), pinnedKernelSlice t u ^ 2 = (1 - t) * t ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => t ^ 2) fun u hu => ?_]
    · rw [setIntegral_const, Measure.real, Real.volume_Ioo, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
    · rw [pinnedKernelSlice, if_neg (not_le.mpr hu.1), zero_sub, neg_pow]
      ring
  rw [hleft, hright]
  ring

/-! ### The Hilbert--Schmidt energy in source coordinates -/

variable (S : PositiveDensitySource)

/-- The reciprocal-tail density `p(1-p)/k` of the source card. -/
def tailEnergyDensity (x : ℝ) : ℝ := S.cdfFun x * (1 - S.cdfFun x) / S.k x

/-- **The Hilbert--Schmidt energy of the source inverse.**  The quantile-coordinate energy of the
pinned kernel is the theta-tail integral `M ∫ p(1-p)/k`. -/
theorem integral_quantileSpeed_sq_slice :
    (∫ t in Ioo (0 : ℝ) 1, quantileSpeed S t ^ 2 * (t * (1 - t)))
      = S.mass * ∫ x, tailEnergyDensity S x := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x)))
      (volume : Measure ℝ) := by
    refine ((continuous_const.div S.continuous_k fun x => (S.pos_k x).ne').pow 2).mul ?_
      |>.aestronglyMeasurable
    exact S.continuous_cdfFun.mul (continuous_const.sub S.continuous_cdfFun)
  have hmain := integral_comp_quantile S
    (fun x => (S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x))) hmeas
  have hleft : (∫ t in Ioo (0 : ℝ) 1,
      (S.mass / S.k (S.quantileFun t)) ^ 2
        * (S.cdfFun (S.quantileFun t) * (1 - S.cdfFun (S.quantileFun t))))
      = ∫ t in Ioo (0 : ℝ) 1, quantileSpeed S t ^ 2 * (t * (1 - t)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [S.cdfFun_quantile ht, quantileSpeed]
  have hright : (∫ x, S.normalized x •
      ((S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x))))
      = S.mass * ∫ x, tailEnergyDensity S x := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hk : S.k x ≠ 0 := (S.pos_k x).ne'
    have hM : S.mass ≠ 0 := S.mass_ne_zero
    show S.normalized x * ((S.mass / S.k x) ^ 2 * (S.cdfFun x * (1 - S.cdfFun x)))
      = S.mass * tailEnergyDensity S x
    rw [show S.normalized x = S.k x / S.mass from rfl, tailEnergyDensity]
    field_simp
  rw [← hleft, hmain, hright]


/-! ### The reflection law `R B R = -B` -/

open HedenmalmPrimeTranslation

/-- Reflection `(R f)(x) = f(-x)`. -/
def sourceReflection (f : ℝ → ℂ) (x : ℝ) : ℂ := f (-x)

theorem sourceFunctional_sourceReflection (f : ℝ → ℂ) :
    sourceFunctional (sourceReflection f) = sourceFunctional f := by
  show (∫ x, f (-x)) = ∫ x, f x
  exact integral_neg_eq_self f volume

/-- **The reflection law.**  For an even source the reflected source inverse is its own negative:
`R B R = -B`. -/
theorem sourceInverse_sourceReflection (hk : ∀ x, S.k (-x) = S.k x) {f : ℝ → ℂ}
    (hf : Integrable f (volume : Measure ℝ)) (x : ℝ) :
    HedenmalmQuantile.sourceInverse S (sourceReflection f) (-x)
      = -HedenmalmQuantile.sourceInverse S f x := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  set c : ℂ := sourceFunctional f / (S.mass : ℂ) with hc
  have hg : Integrable (fun y => f y - c * (S.k y : ℂ)) (volume : Measure ℝ) :=
    hf.sub (hkC.const_mul c)
  have hmassC : (∫ y, (S.k y : ℂ)) = (S.mass : ℂ) := by
    rw [integral_complex_ofReal]
    rfl
  have hzero : (∫ y, (f y - c * (S.k y : ℂ))) = 0 := by
    rw [MeasureTheory.integral_sub hf (hkC.const_mul c), MeasureTheory.integral_const_mul,
      hmassC, hc]
    have hM : ((S.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast S.mass_ne_zero
    show sourceFunctional f - sourceFunctional f / (S.mass : ℂ) * (S.mass : ℂ) = 0
    field_simp
    ring
  have hrefl : (∫ y in Iic (-x), (sourceReflection f y
      - (∫ z, sourceReflection f z) / (S.mass : ℂ) * (S.k y : ℂ)))
      = ∫ u in Ici x, (f u - c * (S.k u : ℂ)) := by
    rw [show (∫ z, sourceReflection f z) = sourceFunctional f from
      sourceFunctional_sourceReflection f, ← hc, setIntegral_Iic_comp_neg]
    refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
    show f (-(-u)) - c * (S.k (-u) : ℂ) = f u - c * (S.k u : ℂ)
    rw [hk u, neg_neg]
  rw [HedenmalmQuantile.sourceInverse, HedenmalmQuantile.sourceInverse, hrefl,
    setIntegral_Ici_eq_sub hg x, hzero]
  show Complex.I * (0 - ∫ u in Iic x, (f u - c * (S.k u : ℂ)))
    = -(Complex.I * ∫ y in Iic x, (f y - c * (S.k y : ℂ)))
  ring



/-! ### The point spectrum is the divisor -/

/-- **A general source coefficient still forces a zero.**  If `u` solves `-i u' + α u = c k` with
`c ≠ 0` and its tilted value vanishes at both ends, then `Ξ_C(α) = 0`. -/
theorem xiC_eq_zero_of_solution_const {α c : ℂ} (hc : c ≠ 0) {u u' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (heq : ∀ x, -Complex.I * u' x + α * u x = c * (S.k x : ℂ))
    (hz : HedenmalmQuantile.HasShiftedTail S α)
    (hbot : Filter.Tendsto (fun x => u x * HedenmalmQuantile.sourceChar α x)
      Filter.atBot (nhds 0))
    (htop : Filter.Tendsto (fun x => u x * HedenmalmQuantile.sourceChar α x)
      Filter.atTop (nhds 0)) :
    HedenmalmQuantile.xiC S α = 0 := by
  have hchar : ∀ x : ℝ, HasDerivAt (HedenmalmQuantile.sourceChar α)
      (Complex.I * α * HedenmalmQuantile.sourceChar α x) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => Complex.I * α * ((t : ℝ) : ℂ)) (Complex.I * α) x := by
      simpa using (hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * α)
    have := hlin.cexp
    refine this.congr_deriv ?_
    rw [HedenmalmQuantile.sourceChar]
    ring
  have hprod : ∀ x : ℝ, HasDerivAt (fun t => u t * HedenmalmQuantile.sourceChar α t)
      (c * Complex.I * ((S.k x : ℂ) * HedenmalmQuantile.sourceChar α x)) x := by
    intro x
    have h := (hderiv x).mul (hchar x)
    refine h.congr_deriv ?_
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hx := heq x
    linear_combination (Complex.I * HedenmalmQuantile.sourceChar α x) * hx
      + (HedenmalmQuantile.sourceChar α x * u' x) * hI
  have hInt : Integrable
      (fun x => c * Complex.I * ((S.k x : ℂ) * HedenmalmQuantile.sourceChar α x))
      (volume : Measure ℝ) :=
    (HedenmalmQuantile.integrable_k_sourceChar S hz).const_mul _
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hprod hInt hbot htop
  rw [MeasureTheory.integral_const_mul, sub_zero] at h
  have hci : c * Complex.I ≠ 0 := mul_ne_zero hc Complex.I_ne_zero
  rw [HedenmalmQuantile.xiC]
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hci
  · exact h1

/-- **A divisor point produces an eigenvector of the source inverse.**  With the endpoint data of
the two-ended mode, `B f_z = -z⁻¹ f_z`. -/
theorem sourceInverse_sourceModeF_eq_smul {z : ℂ} (hz : z ≠ 0)
    (hst : HedenmalmQuantile.HasShiftedTail S z)
    (hint : Integrable (sourceModeF S z) (volume : Measure ℝ))
    (hbot : Filter.Tendsto (sourceModeU S z) Filter.atBot (nhds 0))
    (hmass : (∫ x, sourceModeF S z x) = (S.mass : ℂ)) (x : ℝ) :
    HedenmalmQuantile.sourceInverse S (sourceModeF S z) x
      = (-z⁻¹) * sourceModeF S z x := by
  rw [sourceInverse_sourceModeF S hst hint hbot hmass x, sourceModeF]
  field_simp


end HedenmalmHilbertSchmidt

end

end RHTower
