import GaloisForLFunctions.RHTower.HedenmalmQuantileBoundaryFlux

/-!
# Root modes of the quantile normal form

The quantile function is differentiable with derivative the quantile speed, so the eigenvalue
relation `i q (C g) = -z⁻¹ g` is a first-order linear differential equation in the quantile
coordinate.  Its integrating factor is `exp(i z Q)`, and the explicit solution with vanishing left
endpoint is

`h(t) = -exp(-i z Q t) ∫₀ᵗ exp(i z Q u) du`,  `g(t) = i z q(t) exp(-i z Q t) ∫₀ᵗ exp(i z Q u) du`.

The right endpoint condition is exactly the vanishing of the completed source transform

`Ξ_C(z) = ∫ k(x) exp(i z x) dx`,

because `∫₀¹ exp(i z Q u) du = M⁻¹ Ξ_C(z)`.

The energy of the mode obeys an exact two-point balance whose endpoint limits give the ordered
correlation flux identity.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmQuantile

variable (S : PositiveDensitySource)

/-! ### The quantile is differentiable -/

/-- The distribution function as a map into the open unit interval. -/
def cdfSubtype (x : ℝ) : Ioo (0 : ℝ) 1 := ⟨S.cdfFun x, S.cdfFun_mem_Ioo x⟩

theorem strictMono_cdfSubtype : StrictMono (cdfSubtype S) := fun _ _ h =>
  Subtype.mk_lt_mk.mpr (S.strictMono_cdfFun h)

theorem surjective_cdfSubtype : Function.Surjective (cdfSubtype S) := by
  rintro ⟨t, ht⟩
  obtain ⟨x, hx⟩ := S.surjOn_cdfFun ht
  exact ⟨x, Subtype.ext hx⟩

/-- The distribution function as an order isomorphism onto the open unit interval. -/
def cdfOrderIso : ℝ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective (cdfSubtype S) (strictMono_cdfSubtype S) (surjective_cdfSubtype S)

theorem cdfOrderIso_symm_eq (t : Ioo (0 : ℝ) 1) :
    ((cdfOrderIso S).symm t : ℝ) = S.quantileFun (t : ℝ) := by
  have h := congrArg Subtype.val ((cdfOrderIso S).apply_symm_apply t)
  have h' : S.cdfFun ((cdfOrderIso S).symm t : ℝ) = (t : ℝ) := h
  rw [← h', S.quantile_cdfFun]

theorem continuousOn_quantileFun : ContinuousOn S.quantileFun (Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hrw : (Ioo (0 : ℝ) 1).restrict S.quantileFun
      = fun t : Ioo (0 : ℝ) 1 => ((cdfOrderIso S).symm t : ℝ) := by
    funext t
    exact (cdfOrderIso_symm_eq S t).symm
  rw [hrw]
  exact (cdfOrderIso S).symm.toHomeomorph.continuous

theorem continuousAt_quantileFun {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt S.quantileFun t :=
  (continuousOn_quantileFun S).continuousAt (Ioo_mem_nhds ht.1 ht.2)

/-- **The quantile speed is the derivative of the quantile.** -/
theorem hasDerivAt_quantileFun {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt S.quantileFun (quantileSpeed S t) t := by
  have hf : HasDerivAt S.cdfFun (S.normalized (S.quantileFun t)) (S.quantileFun t) :=
    S.hasDerivAt_cdfFun _
  have hne : S.normalized (S.quantileFun t) ≠ 0 := (S.normalized_pos _).ne'
  have hfg : ∀ᶠ y in 𝓝 t, S.cdfFun (S.quantileFun y) = y := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact S.cdfFun_quantile hy
  have h := HasDerivAt.of_local_left_inverse (continuousAt_quantileFun S ht) hf hne hfg
  have hval : (S.normalized (S.quantileFun t))⁻¹ = quantileSpeed S t := by
    rw [quantileSpeed, show S.normalized (S.quantileFun t) = S.k (S.quantileFun t) / S.mass from rfl,
      inv_div]
  rwa [hval] at h

/-! ### The completed source transform -/

/-- The character `exp(i z x)`. -/
def sourceChar (z : ℂ) (x : ℝ) : ℂ := Complex.exp (Complex.I * z * (x : ℂ))

theorem continuous_sourceChar (z : ℂ) : Continuous (sourceChar z) := by
  unfold sourceChar
  fun_prop

theorem norm_sourceChar (z : ℂ) (x : ℝ) : ‖sourceChar z x‖ = Real.exp (-(z.im) * x) := by
  rw [sourceChar, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The exact tail condition making the source transform converge at `z`. -/
def HasShiftedTail (z : ℂ) : Prop :=
  Integrable (fun x => S.k x * Real.exp (-(z.im) * x)) volume

/-- The completed source transform `Ξ_C(z) = ∫ k(x) exp(i z x) dx`. -/
def xiC (z : ℂ) : ℂ := ∫ x, (S.k x : ℂ) * sourceChar z x

theorem integrable_k_sourceChar {z : ℂ} (hz : HasShiftedTail S z) :
    Integrable (fun x => (S.k x : ℂ) * sourceChar z x) volume := by
  refine Integrable.mono' hz ?_ ?_
  · exact ((Complex.continuous_ofReal.comp S.continuous_k).mul
      (continuous_sourceChar z)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (S.pos_k x).le,
      norm_sourceChar]

theorem integrableOn_sourceChar_comp_quantile {z : ℂ} (hz : HasShiftedTail S z) :
    IntegrableOn (fun u => sourceChar z (S.quantileFun u)) (Ioo (0 : ℝ) 1) volume := by
  rw [S.integrableOn_comp_quantileFun_iff (continuous_sourceChar z).aestronglyMeasurable]
  have hk := integrable_k_sourceChar S hz
  refine (hk.div_const S.mass).congr ?_
  filter_upwards with x
  show (S.k x : ℂ) * sourceChar z x / (S.mass : ℂ) = S.normalized x • sourceChar z x
  rw [Complex.real_smul, show S.normalized x = S.k x / S.mass from rfl]
  push_cast
  ring

/-- **The quantile average of the character is the normalized source transform.** -/
theorem integral_sourceChar_comp_quantile (z : ℂ) :
    ∫ u in Ioo (0 : ℝ) 1, sourceChar z (S.quantileFun u) = xiC S z / (S.mass : ℂ) := by
  rw [integral_comp_quantile S (sourceChar z) (continuous_sourceChar z).aestronglyMeasurable]
  rw [xiC, ← MeasureTheory.integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show S.normalized x • sourceChar z x = (S.k x : ℂ) * sourceChar z x / (S.mass : ℂ)
  rw [Complex.real_smul, show S.normalized x = S.k x / S.mass from rfl]
  push_cast
  ring

/-! ### The explicit root mode -/

/-- The primitive `A(t) = ∫₀ᵗ exp(i z Q u) du`. -/
def rootA (z : ℂ) (t : ℝ) : ℂ := ∫ u in (0 : ℝ)..t, sourceChar z (S.quantileFun u)

/-- The integrating factor `exp(-i z Q t)`. -/
def rootFactor (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-(Complex.I * z * (S.quantileFun t : ℂ)))

/-- The pinned primitive of the root mode, `h(t) = -exp(-i z Q t) A(t)`. -/
def rootH (z : ℂ) (t : ℝ) : ℂ := -(rootFactor S z t * rootA S z t)

/-- The root mode itself, `g(t) = i z q(t) exp(-i z Q t) A(t)`. -/
def rootG (z : ℂ) (t : ℝ) : ℂ :=
  Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ) * (rootFactor S z t * rootA S z t)

@[simp] theorem rootA_zero (z : ℂ) : rootA S z 0 = 0 := by
  rw [rootA, intervalIntegral.integral_same]

@[simp] theorem rootH_zero (z : ℂ) : rootH S z 0 = 0 := by
  rw [rootH, rootA_zero, mul_zero, neg_zero]

theorem rootFactor_mul_sourceChar (z : ℂ) (t : ℝ) :
    rootFactor S z t * sourceChar z (S.quantileFun t) = 1 := by
  rw [rootFactor, sourceChar, ← Complex.exp_add]
  simp

/-- **The right endpoint value of the primitive is the normalized source transform.** -/
theorem rootA_one (z : ℂ) : rootA S z 1 = xiC S z / (S.mass : ℂ) := by
  rw [rootA, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_congr_set (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc),
    integral_sourceChar_comp_quantile S z]

/-- **The endpoint criterion.**  The right endpoint of the mode vanishes exactly at a zero of the
completed source transform. -/
theorem rootA_one_eq_zero_iff (z : ℂ) : rootA S z 1 = 0 ↔ xiC S z = 0 := by
  rw [rootA_one]
  have hM : ((S.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast S.mass_ne_zero
  exact div_eq_zero_iff.trans (by simp [hM])

/-- **The eigenvalue relation of the explicit root mode**, `i q h = -z⁻¹ g`. -/
theorem rootMode_relation {z : ℂ} (hz : z ≠ 0) (t : ℝ) :
    Complex.I * ((quantileSpeed S t : ℝ) : ℂ) * rootH S z t = (-z⁻¹) * rootG S z t := by
  rw [rootH, rootG]
  field_simp
  ring

/-! ### The differential equation -/

theorem hasDerivAt_quantileFun_complex {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => ((S.quantileFun s : ℝ) : ℂ))
      (((quantileSpeed S t : ℝ) : ℂ)) t :=
  (hasDerivAt_quantileFun S ht).ofReal_comp

theorem hasDerivAt_rootFactor {z : ℂ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rootFactor S z)
      (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootFactor S z t) t := by
  have hQ := hasDerivAt_quantileFun_complex S ht
  have hlin : HasDerivAt (fun s : ℝ => -(Complex.I * z * ((S.quantileFun s : ℝ) : ℂ)))
      (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ))) t := by
    simpa using ((hQ.const_mul (Complex.I * z)).neg)
  have := hlin.cexp
  rw [rootFactor]
  convert this using 1
  rw [rootFactor]
  ring

theorem intervalIntegrable_sourceChar_comp_quantile {z : ℂ} (hz : HasShiftedTail S z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun u => sourceChar z (S.quantileFun u)) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le]
  refine (integrableOn_sourceChar_comp_quantile S hz).mono_set ?_
  intro u hu
  exact ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩

theorem hasDerivAt_rootA {z : ℂ} (hz : HasShiftedTail S z) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rootA S z) (sourceChar z (S.quantileFun t)) t := by
  have hmeas : StronglyMeasurableAtFilter (fun u => sourceChar z (S.quantileFun u)) (𝓝 t)
      volume := by
    refine ⟨Ioo (0 : ℝ) 1, Ioo_mem_nhds ht.1 ht.2, ?_⟩
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact (continuous_sourceChar z).comp_continuousOn (continuousOn_quantileFun S)
  have hcont : ContinuousAt (fun u => sourceChar z (S.quantileFun u)) t :=
    (continuous_sourceChar z).continuousAt.comp (continuousAt_quantileFun S ht)
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_sourceChar_comp_quantile S hz ht) hmeas hcont

/-- **The root mode solves the pinned differential equation** `h' = g - 1`. -/
theorem hasDerivAt_rootH {z : ℂ} (hz : HasShiftedTail S z) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rootH S z) (rootG S z t - 1) t := by
  have hF := hasDerivAt_rootFactor S (z := z) ht
  have hA := hasDerivAt_rootA S hz ht
  have hprod := (hF.mul hA).neg
  refine hprod.congr_deriv ?_
  rw [rootG]
  have h1 : rootFactor S z t * sourceChar z (S.quantileFun t) = 1 :=
    rootFactor_mul_sourceChar S z t
  rw [neg_add]
  rw [show -(rootFactor S z t * sourceChar z (S.quantileFun t)) = -1 by rw [h1]]
  ring

/-- **Uniqueness for the pinned differential equation**, in exact two-point form. -/
theorem rootODE_two_point {z m : ℂ} {h : ℝ → ℂ}
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt h (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * h t - m) t)
    (hz : HasShiftedTail S z) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    (rootFactor S z b)⁻¹ * h b - (rootFactor S z a)⁻¹ * h a
      = -m * ∫ u in a..b, sourceChar z (S.quantileFun u) := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := Set.uIcc_subset_Ioo ha hb
  have hFinv : ∀ t : ℝ, (rootFactor S z t)⁻¹ = sourceChar z (S.quantileFun t) := by
    intro t
    rw [rootFactor, sourceChar, ← Complex.exp_neg]
    congr 1
    ring
  have hderivF : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => (rootFactor S z s)⁻¹ * h s) (-m * sourceChar z (S.quantileFun t)) t := by
    intro t htmem
    have htIoo := hsub htmem
    have hQ := hasDerivAt_quantileFun_complex S htIoo
    have hlin : HasDerivAt (fun s : ℝ => Complex.I * z * ((S.quantileFun s : ℝ) : ℂ))
        (Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) t := hQ.const_mul (Complex.I * z)
    have hE : HasDerivAt (fun s => sourceChar z (S.quantileFun s))
        (sourceChar z (S.quantileFun t) * (Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ))) t := by
      simpa [sourceChar] using hlin.cexp
    have hEinv : HasDerivAt (fun s => (rootFactor S z s)⁻¹)
        (sourceChar z (S.quantileFun t) * (Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ))) t := by
      refine hE.congr_of_eventuallyEq ?_
      filter_upwards with s
      exact (hFinv s).symm
    have hmul := hEinv.mul (hderiv t htIoo)
    refine hmul.congr_deriv ?_
    rw [hFinv t]
    ring
  have hcont : IntervalIntegrable (fun t => -m * sourceChar z (S.quantileFun t)) volume a b := by
    have hbase : IntervalIntegrable (fun u => sourceChar z (S.quantileFun u)) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_uIoc]
      refine (integrableOn_sourceChar_comp_quantile S hz).mono_set ?_
      intro u hu
      have : u ∈ uIcc a b := Set.mem_uIcc_of_le (le_of_lt hu.1) hu.2
      exact hsub this
    exact hbase.const_mul _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hcont
  rw [intervalIntegral.integral_const_mul] at this
  exact this.symm

end HedenmalmQuantile

end

end RHTower
