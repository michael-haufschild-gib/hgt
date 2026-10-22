import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileBoundaryFlux

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
def rootFactor (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-(Complex.I * z) * (S.quantileFun t : ℂ))

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

/-! ### The differential equation -/

theorem hasDerivAt_quantileFun_complex {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => ((S.quantileFun s : ℝ) : ℂ))
      (((quantileSpeed S t : ℝ) : ℂ)) t :=
  (hasDerivAt_quantileFun S ht).ofReal_comp

theorem hasDerivAt_rootFactor {z : ℂ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rootFactor S z)
      (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootFactor S z t) t := by
  have hQ := hasDerivAt_quantileFun_complex S ht
  have hlin : HasDerivAt (fun s : ℝ => -(Complex.I * z) * ((S.quantileFun s : ℝ) : ℂ))
      (-(Complex.I * z) * ((quantileSpeed S t : ℝ) : ℂ)) t := hQ.const_mul _
  have hexp := hlin.cexp
  refine hexp.congr_deriv ?_
  show rootFactor S z t * (-(Complex.I * z) * ((quantileSpeed S t : ℝ) : ℂ)) = _
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
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := Set.ordConnected_Ioo.uIcc_subset ha hb
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
      exact hFinv s
    have hmul := hEinv.mul (hderiv t htIoo)
    refine hmul.congr_deriv ?_
    rw [hFinv t]
    ring
  have hcont : IntervalIntegrable (fun t => -m * sourceChar z (S.quantileFun t)) volume a b := by
    have hbase : IntervalIntegrable (fun u => sourceChar z (S.quantileFun u)) volume a b := by
      rw [intervalIntegrable_iff]
      refine (integrableOn_sourceChar_comp_quantile S hz).mono_set ?_
      exact fun u hu => hsub (Set.uIoc_subset_uIcc hu)
    exact hbase.const_mul _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hcont
  rw [intervalIntegral.integral_const_mul] at this
  exact this.symm

/-! ### The energy balance of the root mode -/

theorem rootG_eq {z : ℂ} (t : ℝ) :
    rootG S z t = -(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootH S z t := by
  rw [rootG, rootH]
  ring

theorem hasDerivAt_rootH_ode {z : ℂ} (hz : HasShiftedTail S z) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rootH S z)
      (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootH S z t - 1) t := by
  have h := hasDerivAt_rootH S hz ht
  rwa [rootG_eq] at h

/-- The pointwise energy balance of a solution of the pinned differential equation. -/
theorem energy_deriv_identity (z q h : ℂ) (hq : (starRingEnd ℂ) q = q) :
    (starRingEnd ℂ) (-(Complex.I * z * q) * h - 1) * h
      + (starRingEnd ℂ) h * (-(Complex.I * z * q) * h - 1)
      = 2 * ((z.im : ℝ) : ℂ) * q * ((starRingEnd ℂ) h * h)
        - (h + (starRingEnd ℂ) h) := by
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hzc : (starRingEnd ℂ) z = z - 2 * ((z.im : ℝ) : ℂ) * Complex.I := by
    have hsc := Complex.sub_conj z
    push_cast at hsc
    linear_combination -hsc
  simp only [map_sub, map_mul, map_neg, map_one, Complex.conj_I, hq, hzc]
  linear_combination (-2 * ((z.im : ℝ) : ℂ) * q * ((starRingEnd ℂ) h) * h) * hII

theorem conj_mul_self_eq (w : ℂ) : (starRingEnd ℂ) w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq w

/-- The integrand of the energy balance. -/
def rootBalance (z : ℂ) (t : ℝ) : ℂ :=
  2 * ((z.im : ℝ) : ℂ) * ((quantileSpeed S t * ‖rootH S z t‖ ^ 2 : ℝ) : ℂ)
    - (rootH S z t + (starRingEnd ℂ) (rootH S z t))

theorem hasDerivAt_rootEnergy {z : ℂ} (hz : HasShiftedTail S z) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => (starRingEnd ℂ) (rootH S z s) * rootH S z s) (rootBalance S z t) t := by
  have hode := hasDerivAt_rootH_ode S hz ht
  have hmul := hode.star.mul hode
  refine hmul.congr_deriv ?_
  show (starRingEnd ℂ) (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootH S z t - 1)
        * rootH S z t
      + (starRingEnd ℂ) (rootH S z t)
        * (-(Complex.I * z * ((quantileSpeed S t : ℝ) : ℂ)) * rootH S z t - 1)
    = rootBalance S z t
  rw [energy_deriv_identity z ((quantileSpeed S t : ℝ) : ℂ) (rootH S z t) (Complex.conj_ofReal _),
    rootBalance, conj_mul_self_eq]
  push_cast
  ring

/-! ### Continuity of the mode on the open interval -/

theorem continuousOn_quantileSpeed : ContinuousOn (quantileSpeed S) (Ioo (0 : ℝ) 1) := by
  refine ContinuousOn.div continuousOn_const
    (S.continuous_k.comp_continuousOn (continuousOn_quantileFun S)) ?_
  intro _ _
  exact (S.pos_k _).ne'

theorem continuousOn_rootH {z : ℂ} (hz : HasShiftedTail S z) :
    ContinuousOn (rootH S z) (Ioo (0 : ℝ) 1) := fun _ ht =>
  ((hasDerivAt_rootH S hz ht).continuousAt).continuousWithinAt

theorem continuousOn_rootBalance {z : ℂ} (hz : HasShiftedTail S z) :
    ContinuousOn (rootBalance S z) (Ioo (0 : ℝ) 1) := by
  unfold rootBalance
  have hH := continuousOn_rootH S hz
  refine ContinuousOn.sub ?_ ?_
  · refine ContinuousOn.mul continuousOn_const ?_
    exact Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_quantileSpeed S).mul (hH.norm.pow 2))
  · exact hH.add (Complex.continuous_conj.comp_continuousOn hH)

/-- **The exact two-point energy balance of the root mode.** -/
theorem rootEnergy_two_point {z : ℂ} (hz : HasShiftedTail S z) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    ((‖rootH S z b‖ ^ 2 : ℝ) : ℂ) - ((‖rootH S z a‖ ^ 2 : ℝ) : ℂ)
      = ∫ t in a..b, rootBalance S z t := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := Set.ordConnected_Ioo.uIcc_subset ha hb
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => (starRingEnd ℂ) (rootH S z s) * rootH S z s) (rootBalance S z t) t := by
    intro t htmem
    exact hasDerivAt_rootEnergy S hz (hsub htmem)
  have hint : IntervalIntegrable (rootBalance S z) volume a b :=
    ((continuousOn_rootBalance S hz).mono hsub).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [conj_mul_self_eq, conj_mul_self_eq] at h
  exact h.symm

/-- The mode value is the ordered correlation of the source character. -/
theorem neg_rootH_eq_orderedCorrelation (z : ℂ) (t : ℝ) :
    -(rootH S z t)
      = ∫ u in (0 : ℝ)..t,
          Complex.exp (Complex.I * z * ((S.quantileFun u - S.quantileFun t : ℝ) : ℂ)) := by
  rw [rootH, neg_neg, rootA, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [rootFactor, sourceChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The ordered-correlation flux identity -/

/-- An interior exhaustion of the open unit interval. -/
def interiorSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem interiorSeq_pos (n : ℕ) : 0 < interiorSeq n := by
  rw [interiorSeq]
  positivity

theorem interiorSeq_le_half (n : ℕ) : interiorSeq n ≤ 1 / 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [interiorSeq]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem antitone_interiorSeq : Antitone interiorSeq := by
  intro m n hmn
  rw [interiorSeq, interiorSeq]
  apply one_div_le_one_div_of_le (by positivity)
  have : ((m : ℝ)) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
  linarith

theorem tendsto_interiorSeq : Tendsto interiorSeq atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop
  refine (h2.inv_tendsto_atTop).congr fun n => ?_
  simp [interiorSeq, one_div]

theorem iUnion_interiorIoc :
    (⋃ n : ℕ, Ioc (interiorSeq n) (1 - interiorSeq n)) = Ioo (0 : ℝ) 1 := by
  ext t
  simp only [mem_iUnion, mem_Ioc, mem_Ioo]
  constructor
  · rintro ⟨n, h1, h2⟩
    exact ⟨lt_trans (interiorSeq_pos n) h1,
      lt_of_le_of_lt h2 (by linarith [interiorSeq_pos n])⟩
  · rintro ⟨h0, h1⟩
    have hpos : 0 < min t (1 - t) := lt_min h0 (by linarith)
    obtain ⟨n, hn⟩ := (tendsto_interiorSeq.eventually (eventually_lt_nhds hpos)).exists
    exact ⟨n, lt_of_lt_of_le hn (min_le_left _ _),
      by have := lt_of_lt_of_le hn (min_le_right _ _); linarith⟩

theorem monotone_interiorIoc :
    Monotone fun n : ℕ => Ioc (interiorSeq n) (1 - interiorSeq n) := by
  intro m n hmn t ht
  refine ⟨lt_of_le_of_lt (antitone_interiorSeq hmn) ht.1, ?_⟩
  have := antitone_interiorSeq hmn
  linarith [ht.2]

/-- The endpoint data of a root mode: the exact source-tail input the flux identity uses. -/
structure RootModeEndpoints (z : ℂ) : Prop where
  integrableEnergy :
    IntegrableOn (fun t => quantileSpeed S t * ‖rootH S z t‖ ^ 2) (Ioo (0 : ℝ) 1) volume
  integrableValue : IntegrableOn (rootH S z) (Ioo (0 : ℝ) 1) volume
  tendstoLeft : Tendsto (fun t => ‖rootH S z t‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)
  tendstoRight : Tendsto (fun t => ‖rootH S z t‖ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 0)

theorem integrableOn_conj_rootH {z : ℂ} (he : RootModeEndpoints S z) :
    IntegrableOn (fun t => (starRingEnd ℂ) (rootH S z t)) (Ioo (0 : ℝ) 1) volume := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable he.integrableValue.1, ?_⟩
  refine he.integrableValue.2.congr' ?_
  filter_upwards with x
  simp

theorem integrableOn_energyComplex {z : ℂ} (he : RootModeEndpoints S z) :
    IntegrableOn (fun t => 2 * ((z.im : ℝ) : ℂ) *
      ((quantileSpeed S t * ‖rootH S z t‖ ^ 2 : ℝ) : ℂ)) (Ioo (0 : ℝ) 1) volume :=
  (he.integrableEnergy.ofReal).const_mul (2 * ((z.im : ℝ) : ℂ))

theorem integrableOn_rootBalance {z : ℂ} (he : RootModeEndpoints S z) :
    IntegrableOn (rootBalance S z) (Ioo (0 : ℝ) 1) volume :=
  (integrableOn_energyComplex S he).sub
    (he.integrableValue.add (integrableOn_conj_rootH S he))

/-- **The ordered-correlation flux identity.**  The real part of the ordered correlation of the
root mode is the negative of the imaginary spectral part times its quantile energy. -/
theorem rootFlux_identity {z : ℂ} (hz : HasShiftedTail S z) (he : RootModeEndpoints S z) :
    (∫ t in Ioo (0 : ℝ) 1, -(rootH S z t)).re
      = -(z.im) * ∫ t in Ioo (0 : ℝ) 1, quantileSpeed S t * ‖rootH S z t‖ ^ 2 := by
  -- the balance integrates to zero over the whole interval
  have hzero : ∫ t in Ioo (0 : ℝ) 1, rootBalance S z t = 0 := by
    have hlim : Tendsto (fun n : ℕ => ∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
        rootBalance S z t) atTop (𝓝 (∫ t in Ioo (0 : ℝ) 1, rootBalance S z t)) := by
      have h := MeasureTheory.tendsto_setIntegral_of_monotone
        (fun n : ℕ => measurableSet_Ioc) monotone_interiorIoc
        (by rw [iUnion_interiorIoc]; exact integrableOn_rootBalance S he)
      rwa [iUnion_interiorIoc] at h
    have hmemL : ∀ n : ℕ, interiorSeq n ∈ Ioo (0 : ℝ) 1 := fun n =>
      ⟨interiorSeq_pos n, lt_of_le_of_lt (interiorSeq_le_half n) (by norm_num)⟩
    have hmemR : ∀ n : ℕ, 1 - interiorSeq n ∈ Ioo (0 : ℝ) 1 := fun n =>
      ⟨by linarith [interiorSeq_le_half n], by linarith [interiorSeq_pos n]⟩
    have heq : ∀ n : ℕ, ∫ t in Ioc (interiorSeq n) (1 - interiorSeq n), rootBalance S z t
        = ((‖rootH S z (1 - interiorSeq n)‖ ^ 2 : ℝ) : ℂ)
          - ((‖rootH S z (interiorSeq n)‖ ^ 2 : ℝ) : ℂ) := by
      intro n
      rw [← intervalIntegral.integral_of_le (by linarith [interiorSeq_le_half n]),
        ← rootEnergy_two_point S hz (hmemL n) (hmemR n)]
    have hL : Tendsto (fun n : ℕ => ‖rootH S z (interiorSeq n)‖ ^ 2) atTop (𝓝 0) := by
      refine he.tendstoLeft.comp ?_
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_interiorSeq
        (Filter.Eventually.of_forall fun n => interiorSeq_pos n)
    have hR : Tendsto (fun n : ℕ => ‖rootH S z (1 - interiorSeq n)‖ ^ 2) atTop (𝓝 0) := by
      refine he.tendstoRight.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Filter.Eventually.of_forall fun n => by
          simp only [mem_Iio]
          linarith [interiorSeq_pos n])
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub tendsto_interiorSeq
    have hlim2 : Tendsto (fun n : ℕ => ∫ t in Ioc (interiorSeq n) (1 - interiorSeq n),
        rootBalance S z t) atTop (𝓝 0) := by
      refine Filter.Tendsto.congr (fun n => (heq n).symm) ?_
      have := ((Complex.continuous_ofReal.tendsto 0).comp hR).sub
        ((Complex.continuous_ofReal.tendsto 0).comp hL)
      simpa using this
    exact tendsto_nhds_unique hlim hlim2
  -- split the balance
  have hsplit : ∫ t in Ioo (0 : ℝ) 1, rootBalance S z t
      = 2 * ((z.im : ℝ) : ℂ) *
          ((∫ t in Ioo (0 : ℝ) 1, quantileSpeed S t * ‖rootH S z t‖ ^ 2 : ℝ) : ℂ)
        - ((∫ t in Ioo (0 : ℝ) 1, rootH S z t)
          + (starRingEnd ℂ) (∫ t in Ioo (0 : ℝ) 1, rootH S z t)) := by
    have h1 := integrableOn_energyComplex S he
    have h2 : IntegrableOn (fun t => rootH S z t + (starRingEnd ℂ) (rootH S z t))
        (Ioo (0 : ℝ) 1) volume := he.integrableValue.add (integrableOn_conj_rootH S he)
    unfold rootBalance
    rw [MeasureTheory.integral_sub h1 h2,
      MeasureTheory.integral_add he.integrableValue (integrableOn_conj_rootH S he),
      integral_conj]
    congr 1
    rw [← integral_complex_ofReal, ← MeasureTheory.integral_const_mul]
  rw [hzero] at hsplit
  have hre := congrArg Complex.re hsplit.symm
  simp only [Complex.sub_re, Complex.zero_re] at hre
  rw [MeasureTheory.integral_neg, Complex.neg_re]
  have hadd : (∫ t in Ioo (0 : ℝ) 1, rootH S z t)
      + (starRingEnd ℂ) (∫ t in Ioo (0 : ℝ) 1, rootH S z t)
      = ((2 * (∫ t in Ioo (0 : ℝ) 1, rootH S z t).re : ℝ) : ℂ) :=
    Complex.add_conj _
  rw [hadd] at hre
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat] at hre
  linarith [hre]

end HedenmalmQuantile

end

end RHTower
