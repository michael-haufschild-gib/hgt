import GaloisForLFunctions.HTGeometry.ApertureConeWinding

/-!
# Logarithmic translation on the aperture cone

In the logistic coordinate `t = σ(x) = eˣ/(1 + eˣ)` the scale changes `φ_c(t) = ct/(1 + (c−1)t)`
of the aperture interval become translations:

* **(SAC.13)** `φ_c(σ(x)) = σ(x + log c)`; the `φ_c` form the multiplicative group, fix both
  endpoints and act freely on `(0,1)`;
* the translation flow `g ↦ g ∘ φ_c` on the cone `C*(e_1) ≅ C_0((0,1])` fixes the endpoint
  character, preserves the open-history ideal `J_T`, and carries `e_d` to `e_{dc}`;
* **(SAC.15)** the logarithmic representation `ι_T(f) = [ε ↦ f(log T − log ε)]` of `C_0(ℝ)` is an
  isometric `*`-homomorphism into `J_T`, and aperture dilation implements translation:
  `ι_T(f(· + log c)) = f(logit e_c)`.

The isometry is the eigenvalue/aperture matching of Theorem SAC-A: `σ(e_1) = [0,1]`, so the
functional-calculus norm of `f ∘ logit` is the supremum of `f` over `logit((0,1)) = ℝ`.
-/

set_option autoImplicit false

open Filter Topology Set ContinuousLinearMap
open scoped ContinuousMapZero ZeroAtInfty

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Multiplicative scale is additive translation -/

/-- The logistic coordinate `σ(x) = eˣ/(1 + eˣ)` of the aperture interval. -/
def apertureSigmoid (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x)

theorem apertureSigmoid_mem (x : ℝ) : apertureSigmoid x ∈ Ioo (0 : ℝ) 1 := by
  have h := Real.exp_pos x
  refine ⟨div_pos h (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

/-- **(SAC.13)** `φ_c(σ(x)) = σ(x + log c)`. -/
theorem realScaleChange_apertureSigmoid {c : ℝ} (hc : 0 < c) (x : ℝ) :
    realScaleChange c (apertureSigmoid x) = apertureSigmoid (x + Real.log c) := by
  have h := Real.exp_pos x
  rw [realScaleChange, apertureSigmoid, apertureSigmoid, Real.exp_add, Real.exp_log hc]
  have h1 : (0 : ℝ) < 1 + Real.exp x := by linarith
  have h2 : (0 : ℝ) < 1 + Real.exp x * c := by positivity
  have h3 : 1 + (c - 1) * (Real.exp x / (1 + Real.exp x)) =
      (1 + Real.exp x * c) / (1 + Real.exp x) := by
    field_simp; ring
  rw [h3]
  field_simp

/-- The scale changes form the multiplicative group: `φ_c ∘ φ_d = φ_{cd}`. -/
theorem realScaleChange_comp {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    realScaleChange c (realScaleChange d t) = realScaleChange (c * d) t := by
  have h1 := (scaleChange_denom_pos hd ht).ne'
  have h2 := (scaleChange_denom_pos (mul_pos hc hd) ht).ne'
  have h1' : 1 + d * t - t ≠ 0 := fun h => h1 (by linarith)
  have h1'' : 1 + t * (d - 1) ≠ 0 := fun h => h1 (by linarith)
  have h2' : 1 + t * (c * d - 1) ≠ 0 := fun h => h2 (by linarith)
  rw [realScaleChange, realScaleChange, realScaleChange]
  have h3 : 1 + (c - 1) * (d * t / (1 + (d - 1) * t)) =
      (1 + (c * d - 1) * t) / (1 + (d - 1) * t) := by
    field_simp; ring
  rw [h3]
  field_simp

/-- The translation flow fixes both endpoints of the aperture interval. -/
theorem realScaleChange_endpoints {c : ℝ} (hc : 0 < c) :
    realScaleChange c 0 = 0 ∧ realScaleChange c 1 = 1 := by
  refine ⟨by simp [realScaleChange], ?_⟩
  simp [realScaleChange, hc.ne']

/-- **The translation flow acts freely on the open aperture**: `φ_c(t) = t` for some `0 < t < 1`
only for `c = 1`. -/
theorem eq_one_of_realScaleChange_eq {c t : ℝ} (hc : 0 < c) (ht0 : 0 < t) (ht1 : t < 1)
    (h : realScaleChange c t = t) : c = 1 := by
  have hd := scaleChange_denom_pos hc ⟨ht0.le, ht1.le⟩
  rw [realScaleChange, div_eq_iff hd.ne'] at h
  have : t * (1 - t) * (c - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · linarith
    · linarith
  · linarith

/-! ## The translation action on the cone -/

section Flow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
  (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

include hinj hH in
theorem scaleChange_mem_quasispectrum {c : ℝ} (hc : 0 < c)
    (p : quasispectrum ℂ (unitGerm hT hcpt)) :
    scaleChange c p ∈ quasispectrum ℂ (unitGerm hT hcpt) := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hp : (p : ℂ) ∈ unitIntervalC := hσ ▸ p.2
  obtain ⟨t, ht, hpt⟩ := hp
  have hmem : scaleChange c (p : ℂ) ∈ unitIntervalC := by
    rw [← hpt, scaleChange_ofReal]
    refine ⟨_, ⟨div_nonneg (mul_nonneg hc.le ht.1) (scaleChange_denom_pos hc ht).le, ?_⟩,
      rfl⟩
    rw [div_le_one (scaleChange_denom_pos hc ht)]
    nlinarith [ht.1, ht.2]
  rw [← hσ] at hmem
  exact hmem

/-- The scale change `φ_c` as a pointed self-map of `σ(e) = [0,1]`. -/
def scaleFlowMap {c : ℝ} (hc : 0 < c) :
    C(quasispectrum ℂ (unitGerm hT hcpt), quasispectrum ℂ (unitGerm hT hcpt))₀ :=
  ⟨⟨fun p => ⟨scaleChange c p, scaleChange_mem_quasispectrum hT hcpt hinj hH hc p⟩,
    ((continuousOn_scaleChange hc).comp_continuous continuous_subtype_val fun p =>
      (quasispectrum_unitGerm hT hcpt hinj hH) ▸ p.2).subtype_mk _⟩,
    Subtype.ext (by simp [scaleChange])⟩

/-- **The translation flow on the cone** `C*(e_1) ≅ C_0((0,1])`: `g ↦ g ∘ φ_c`. -/
def scaleFlow {c : ℝ} (hc : 0 < c) :
    C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ →⋆ₙₐ[ℂ]
      C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀ :=
  ContinuousMapZero.nonUnitalStarAlgHom_precomp ℂ (scaleFlowMap hT hcpt hinj hH hc)

include hinj hH in
/-- The translation flow fixes the closed endpoint: `χ(g ∘ φ_c) = χ(g)`. -/
theorem endpointChar_scaleFlow {c : ℝ} (hc : 0 < c)
    (g : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀) :
    endpointChar (one_mem_quasispectrum_unitGerm hT hcpt hinj hH) (scaleFlow hT hcpt hinj hH hc g) =
      endpointChar (one_mem_quasispectrum_unitGerm hT hcpt hinj hH) g := by
  change g ⟨scaleChange c 1, _⟩ = g ⟨1, _⟩
  congr 1
  apply Subtype.ext
  change scaleChange c 1 = 1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp [scaleChange, div_self hc']

include hinj hH in
/-- The translation flow preserves the open-history ideal. -/
theorem scaleFlow_mem_endpointKernel {c : ℝ} (hc : 0 < c)
    {g : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀}
    (hg : g ∈ endpointKernel (one_mem_quasispectrum_unitGerm hT hcpt hinj hH)) :
    scaleFlow hT hcpt hinj hH hc g ∈
      endpointKernel (one_mem_quasispectrum_unitGerm hT hcpt hinj hH) := by
  have := endpointChar_scaleFlow hT hcpt hinj hH hc g
  change endpointChar _ (scaleFlow hT hcpt hinj hH hc g) = 0
  rw [this]; exact hg

include hinj hH in
/-- The flow is the multiplicative group: `φ_c`-translation after `φ_d`-translation is the
`φ_{cd}`-translation. -/
theorem scaleFlow_comp {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (g : C(quasispectrum ℂ (unitGerm hT hcpt), ℂ)₀) :
    scaleFlow hT hcpt hinj hH hc (scaleFlow hT hcpt hinj hH hd g) =
      scaleFlow hT hcpt hinj hH (mul_pos hd hc) g := by
  ext p
  change g ⟨scaleChange d (scaleChange c p), _⟩ = g ⟨scaleChange (d * c) p, _⟩
  congr 1
  apply Subtype.ext
  change scaleChange d (scaleChange c p) = scaleChange (d * c) p
  have hp : (p : ℂ) ∈ unitIntervalC := (quasispectrum_unitGerm hT hcpt hinj hH) ▸ p.2
  obtain ⟨t, ht, hpt⟩ := hp
  rw [← hpt, scaleChange_ofReal, scaleChange_ofReal, scaleChange_ofReal]
  congr 1
  exact realScaleChange_comp hd hc ht

include hinj hH in
/-- Under the functional calculus the flow sends `e_d` to `e_{dc}`. -/
theorem cfcₙHom_scaleFlow_scaleGerm {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∃ g, cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) g = scaleGerm T hT hcpt hd ∧
      cfcₙHom (R := ℂ) (isStarNormal_unitGerm hT hcpt) (scaleFlow hT hcpt hinj hH hc g) =
        scaleGerm T hT hcpt (mul_pos hd hc) := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hcd : ContinuousOn (scaleChange d) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_scaleChange hd
  have hcdc : ContinuousOn (scaleChange (d * c)) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_scaleChange (mul_pos hd hc)
  refine ⟨_, (cfcₙ_apply (scaleChange d) _ hcd (by simp [scaleChange])
    (isStarNormal_unitGerm hT hcpt)).symm.trans
    (scaleGerm_eq_cfcₙ hT hcpt hinj hH hd).symm, ?_⟩
  rw [scaleGerm_eq_cfcₙ hT hcpt hinj hH (mul_pos hd hc),
    cfcₙ_apply (scaleChange (d * c)) _ hcdc (by simp [scaleChange])
      (isStarNormal_unitGerm hT hcpt)]
  congr 1
  ext p
  change scaleChange d (scaleChange c p) = scaleChange (d * c) p
  have hp : (p : ℂ) ∈ unitIntervalC := hσ ▸ p.2
  obtain ⟨t, ht, hpt⟩ := hp
  rw [← hpt, scaleChange_ofReal, scaleChange_ofReal, scaleChange_ofReal]
  congr 1
  exact realScaleChange_comp hd hc ht

end Flow

/-! ## The logarithmic coordinate -/

/-- The logit `t ↦ log(t/(1 − t))`, inverse to the logistic coordinate on `(0,1)`. -/
def apertureLogit (t : ℝ) : ℝ := Real.log (t / (1 - t))

theorem apertureLogit_apertureSigmoid (x : ℝ) : apertureLogit (apertureSigmoid x) = x := by
  have h := Real.exp_pos x
  have h1 : (0 : ℝ) < 1 + Real.exp x := by linarith
  have : apertureSigmoid x / (1 - apertureSigmoid x) = Real.exp x := by
    rw [apertureSigmoid]; field_simp; ring
  rw [apertureLogit, this, Real.log_exp]

theorem apertureSigmoid_apertureLogit {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    apertureSigmoid (apertureLogit t) = t := by
  have h1 : (0 : ℝ) < 1 - t := by linarith
  rw [apertureSigmoid, apertureLogit, Real.exp_log (div_pos ht0 h1)]
  field_simp
  ring

/-- **(SAC.13) in the logarithmic coordinate**: `log φ_c(t)/(1 − φ_c(t)) = logit t + log c`. -/
theorem apertureLogit_realScaleChange {c t : ℝ} (hc : 0 < c) (ht0 : 0 < t) (ht1 : t < 1) :
    apertureLogit (realScaleChange c t) = apertureLogit t + Real.log c := by
  conv_lhs => rw [← apertureSigmoid_apertureLogit ht0 ht1]
  rw [realScaleChange_apertureSigmoid hc, apertureLogit_apertureSigmoid]

theorem tendsto_apertureLogit_zero : Tendsto apertureLogit (𝓝[>] 0) atBot := by
  have h1 : Tendsto (fun t : ℝ => t / (1 - t)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun t : ℝ => t / (1 - t)) 0 :=
        continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact div_pos ht.1 (by linarith [ht.2])
  exact Real.tendsto_log_nhdsGT_zero.comp h1

theorem apertureLogit_one_sub (t : ℝ) : apertureLogit (1 - t) = -apertureLogit t := by
  rw [apertureLogit, apertureLogit, sub_sub_cancel, ← Real.log_inv, inv_div]

theorem tendsto_apertureLogit_one : Tendsto apertureLogit (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun t : ℝ => 1 - t) 1 :=
        (continuous_const.sub continuous_id).continuousAt
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (Set.mem_Iio.mp ht)
  have h2 := tendsto_apertureLogit_zero.comp h1
  have h3 : (apertureLogit ∘ fun t : ℝ => 1 - t) = fun t => -apertureLogit t := by
    funext t; simp only [Function.comp_apply, apertureLogit_one_sub]
  rw [h3] at h2
  have h4 := tendsto_neg_atBot_atTop.comp h2
  have h5 : (Neg.neg ∘ fun t => -apertureLogit t) = apertureLogit := by
    funext t; simp
  rwa [h5] at h4

/-- The profile `t ↦ f(logit t)` on `(0,1)`, extended by `0` at the endpoints. -/
def logProfile (f : C₀(ℝ, ℂ)) (t : ℝ) : ℂ :=
  if 0 < t ∧ t < 1 then f (apertureLogit t) else 0

theorem continuousOn_logProfile (f : C₀(ℝ, ℂ)) : ContinuousOn (logProfile f) (Icc 0 1) := by
  have hbot : Tendsto f atBot (𝓝 0) := (zero_at_infty f).mono_left atBot_le_cocompact
  have htop : Tendsto f atTop (𝓝 0) := (zero_at_infty f).mono_left atTop_le_cocompact
  have hint : ∀ t, 0 < t → t < 1 → ContinuousAt (logProfile f) t := fun t h0 h1 => by
    have hev : logProfile f =ᶠ[𝓝 t] fun t => f (apertureLogit t) := by
      filter_upwards [Ioo_mem_nhds h0 h1] with u hu
      simp [logProfile, hu.1, hu.2]
    refine ContinuousAt.congr ?_ hev.symm
    refine f.continuous.continuousAt.comp ?_
    have hq : ContinuousAt (fun u : ℝ => u / (1 - u)) t :=
      continuousAt_id.div (continuousAt_const.sub continuousAt_id)
        (show (1 : ℝ) - t ≠ 0 by linarith)
    exact (Real.continuousAt_log (div_pos h0 (show (0 : ℝ) < 1 - t by linarith)).ne').comp
      (f := fun u : ℝ => u / (1 - u)) hq
  intro t ht
  rcases ht.1.eq_or_lt with rfl | h0
  · refine (continuousWithinAt_Ioi_iff_Ici.mp ?_).mono Icc_subset_Ici_self
    have hval : logProfile f 0 = 0 := by simp [logProfile]
    rw [ContinuousWithinAt, hval]
    refine (hbot.comp tendsto_apertureLogit_zero).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    simp [logProfile, hu.1, hu.2]
  rcases ht.2.eq_or_lt with rfl | h1
  · refine (continuousWithinAt_Iio_iff_Iic.mp ?_).mono Icc_subset_Iic_self
    have hval : logProfile f 1 = 0 := by simp [logProfile]
    rw [ContinuousWithinAt, hval]
    refine (htop.comp tendsto_apertureLogit_one).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with u hu
    simp [logProfile, hu.1, hu.2]
  · exact (hint t h0 h1).continuousWithinAt

/-- The globally continuous symbol `z ↦ f(logit(clamp z))`. -/
def logSymbol (f : C₀(ℝ, ℂ)) (z : ℂ) : ℂ := logProfile f (max 0 (min 1 z.re))

theorem continuous_logSymbol (f : C₀(ℝ, ℂ)) : Continuous (logSymbol f) :=
  (continuousOn_logProfile f).comp_continuous
    (continuous_const.max (continuous_const.min Complex.continuous_re))
    fun _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem logSymbol_zero (f : C₀(ℝ, ℂ)) : logSymbol f 0 = 0 := by simp [logSymbol, logProfile]

theorem logSymbol_one (f : C₀(ℝ, ℂ)) : logSymbol f 1 = 0 := by simp [logSymbol, logProfile]

theorem logSymbol_ofReal (f : C₀(ℝ, ℂ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    logSymbol f t = logProfile f t := by
  simp [logSymbol, min_eq_right ht.2, max_eq_right ht.1]

theorem norm_logSymbol_le (f : C₀(ℝ, ℂ)) (z : ℂ) : ‖logSymbol f z‖ ≤ ‖f‖ := by
  unfold logSymbol logProfile
  split_ifs
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact f.toBCF.norm_coe_le_norm _
  · simp

theorem logSymbol_mul (f g : C₀(ℝ, ℂ)) (z : ℂ) :
    logSymbol (f * g) z = logSymbol f z * logSymbol g z := by
  unfold logSymbol logProfile; split_ifs <;> simp

theorem logSymbol_add (f g : C₀(ℝ, ℂ)) (z : ℂ) :
    logSymbol (f + g) z = logSymbol f z + logSymbol g z := by
  unfold logSymbol logProfile; split_ifs <;> simp

theorem logSymbol_smul (c : ℂ) (f : C₀(ℝ, ℂ)) (z : ℂ) :
    logSymbol (c • f) z = c • logSymbol f z := by
  unfold logSymbol logProfile; split_ifs <;> simp

theorem logSymbol_star (f : C₀(ℝ, ℂ)) (z : ℂ) :
    logSymbol (star f) z = star (logSymbol f z) := by
  unfold logSymbol logProfile; split_ifs <;> simp

theorem realScaleChange_mem_Ioo {c t : ℝ} (hc : 0 < c) (ht0 : 0 < t) (ht1 : t < 1) :
    realScaleChange c t ∈ Ioo (0 : ℝ) 1 := by
  have hd := scaleChange_denom_pos hc ⟨ht0.le, ht1.le⟩
  refine ⟨div_pos (mul_pos hc ht0) hd, (div_lt_one hd).mpr ?_⟩
  nlinarith

/-- Translation `f ↦ f(· + a)` of `C_0(ℝ)`. -/
def translateC0 (a : ℝ) (f : C₀(ℝ, ℂ)) : C₀(ℝ, ℂ) :=
  ⟨⟨fun x => f (x + a), f.continuous.comp (continuous_add_const a)⟩,
    (zero_at_infty f).comp (Homeomorph.addRight a).isClosedEmbedding.tendsto_cocompact⟩

theorem translateC0_apply (a : ℝ) (f : C₀(ℝ, ℂ)) (x : ℝ) :
    translateC0 a f x = f (x + a) := rfl

section Representation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
  (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)

/-- **(SAC.15)** The logarithmic representation `ι_T(f) = [ε ↦ f(log T − log ε)]` of
`C_0(ℝ)`. -/
def logRepresentation (f : C₀(ℝ, ℂ)) : BoundaryCorona H :=
  cfcₙ (logSymbol f) (unitGerm hT hcpt)

include hinj hH in
theorem logRepresentation_mem_openHistoryIdeal (f : C₀(ℝ, ℂ)) :
    logRepresentation hT hcpt f ∈ openHistoryIdeal hT hcpt :=
  cfcₙ_mem_openHistoryIdeal hT hcpt hinj hH (continuous_logSymbol f).continuousOn
    (logSymbol_zero f) (logSymbol_one f)

include hinj hH in
/-- **(SAC.15) `ι_T` is faithful**: `‖ι_T(f)‖ = ‖f‖_∞`. -/
theorem norm_logRepresentation (f : C₀(ℝ, ℂ)) :
    ‖logRepresentation hT hcpt f‖ = ‖f‖ := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  apply le_antisymm
  · exact norm_cfcₙ_le fun z _ => norm_logSymbol_le f z
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr fun x => ?_
    have hmem : ((apertureSigmoid x : ℝ) : ℂ) ∈ quasispectrum ℂ (unitGerm hT hcpt) := by
      rw [hσ]
      exact ⟨_, ⟨(apertureSigmoid_mem x).1.le, (apertureSigmoid_mem x).2.le⟩, rfl⟩
    have h := norm_apply_le_norm_cfcₙ (logSymbol f) (unitGerm hT hcpt) hmem
      (continuous_logSymbol f).continuousOn (logSymbol_zero f) (isStarNormal_unitGerm hT hcpt)
    rw [logSymbol_ofReal f ⟨(apertureSigmoid_mem x).1.le, (apertureSigmoid_mem x).2.le⟩,
      logProfile, if_pos ⟨(apertureSigmoid_mem x).1, (apertureSigmoid_mem x).2⟩,
      apertureLogit_apertureSigmoid] at h
    exact h

/-- `ι_T : C_0(ℝ) → Q` as a `*`-homomorphism. -/
def logRepresentationHom : C₀(ℝ, ℂ) →⋆ₙₐ[ℂ] BoundaryCorona H where
  toFun := logRepresentation hT hcpt
  map_smul' c f := by
    change cfcₙ (logSymbol (c • f)) _ = c • cfcₙ (logSymbol f) _
    rw [show logSymbol (c • f) = fun z => c • logSymbol f z from funext (logSymbol_smul c f)]
    exact cfcₙ_smul c (logSymbol f) _ (continuous_logSymbol f).continuousOn (logSymbol_zero f)
  map_zero' := by
    have : logSymbol (0 : C₀(ℝ, ℂ)) = 0 := funext fun z => by
      unfold logSymbol logProfile; split_ifs <;> simp
    simp only [logRepresentation, this]
    exact cfcₙ_zero ℂ _
  map_add' f g := by
    change cfcₙ (logSymbol (f + g)) _ = cfcₙ (logSymbol f) _ + cfcₙ (logSymbol g) _
    rw [show logSymbol (f + g) = fun z => logSymbol f z + logSymbol g z from
      funext (logSymbol_add f g)]
    exact cfcₙ_add _ _ _ (continuous_logSymbol f).continuousOn (logSymbol_zero f)
      (continuous_logSymbol g).continuousOn (logSymbol_zero g)
  map_mul' f g := by
    change cfcₙ (logSymbol (f * g)) _ = cfcₙ (logSymbol f) _ * cfcₙ (logSymbol g) _
    rw [show logSymbol (f * g) = fun z => logSymbol f z * logSymbol g z from
      funext (logSymbol_mul f g)]
    exact cfcₙ_mul _ _ _ (continuous_logSymbol f).continuousOn (logSymbol_zero f)
      (continuous_logSymbol g).continuousOn (logSymbol_zero g)
  map_star' f := by
    change cfcₙ (logSymbol (star f)) _ = star (cfcₙ (logSymbol f) _)
    rw [show logSymbol (star f) = fun z => star (logSymbol f z) from funext (logSymbol_star f)]
    exact cfcₙ_star (logSymbol f) (unitGerm hT hcpt)

include hinj hH in
/-- **(SAC.15)** `ι_T` is a faithful (isometric) `*`-representation of `C_0(ℝ)` in the
open-history ideal. -/
theorem logRepresentationHom_isometry :
    Isometry (logRepresentationHom hT hcpt (H := H)) ∧
      ∀ f, logRepresentationHom hT hcpt f ∈ openHistoryIdeal hT hcpt :=
  ⟨AddMonoidHomClass.isometry_of_norm _ fun f => norm_logRepresentation hT hcpt hinj hH f,
    logRepresentation_mem_openHistoryIdeal hT hcpt hinj hH⟩

/-- **(SAC.15) on histories**: the representative of `ι_T(f)` at the aperture `ε` is
`f(log T − log ε)` (with value `0` on `ker T`). -/
theorem logRepresentation_history (f : C₀(ℝ, ℂ)) (ε : Aperture) :
    logRepresentation hT hcpt f =
        coronaMk H (cfcₙ (logSymbol f) (germHistory hT hcpt one_pos)) ∧
      compactIncl H (historyEval ε (cfcₙ (logSymbol f) (germHistory hT hcpt one_pos))) =
        cfc (fun z : ℂ => if 0 < z.re then f (Real.log z.re - Real.log ε) else 0) T := by
  refine ⟨cfcₙ_scaleGerm hT hcpt one_pos (logSymbol f) (continuous_logSymbol f)
    (logSymbol_zero f),
    ?_⟩
  have hε : (0 : ℝ) < ε := ε.2.1
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hsC : ∀ z ∈ spectrum ℂ T, z = (z.re : ℂ) ∧ 0 ≤ z.re := fun z hz => by
    have hre : z = (z.re : ℂ) := hT.isSelfAdjoint.mem_spectrum_eq_re hz
    refine ⟨hre, ?_⟩
    rw [hre] at hz
    exact (hspec ((spectrum.algebraMap_mem_iff ℂ (R := ℝ) (A := H →L[ℂ] H)).mp hz)).1
  have hgcont :
      ContinuousOn (fun z : ℂ => ((z.re / ((ε : ℝ) + z.re) : ℝ) : ℂ)) (spectrum ℂ T) :=
    (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.continuousOn.div
      (continuousOn_const.add Complex.continuous_re.continuousOn) fun z hz =>
        (show (0 : ℝ) < ε + z.re by linarith [(hsC z hz).2]).ne'))
  rw [cfcₙ_germHistory_apply hT hcpt one_pos (logSymbol f) (continuous_logSymbol f)
    (logSymbol_zero f), div_one, positiveBoundaryTransfer_eq_cfc_complex T hT,
    ← cfc_comp _ _ T hT.isSelfAdjoint.isStarNormal (continuous_logSymbol f).continuousOn hgcont]
  refine cfc_congr fun z hz => ?_
  obtain ⟨-, hz0⟩ := hsC z hz
  have hmem : z.re / ((ε : ℝ) + z.re) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hz0 (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
  simp only [Function.comp_apply]
  rw [logSymbol_ofReal f hmem, logProfile]
  rcases hz0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have h1 : z.re / ((ε : ℝ) + z.re) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    rw [if_pos ⟨div_pos hpos (by linarith), h1⟩, if_pos hpos]
    congr 1
    rw [apertureLogit, ← Real.log_div hpos.ne' hε.ne']
    congr 1
    have hd : (0 : ℝ) < ε + z.re := by linarith
    field_simp
    rw [add_sub_cancel_right, div_self hε.ne']

include hinj hH in
/-- **Aperture dilation implements translation**: `ι_T(f(· + log c))` is the functional
calculus of `e_c`, whose history is the dilation `ε ↦ E_{ε/c}(T)` of the history of `e_1`. -/
theorem logRepresentation_translate {c : ℝ} (hc : 0 < c) (f : C₀(ℝ, ℂ)) :
    logRepresentation hT hcpt (translateC0 (Real.log c) f) =
      cfcₙ (logSymbol f) (scaleGerm T hT hcpt hc) := by
  have hσ := quasispectrum_unitGerm hT hcpt hinj hH
  have hφ : ContinuousOn (scaleChange c) (quasispectrum ℂ (unitGerm hT hcpt)) := by
    rw [hσ]; exact continuousOn_scaleChange hc
  rw [scaleGerm_eq_cfcₙ hT hcpt hinj hH hc, ← cfcₙ_comp (logSymbol f) (scaleChange c) _
    (continuous_logSymbol f).continuousOn (logSymbol_zero f) hφ (by simp [scaleChange])
    (isStarNormal_unitGerm hT hcpt)]
  unfold logRepresentation
  refine cfcₙ_congr fun z hz => ?_
  rw [hσ] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [Function.comp_apply, scaleChange_ofReal]
  have hφt : c * t / (1 + (c - 1) * t) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (mul_nonneg hc.le ht.1) (scaleChange_denom_pos hc ht).le,
      (div_le_one (scaleChange_denom_pos hc ht)).mpr (by nlinarith [ht.1, ht.2])⟩
  rw [logSymbol_ofReal _ ht, logSymbol_ofReal _ hφt, logProfile, logProfile]
  rcases ht.1.eq_or_lt with rfl | h0
  · simp
  rcases ht.2.eq_or_lt with rfl | h1
  · simp [hc.ne']
  have hmem := realScaleChange_mem_Ioo hc h0 h1
  rw [if_pos ⟨h0, h1⟩, if_pos (show 0 < c * t / (1 + (c - 1) * t) ∧
    c * t / (1 + (c - 1) * t) < 1 from hmem), translateC0_apply]
  congr 1
  exact (apertureLogit_realScaleChange hc h0 h1).symm

end Representation

end GaloisForLFunctions.HTGeometry
