import GaloisForLFunctions.RHTower.ThetaReflectedJumpExponents

/-!
# Theta Xi as the characteristic function of a radial density on ℝ³

Let `ν̃(r) = -k'(r)/r` (the slope of `k'` at the seam, continuous with `ν̃(0) = -k''(0)`) and
`M = Ξ(0)`.  The radial function `f₃(y) = ν̃(|y|)/(2πM)` on `ℝ³` is a continuous probability
density with `f₃(0) = -k''(0)/(2πM)`, and

`∫_{ℝ³} e^{i⟨y, ξ⟩} f₃(y) dy = Ξ(|ξ|)/M`   for every `ξ ∈ ℝ³`.

Proof: a reflection carries `ξ` to `|ξ| e₀`; the measure-preserving split `ℝ³ = ℝ × ℝ²` and the
radial integration formula on `ℝ²` give the Archimedes projection
`∫_{ℝ²} ν̃(√(c² + |z|²)) dz = 2π ∫_{|c|}^∞ s ν̃(s) ds = 2π k(c)`, so the marginal of `f₃` on each
axis is `k/M`, whose Fourier transform is `Ξ/M`.  Consequently `ξ ↦ Ξ(|ξ|)/M` is positive definite
on `ℝ³`.
-/
open Complex Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate ComplexOrder

namespace RHTower

noncomputable section

/-! ## The continuous Lévy profile -/

/-- The Lévy density continued through the seam: `ν̃(r) = -k'(r)/r`, `ν̃(0) = -k''(0)`. -/
def thetaLevyProfile (r : ℝ) : ℝ := -dslope (deriv thetaCuspFullSource) 0 r

theorem thetaLevyProfile_of_ne {r : ℝ} (hr : r ≠ 0) : thetaLevyProfile r = thetaLevyDensity r := by
  rw [thetaLevyProfile, dslope_of_ne _ hr, slope_def_field, deriv_thetaCuspFullSource_zero,
    thetaLevyDensity, thetaJumpDensity]
  field_simp
  ring

theorem thetaLevyProfile_zero :
    thetaLevyProfile 0 = -iteratedDeriv 2 thetaCuspFullSource 0 := by
  rw [thetaLevyProfile, dslope_same, iteratedDeriv_succ, iteratedDeriv_one]

theorem continuous_thetaLevyProfile : Continuous thetaLevyProfile := by
  have hd : Differentiable ℝ (deriv thetaCuspFullSource) :=
    fun y => ((contDiff_thetaCuspFullSource.differentiable_iteratedDeriv 1 (by simp)) y).congr_of_eventuallyEq
      (Eventually.of_forall fun z => by rw [iteratedDeriv_one])
  refine (continuous_iff_continuousAt.mpr fun r => ?_).neg
  rcases eq_or_ne r 0 with rfl | hr
  · exact continuousAt_dslope_same.mpr (hd 0)
  · exact (continuousAt_dslope_of_ne hr).mpr (hd r).continuousAt

/-! ## Splitting `ℝ³ = ℝ × ℝ²` -/

/-- The measurable equivalence `ℝ³ ≃ ℝ × ℝ²`, `y ↦ (y₀, (y₁, y₂))`. -/
def euclideanThreeSplit : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem measurePreserving_euclideanThreeSplit :
    MeasurePreserving euclideanThreeSplit volume volume := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) volume
      (volume.prod volume) := by
    simpa only [← volume_pi] using measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0
  have h3 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))
  rw [Measure.volume_eq_prod]
  exact h3.comp (h2.comp h1)

theorem euclideanThreeSplit_fst (y : EuclideanSpace ℝ (Fin 3)) : (euclideanThreeSplit y).1 = y 0 :=
  rfl

theorem norm_eq_euclideanThreeSplit (y : EuclideanSpace ℝ (Fin 3)) :
    ‖y‖ = √((y 0) ^ 2 + ‖(euclideanThreeSplit y).2‖ ^ 2) := by
  have h2 : ‖(euclideanThreeSplit y).2‖ ^ 2 = (y 1) ^ 2 + (y 2) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [euclideanThreeSplit]
    rfl
  rw [h2, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  ring_nf

/-! ## The two-dimensional slices -/

/-- `∫_a^∞ ω = k(a)`. -/
theorem integral_Ioi_thetaJumpDensity (a : ℝ) :
    ∫ x in Ioi a, thetaJumpDensity x = thetaCuspFullSource a := by
  simp only [thetaJumpDensity]
  rw [integral_neg, integral_Ioi_of_hasDerivAt_of_tendsto (m := 0)
    continuous_thetaCuspFullSource.continuousWithinAt
    (fun x _ => (differentiable_thetaCuspFullSource x).hasDerivAt)
    integrable_deriv_thetaCuspFullSource.integrableOn tendsto_thetaCuspFullSource_atTop_zero]
  ring

theorem sqrt_sq_add_sq_pos {c : ℝ} (hc : c ≠ 0) (r : ℝ) : 0 < √(c ^ 2 + r ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

/-- `r ν̃(√(c² + r²)) = ω(√(c² + r²)) · r/√(c² + r²)` and it decays like `e^{-r}`. -/
theorem mul_thetaLevyProfile_sqrt {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    r * thetaLevyProfile (√(c ^ 2 + r ^ 2)) =
      thetaJumpDensity (√(c ^ 2 + r ^ 2)) * (r / √(c ^ 2 + r ^ 2)) := by
  have hs := sqrt_sq_add_sq_pos hc r
  rw [thetaLevyProfile_of_ne hs.ne', thetaLevyDensity]
  field_simp

theorem integrableOn_mul_thetaLevyProfile_sqrt {c : ℝ} (hc : c ≠ 0) :
    IntegrableOn (fun r => r * thetaLevyProfile (√(c ^ 2 + r ^ 2))) (Ici 0) := by
  obtain ⟨C, hC, h⟩ := exists_abs_thetaJumpDensity_le 1
  have hcont : Continuous fun r => r * thetaLevyProfile (√(c ^ 2 + r ^ 2)) := by
    have := continuous_thetaLevyProfile; fun_prop
  refine (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul C).mono'
    hcont.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun r hr => ?_)))
  have hr : (0 : ℝ) ≤ r := le_of_lt hr
  have hs := sqrt_sq_add_sq_pos hc r
  have hrs : r ≤ √(c ^ 2 + r ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg c])
  rw [mul_thetaLevyProfile_sqrt hc, Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hr,
    abs_of_pos hs]
  have hq : r / √(c ^ 2 + r ^ 2) ≤ 1 := (div_le_one hs).mpr hrs
  calc |thetaJumpDensity √(c ^ 2 + r ^ 2)| * (r / √(c ^ 2 + r ^ 2))
      ≤ C * Real.exp (-(1 * |√(c ^ 2 + r ^ 2)|)) * 1 :=
        mul_le_mul (h _) hq (by positivity) (by positivity)
    _ ≤ C * Real.exp (-1 * r) := by
        rw [mul_one, abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC

/-- `∫₀^∞ r ν̃(√(c² + r²)) dr = k(c)` for `c ≠ 0`. -/
theorem integral_mul_thetaLevyProfile_sqrt {c : ℝ} (hc : c ≠ 0) :
    ∫ r in Ioi (0 : ℝ), r * thetaLevyProfile (√(c ^ 2 + r ^ 2)) = thetaCuspFullSource c := by
  set f : ℝ → ℝ := fun r => √(c ^ 2 + r ^ 2)
  have hf0 : f 0 = |c| := by simp [f, Real.sqrt_sq_eq_abs]
  have hcont : ContinuousOn f (Ici 0) := by fun_prop
  have htend : Tendsto f atTop atTop :=
    tendsto_atTop_mono (fun r => Real.le_sqrt_of_sq_le (by simp only [id]; nlinarith [sq_nonneg c]))
      tendsto_id
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt f (x / √(c ^ 2 + x ^ 2)) (Ioi x) x := by
    intro x _
    have hpos : c ^ 2 + x ^ 2 ≠ 0 := by positivity
    have h := ((hasDerivAt_pow 2 x).const_add (c ^ 2)).sqrt hpos
    refine h.hasDerivWithinAt.congr_deriv ?_
    field_simp
    ring
  have hg : ContinuousOn thetaJumpDensity (f '' Ioi 0) := continuous_thetaJumpDensity.continuousOn
  have hgi : IntegrableOn thetaJumpDensity (f '' Ici 0) := integrable_thetaJumpDensity.integrableOn
  have hgf : IntegrableOn (fun x => (thetaJumpDensity ∘ f) x * (x / √(c ^ 2 + x ^ 2))) (Ici 0) := by
    refine (integrableOn_mul_thetaLevyProfile_sqrt hc).congr_fun (fun x _ => ?_) measurableSet_Ici
    simp only [Function.comp, f]
    rw [mul_thetaLevyProfile_sqrt hc]
  have key := integral_comp_mul_deriv_Ioi hcont htend hderiv hg hgi hgf
  rw [hf0, integral_Ioi_thetaJumpDensity] at key
  have habs : thetaCuspFullSource |c| = thetaCuspFullSource c := by
    rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, thetaCuspFullSource_neg]
  rw [← habs, ← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [Function.comp, f]
  rw [mul_thetaLevyProfile_sqrt hc]

/-- **The two-dimensional slice.** `∫_{ℝ²} ν̃(√(c² + |z|²)) dz = 2π k(c)` for `c ≠ 0`. -/
theorem integral_thetaLevyProfile_slice {c : ℝ} (hc : c ≠ 0) :
    ∫ z : EuclideanSpace ℝ (Fin 2), thetaLevyProfile (√(c ^ 2 + ‖z‖ ^ 2)) =
      2 * Real.pi * thetaCuspFullSource c := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r => thetaLevyProfile (√(c ^ 2 + r ^ 2)))
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul] at h
  rw [h]
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, Real.pi_pos.le]
  rw [hball, integral_mul_thetaLevyProfile_sqrt hc]
  ring

theorem integrable_thetaLevyProfile_slice {c : ℝ} (hc : c ≠ 0) :
    Integrable fun z : EuclideanSpace ℝ (Fin 2) => thetaLevyProfile (√(c ^ 2 + ‖z‖ ^ 2)) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (f := fun r => thetaLevyProfile (√(c ^ 2 + r ^ 2)))).mpr
  simp only [finrank_euclideanSpace_fin, Nat.reduceSub, pow_one, smul_eq_mul] at h
  exact h ((integrableOn_mul_thetaLevyProfile_sqrt hc).mono_set Ioi_subset_Ici_self)

theorem thetaLevyProfile_sqrt_pos {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    0 < thetaLevyProfile (√(c ^ 2 + r ^ 2)) := by
  have hs := sqrt_sq_add_sq_pos hc r
  rw [thetaLevyProfile_of_ne hs.ne']
  exact thetaLevyDensity_pos hs

/-! ## The radial density on `ℝ³` -/

/-- The radial density `f₃(y) = ω(|y|)/(2πM|y|)` on `ℝ³`, with value `-k''(0)/(2πM)` at `0`. -/
def thetaSphericalDensity (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  thetaLevyProfile ‖y‖ / (2 * Real.pi * Xi 0)

theorem continuous_thetaSphericalDensity : Continuous thetaSphericalDensity :=
  (continuous_thetaLevyProfile.comp continuous_norm).div_const _

theorem thetaSphericalDensity_of_ne {y : EuclideanSpace ℝ (Fin 3)} (hy : y ≠ 0) :
    thetaSphericalDensity y = thetaJumpDensity ‖y‖ / (2 * Real.pi * Xi 0 * ‖y‖) := by
  rw [thetaSphericalDensity, thetaLevyProfile_of_ne (norm_ne_zero_iff.mpr hy), thetaLevyDensity]
  field_simp

theorem thetaSphericalDensity_zero :
    thetaSphericalDensity 0 = -iteratedDeriv 2 thetaCuspFullSource 0 / (2 * Real.pi * Xi 0) := by
  rw [thetaSphericalDensity, norm_zero, thetaLevyProfile_zero]

theorem thetaSphericalDensity_nonneg (y : EuclideanSpace ℝ (Fin 3)) : 0 ≤ thetaSphericalDensity y := by
  have hM := Xi_zero_pos
  rcases eq_or_ne y 0 with rfl | hy
  · -- the seam value is a limit of positive values
    have hcont := (continuous_thetaLevyProfile.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hnn : 0 ≤ thetaLevyProfile 0 := ge_of_tendsto hcont (eventually_nhdsWithin_of_forall
      fun r (hr : 0 < r) => by rw [thetaLevyProfile_of_ne hr.ne']; exact (thetaLevyDensity_pos hr).le)
    rw [thetaSphericalDensity, norm_zero]
    positivity
  · rw [thetaSphericalDensity, thetaLevyProfile_of_ne (norm_ne_zero_iff.mpr hy)]
    have := thetaLevyDensity_pos (norm_pos_iff.mpr hy)
    positivity

/-- The integrand on `ℝ × ℝ²` after splitting. -/
def sphericalAxisIntegrand (s : ℝ) (p : ℝ × EuclideanSpace ℝ (Fin 2)) : ℂ :=
  cexp (s * p.1 * I) *
    ((thetaLevyProfile (√(p.1 ^ 2 + ‖p.2‖ ^ 2)) / (2 * Real.pi * Xi 0) : ℝ) : ℂ)

theorem sphericalAxisIntegrand_split (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    sphericalAxisIntegrand s (euclideanThreeSplit y) =
      cexp (s * y 0 * I) * (thetaSphericalDensity y : ℂ) := by
  rw [sphericalAxisIntegrand, thetaSphericalDensity, norm_eq_euclideanThreeSplit,
    euclideanThreeSplit_fst]

theorem integral_sphericalAxisIntegrand_slice (s : ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫ z : EuclideanSpace ℝ (Fin 2), sphericalAxisIntegrand s (c, z) =
      cexp (s * c * I) * ((thetaCuspFullSource c / Xi 0 : ℝ) : ℂ) := by
  have hM := Xi_zero_pos
  simp only [sphericalAxisIntegrand]
  rw [integral_const_mul, integral_complex_ofReal, integral_div, integral_thetaLevyProfile_slice hc]
  congr 2
  field_simp

theorem integrable_sphericalAxisIntegrand (s : ℝ) :
    Integrable (sphericalAxisIntegrand s) (volume.prod volume) := by
  have hM := Xi_zero_pos
  have hcont : Continuous (sphericalAxisIntegrand s) := by
    unfold sphericalAxisIntegrand
    have := continuous_thetaLevyProfile
    fun_prop
  refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure ℝ)) 0)] with c hc
    simp only [sphericalAxisIntegrand]
    exact (((integrable_thetaLevyProfile_slice hc).div_const _).ofReal).const_mul _
  · have hk : Integrable fun c : ℝ => thetaCuspFullSource c / Xi 0 :=
      integrable_thetaCuspFullSource'.div_const _
    refine hk.congr ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure ℝ)) 0)] with c hc
    simp only [sphericalAxisIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (s : ℂ) * c * I = ((s * c : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    simp only [one_mul]
    have hpos : ∀ z : EuclideanSpace ℝ (Fin 2),
        |thetaLevyProfile (√(c ^ 2 + ‖z‖ ^ 2)) / (2 * Real.pi * Xi 0)| =
          thetaLevyProfile (√(c ^ 2 + ‖z‖ ^ 2)) / (2 * Real.pi * Xi 0) := fun z =>
      abs_of_pos (div_pos (thetaLevyProfile_sqrt_pos hc _) (by positivity))
    simp_rw [hpos]
    rw [integral_div, integral_thetaLevyProfile_slice hc]
    field_simp

theorem integrable_thetaSphericalDensity : Integrable thetaSphericalDensity := by
  have h := (measurePreserving_euclideanThreeSplit.integrable_comp_emb
    euclideanThreeSplit.measurableEmbedding).mpr
    (by rw [Measure.volume_eq_prod]; exact integrable_sphericalAxisIntegrand 0)
  have h' := h.norm
  refine h'.congr (Eventually.of_forall fun y => ?_)
  simp only [Function.comp, sphericalAxisIntegrand_split, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (thetaSphericalDensity_nonneg y)

/-- **Archimedes projection.** Along the first axis, `∫_{ℝ³} e^{i s y₀} f₃(y) dy = Ξ(s)/M`. -/
theorem integral_cexp_axis_mul_thetaSphericalDensity (s : ℝ) :
    ∫ y : EuclideanSpace ℝ (Fin 3), cexp (s * y 0 * I) * (thetaSphericalDensity y : ℂ) =
      XiC s / Xi 0 := by
  have hM : (Xi 0 : ℂ) ≠ 0 := by exact_mod_cast Xi_zero_pos.ne'
  simp_rw [← sphericalAxisIntegrand_split]
  rw [measurePreserving_euclideanThreeSplit.integral_comp' (sphericalAxisIntegrand s),
    Measure.volume_eq_prod, integral_prod _ (integrable_sphericalAxisIntegrand s)]
  have hae : (fun c : ℝ => ∫ z : EuclideanSpace ℝ (Fin 2), sphericalAxisIntegrand s (c, z)) =ᵐ[volume]
      fun c => cexp (s * c * I) * ((thetaCuspFullSource c / Xi 0 : ℝ) : ℂ) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure ℝ)) 0)] with c hc
    exact integral_sphericalAxisIntegrand_slice s hc
  rw [integral_congr_ae hae]
  have hX : XiC s = ∫ c : ℝ, cexp (s * c * I) * (thetaCuspFullSource c : ℂ) := by
    rw [← HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all, thetaCuspFourierLaplace,
      ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    simp only [thetaCuspFourierLaplaceIntegrand, thetaCuspFullSource_neg, Complex.ofReal_neg]
    ring_nf
  rw [hX, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  push_cast
  ring

/-- **Spherical integration (8).** `∫_{ℝ³} e^{i⟨y, ξ⟩} f₃(y) dy = Ξ(|ξ|)/M` for every `ξ ∈ ℝ³`. -/
theorem integral_cexp_inner_mul_thetaSphericalDensity (ξ : EuclideanSpace ℝ (Fin 3)) :
    ∫ y : EuclideanSpace ℝ (Fin 3), cexp (⟪y, ξ⟫ * I) * (thetaSphericalDensity y : ℂ) =
      XiC ‖ξ‖ / Xi 0 := by
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hinner : ∀ y : EuclideanSpace ℝ (Fin 3), ⟪y, e⟫ = y 0 := fun y => by
    simp [e, EuclideanSpace.inner_single_right]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h := integral_cexp_axis_mul_thetaSphericalDensity 0
    simp only [Complex.ofReal_zero, zero_mul, norm_zero] at h ⊢
    simpa using h
  set v : EuclideanSpace ℝ (Fin 3) := ‖ξ‖⁻¹ • ξ
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)
  set R := (ℝ ∙ (e - v))ᗮ.reflection
  have hRe : R e = v := Submodule.reflection_sub (by rw [he, hv])
  have hξR : ξ = ‖ξ‖ • R e := by
    rw [hRe]; simp only [v, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), one_smul]
  have hmp := R.measurePreserving
  have hcomp := hmp.integral_comp' (f := R.toMeasurableEquiv)
    (fun y => cexp (⟪y, ξ⟫ * I) * (thetaSphericalDensity y : ℂ))
  rw [← hcomp, ← integral_cexp_axis_mul_thetaSphericalDensity ‖ξ‖]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv]
  have hn : thetaSphericalDensity (R y) = thetaSphericalDensity y := by
    simp only [thetaSphericalDensity, LinearIsometryEquiv.norm_map]
  rw [hn]
  congr 2
  conv_lhs => rw [hξR]
  rw [inner_smul_right, LinearIsometryEquiv.inner_map_map, hinner]
  push_cast; ring

/-- `f₃` is a probability density on `ℝ³`. -/
theorem integral_thetaSphericalDensity :
    ∫ y : EuclideanSpace ℝ (Fin 3), thetaSphericalDensity y = 1 := by
  have h := integral_cexp_inner_mul_thetaSphericalDensity 0
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, norm_zero,
    integral_complex_ofReal] at h
  have hM : (Xi 0 : ℂ) ≠ 0 := by exact_mod_cast Xi_zero_pos.ne'
  have hX : XiC 0 = (Xi 0 : ℂ) := by simpa using XiC_ofReal 0
  rw [hX, div_self hM] at h
  exact_mod_cast h

/-- **Positive definiteness on `ℝ³`.** `ξ ↦ Ξ(|ξ|)/M` is positive definite. -/
theorem XiC_norm_positiveDefinite {n : ℕ} (ξ : Fin n → EuclideanSpace ℝ (Fin 3)) (c : Fin n → ℂ) :
    0 ≤ ∑ j, ∑ k, c j * conj (c k) * (XiC ‖ξ j - ξ k‖ / Xi 0) := by
  have hf := integrable_thetaSphericalDensity
  set e : Fin n → EuclideanSpace ℝ (Fin 3) → ℂ := fun j y => cexp (⟪y, ξ j⟫ * I)
  have hnorm : ∀ j y, ‖e j y‖ = 1 := fun j y => by
    simp only [e]; exact Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ j k, Integrable fun y => c j * conj (c k) *
      (cexp (⟪y, ξ j - ξ k⟫ * I) * (thetaSphericalDensity y : ℂ)) := by
    intro j k
    refine (hf.ofReal.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun y => ?_)).const_mul _
    rw [show (⟪y, ξ j - ξ k⟫ : ℂ) * I = ((⟪y, ξ j - ξ k⟫ : ℝ) : ℂ) * I from rfl,
      Complex.norm_exp_ofReal_mul_I]
  simp_rw [← integral_cexp_inner_mul_thetaSphericalDensity]
  simp_rw [← integral_const_mul]
  have hswap : ∑ j, ∑ k, ∫ y, c j * conj (c k) *
      (cexp (⟪y, ξ j - ξ k⟫ * I) * (thetaSphericalDensity y : ℂ)) =
      ∫ y, ∑ j, ∑ k, c j * conj (c k) *
        (cexp (⟪y, ξ j - ξ k⟫ * I) * (thetaSphericalDensity y : ℂ)) := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k]
  rw [hswap]
  have hpt : ∀ y, ∑ j, ∑ k, c j * conj (c k) *
      (cexp (⟪y, ξ j - ξ k⟫ * I) * (thetaSphericalDensity y : ℂ)) =
      ((‖∑ j, c j * e j y‖ ^ 2 * thetaSphericalDensity y : ℝ) : ℂ) := by
    intro y
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [e, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [inner_sub_right, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    field_simp
    have h1 : cexp (I * ((⟪y, ξ k⟫ : ℝ) : ℂ)) * cexp (-(I * ((⟪y, ξ k⟫ : ℝ) : ℂ))) = 1 := by
      rw [← Complex.exp_add]; simp
    linear_combination (-(c j * conj (c k) * (thetaSphericalDensity y : ℂ))) * h1
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun y =>
    mul_nonneg (by positivity) (thetaSphericalDensity_nonneg y))

end

end RHTower
