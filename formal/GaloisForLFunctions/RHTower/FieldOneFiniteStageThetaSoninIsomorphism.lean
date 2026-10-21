import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassSonin
import GaloisForLFunctions.RHTower.FieldOneFiniteStageThetaSourceNormalization
import GaloisForLFunctions.RHTower.ConstrainedProlateOperator

/-!
# Semilocal Sonin stability `θ_S : Sonin_λ(ℝ) ≃ Sonin_λ(X_S)`

Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, Theorem 4.6, for every
finite set `S` of finite places of `ℚ` and every aperture `λ`.

The literal theta transport `θ_S = c · w_S⁻¹ ∘ w_∞ ∘ E_S`, with the Euler operator
`E_S = ∏_{p ∈ S} (1 - p^{-1/2} U_p^*)`, is the unique bounded extension of
`f ↦ E(σ_S ⊗ f)` from even Schwartz functions (`FieldOneFiniteStageThetaSourceNormalization`).
Neither Sonin space is defined through `θ_S`: `Sonin_λ(X_S)` is the common kernel of the literal
cutoff `1_{|x|_S ≤ λ}` and of the same cutoff after the semilocal Fourier unitary
(`FieldOneFiniteStageClassSonin`), and `Sonin_λ(ℝ)` is the even common-kernel carrier.

* `w_∞` and `w_S` carry `1_{[-λ,λ]}` and `1_{|x|_S ≤ λ}` to the same radial cutoff
  `1_{u ≤ λ}` on `L²(ℝ_+^*, d*u)`; the semilocal module of the split point of `(k,u)` is `u`.
* `U_p^* f = p^{-1/2} f(·/p)` only moves mass outward, so it preserves the closed space of even
  vectors vanishing on `[-λ,λ]`; there each Euler factor is a Neumann-invertible perturbation of
  the identity, hence `E_S` maps that space onto itself.
* `F_S θ_S = θ_S F` on the dense even-Schwartz core (`F_S σ_S = σ_S`), hence everywhere.

Consequently `θ_S f ∈ Sonin_λ(X_S) ↔ f ∈ Sonin_λ(ℝ)`, and `θ_S` restricts to a bounded linear
isomorphism of the two Sonin spaces.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set IsDedekindDomain
open scoped NNReal FourierTransform

/-! ## The common radial cutoff on `L²(ℝ_+^*, d*u)` -/

/-- Radial aperture `{u ∈ ℝ_+^* | u ≤ λ}`. -/
def fieldOnePositiveUnitsAperture (lam : ℝ) : Set ℝ≥0ˣ :=
  {u | ((u : ℝ≥0) : ℝ) ≤ lam}

theorem fieldOnePositiveUnitsAperture_measurable (lam : ℝ) :
    MeasurableSet (fieldOnePositiveUnitsAperture lam) := by
  change MeasurableSet ((fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) ⁻¹' Set.Iic lam)
  exact measurableSet_Iic.preimage
    (NNReal.continuous_coe.comp Units.continuous_val).measurable

/-- Sharp radial cutoff `1_{u ≤ λ}` on `L²(ℝ_+^*, d*u)`. -/
def fieldOnePositiveUnitsCutoff (lam : ℝ) :
    FieldOnePositiveUnitsL2 →L[ℂ] FieldOnePositiveUnitsL2 :=
  RHTower.lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) fieldOnePositiveUnitsHaarMeasure 2
    (fieldOnePositiveUnitsAperture lam) (fieldOnePositiveUnitsAperture_measurable lam)

theorem fieldOnePositiveUnitsCutoff_ae (lam : ℝ) (f : FieldOnePositiveUnitsL2) :
    fieldOnePositiveUnitsCutoff lam f =ᵐ[fieldOnePositiveUnitsHaarMeasure]
      (fieldOnePositiveUnitsAperture lam).indicator fun u => f u :=
  RHTower.lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ) fieldOnePositiveUnitsHaarMeasure 2
    (fieldOnePositiveUnitsAperture lam) (fieldOnePositiveUnitsAperture_measurable lam) f

/-! ## The archimedean side: `w_∞` -/

theorem fieldOnePositiveUnits_exp_expHomeomorph_symm (u : ℝ≥0ˣ) :
    Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm u) = ((u : ℝ≥0) : ℝ) := by
  have h := congrArg Units.val (fieldOnePositiveUnitsExpHomeomorph.apply_symm_apply u)
  exact congrArg Subtype.val h

/-- A Lebesgue a.e. identity in the logarithmic coordinate holds Haar-a.e. on `ℝ_+^*`. -/
theorem fieldOnePositiveUnits_ae_comp_log {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) :
    (fun u => F (fieldOnePositiveUnitsExpHomeomorph.symm u)) =ᵐ[fieldOnePositiveUnitsHaarMeasure]
      fun u => G (fieldOnePositiveUnitsExpHomeomorph.symm u) :=
  fieldOnePositiveUnits_aeLogToHaar
    ((MeasurePreserving.symm fieldOnePositiveUnitsExpHomeomorph.toMeasurableEquiv
      fieldOnePositiveUnitsExp_measurePreserving).quasiMeasurePreserving.ae_eq_comp h)

/-- Pointwise form of `w_∞` on all of `L²(ℝ)^ev`. -/
theorem fieldOneEvenToPositiveUnitsHaarUnitary_ae_log (f : RHTower.evenSubspace) :
    fieldOneEvenToPositiveUnitsHaarUnitary f =ᵐ[fieldOnePositiveUnitsHaarMeasure]
      fun u =>
        (GaloisForLFunctions.HTGeometry.sqrtWeight fieldOnePositiveUnitsHaarLogWeight u)⁻¹ *
          ((RHTower.logEvenUnitary f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ)
            (fieldOnePositiveUnitsExpHomeomorph.symm u) := by
  let h : Lp (α := ℝ) ℂ 2 := RHTower.logEvenUnitary f
  let j : Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure :=
    fieldOnePositiveUnitsLogPullbackUnitary.symm h
  have hpull : j =ᵐ[fieldOnePositiveUnitsLogHaarMeasure]
      fun u => h (fieldOnePositiveUnitsExpHomeomorph.symm u) :=
    Lp.coeFn_compMeasurePreserving h fieldOnePositiveUnitsExp_measurePreserving.symm
  have hweighted :
      fieldOnePositiveUnitsHaarDensityDiv j =ᵐ[fieldOnePositiveUnitsHaarMeasure]
        fun u =>
          (GaloisForLFunctions.HTGeometry.sqrtWeight fieldOnePositiveUnitsHaarLogWeight u)⁻¹ *
            h (fieldOnePositiveUnitsExpHomeomorph.symm u) := by
    filter_upwards [fieldOnePositiveUnitsHaarDensityDiv_ae j,
      fieldOnePositiveUnits_aeLogToHaar hpull] with u hdivu hpullu
    rw [hdivu, hpullu]
  simpa [fieldOneEvenToPositiveUnitsHaarUnitary, fieldOnePositiveUnitsLogPullbackUnitary,
    fieldOnePositiveUnitsHaarToLogUnitary_symm_apply, h, j] using hweighted

/-- `w_∞` carries the archimedean cutoff `1_{[-λ,λ]}` to the radial cutoff `1_{u ≤ λ}`. -/
theorem fieldOneEvenToPositiveUnitsHaarUnitary_evenIndicatorCutoff
    (lam : ℝ) (f : RHTower.evenSubspace) :
    fieldOneEvenToPositiveUnitsHaarUnitary (RHTower.evenIndicatorCutoff lam f) =
      fieldOnePositiveUnitsCutoff lam (fieldOneEvenToPositiveUnitsHaarUnitary f) := by
  set g := RHTower.evenIndicatorCutoff lam f with hg
  have hcut : ((g : RHTower.SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (RHTower.centralInterval lam).indicator fun x => (f : RHTower.SoninL2) x :=
    RHTower.indicatorCutoff_ae _ (RHTower.measurableSet_centralInterval lam) f.1
  have hcutExp := hcut.comp_tendsto RHTower.realExp_quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [fieldOneEvenToPositiveUnitsHaarUnitary_ae_log g,
    fieldOneEvenToPositiveUnitsHaarUnitary_ae_log f,
    fieldOnePositiveUnits_ae_comp_log (RHTower.logEvenUnitary_ae g),
    fieldOnePositiveUnits_ae_comp_log (RHTower.logEvenUnitary_ae f),
    fieldOnePositiveUnits_ae_comp_log hcutExp,
    fieldOnePositiveUnitsCutoff_ae lam (fieldOneEvenToPositiveUnitsHaarUnitary f)]
    with u hgu hfu hlogg hlogf hcutu hcutoff
  simp only [Function.comp_apply] at hcutu
  rw [hgu, hcutoff, hlogg, hcutu, fieldOnePositiveUnits_exp_expHomeomorph_symm]
  have hu0 : 0 < ((u : ℝ≥0) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr u.ne_zero)
  by_cases hu : u ∈ fieldOnePositiveUnitsAperture lam
  · have hmem : ((u : ℝ≥0) : ℝ) ∈ RHTower.centralInterval lam := by
      change ((u : ℝ≥0) : ℝ) ≤ lam at hu
      exact ⟨by linarith, hu⟩
    rw [indicator_of_mem hmem, indicator_of_mem hu, hfu, hlogf,
      fieldOnePositiveUnits_exp_expHomeomorph_symm]
  · have hmem : ((u : ℝ≥0) : ℝ) ∉ RHTower.centralInterval lam := fun h => hu h.2
    rw [indicator_of_notMem hmem, indicator_of_notMem hu, mul_zero, mul_zero]

/-! ## The semilocal side: `w_S` -/

/-- The point of `X_S` attached to `(k,u) ∈ K_S × ℝ_+^*` by the Haar splitting of `C_S`. -/
def fieldOneFiniteStageSplitClassPoint (S : Finset (HeightOneSpectrum ℤ))
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) : FieldOneFiniteStageClassSpace S :=
  fieldOneFiniteStageIdeleClassToClassSpace S
    ((fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm z)

/-- The semilocal module of the split point of `(k,u)` is `u`. -/
theorem fieldOneFiniteStageClassModule_splitClassPoint (S : Finset (HeightOneSpectrum ℤ))
    (z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :
    (fieldOneFiniteStageClassModule S (fieldOneFiniteStageSplitClassPoint S z) : ℝ) =
      ((z.2 : ℝ≥0) : ℝ) := by
  unfold fieldOneFiniteStageSplitClassPoint
  rw [fieldOneFiniteStageClassModule_ideleClass]
  have h2 : fieldOneFiniteStageIdeleClassUnitModule S
      ((fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm z) = z.2 :=
    congrArg Prod.snd ((fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).apply_symm_apply z)
  have h3 := congrArg (fun r : ℝ≥0ˣ => ((r : ℝ≥0) : ℝ)) h2
  simpa [fieldOneFiniteStageIdeleClassUnitModule] using h3

/-- An a.e. identity on `X_S` pulls back along the split point map. -/
theorem fieldOneFiniteStage_ae_comp_splitClassPoint (S : Finset (HeightOneSpectrum ℤ))
    {F G : FieldOneFiniteStageClassSpace S → ℂ}
    (h : F =ᵐ[fieldOneFiniteStageClassAdditiveMeasure S] G) :
    (fun z => F (fieldOneFiniteStageSplitClassPoint S z)) =ᵐ[
        fieldOneFiniteStageSplitProductHaarMeasure S]
      fun z => G (fieldOneFiniteStageSplitClassPoint S z) := by
  have h1 := (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S).quasiMeasurePreserving
    |>.ae_eq_comp h
  have h2 : (F ∘ fieldOneFiniteStageIdeleClassToClassSpace S) =ᵐ[
      fieldOneFiniteStageSplitHaarMeasure S] (G ∘ fieldOneFiniteStageIdeleClassToClassSpace S) :=
    (GaloisForLFunctions.HTGeometry.withDensity_realDensity_ae_eq
      (fieldOneFiniteStageIdeleClassModuleReal_measurable S)
      (fieldOneFiniteStageIdeleClassModuleReal_pos S)).mp h1
  exact (fieldOneFiniteStageSplit_symm_measurePreserving S).quasiMeasurePreserving.ae_eq_comp h2

/-- Pointwise form of the class-to-split-product unitary:
`(U f)(k,u) = |c|^{1/2} f(c)` at the split class `c` of `(k,u)`. -/
theorem fieldOneFiniteStageClassToSplitProductL2Unitary_ae (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassToSplitProductL2Unitary S f =ᵐ[
        fieldOneFiniteStageSplitProductHaarMeasure S]
      fun z => GaloisForLFunctions.HTGeometry.sqrtWeight
          (fieldOneFiniteStageIdeleClassModuleReal S)
          ((fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm z) *
        f (fieldOneFiniteStageSplitClassPoint S z) := by
  let g := fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S f
  have h1 : g =ᵐ[fieldOneFiniteStageSplitHaarMeasure S]
      fun c => f (fieldOneFiniteStageIdeleClassToClassSpace S c) :=
    (GaloisForLFunctions.HTGeometry.withDensity_realDensity_ae_eq
      (fieldOneFiniteStageIdeleClassModuleReal_measurable S)
      (fieldOneFiniteStageIdeleClassModuleReal_pos S)).mp
      (fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary_ae S f)
  have h2 : fieldOneFiniteStageIdeleClassHalfDensityUnitary S g =ᵐ[
      fieldOneFiniteStageSplitHaarMeasure S]
      fun c => GaloisForLFunctions.HTGeometry.sqrtWeight
          (fieldOneFiniteStageIdeleClassModuleReal S) c *
        f (fieldOneFiniteStageIdeleClassToClassSpace S c) := by
    filter_upwards [fieldOneFiniteStageIdeleClassHalfDensityUnitary_ae S g, h1] with c hc h1c
    rw [hc, h1c]
  have h3 := Lp.coeFn_compMeasurePreserving
    (fieldOneFiniteStageIdeleClassHalfDensityUnitary S g)
    (fieldOneFiniteStageSplit_symm_measurePreserving S)
  have h4 := (fieldOneFiniteStageSplit_symm_measurePreserving S).quasiMeasurePreserving
    |>.ae_eq_comp h2
  have hU : fieldOneFiniteStageClassToSplitProductL2Unitary S f =
      Lp.compMeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm
        (fieldOneFiniteStageSplit_symm_measurePreserving S)
        (fieldOneFiniteStageIdeleClassHalfDensityUnitary S g) := rfl
  rw [hU]
  filter_upwards [h3, h4] with z hz h4z
  rw [hz]
  exact h4z

/-- Product aperture `{(k,u) | u ≤ λ}` on `K_S × ℝ_+^*`. -/
def fieldOneFiniteStageSplitProductAperture (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    Set (FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :=
  Prod.snd ⁻¹' fieldOnePositiveUnitsAperture lam

theorem fieldOneFiniteStageSplitProductAperture_measurable
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    MeasurableSet (fieldOneFiniteStageSplitProductAperture S lam) :=
  (fieldOnePositiveUnitsAperture_measurable lam).preimage measurable_snd

/-- Radial cutoff `1_{u ≤ λ}` on the split product `L²(K_S × ℝ_+^*)`. -/
def fieldOneFiniteStageSplitProductCutoff (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    FieldOneFiniteStageSplitProductL2 S →L[ℂ] FieldOneFiniteStageSplitProductL2 S :=
  RHTower.lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) (fieldOneFiniteStageSplitProductHaarMeasure S) 2
    (fieldOneFiniteStageSplitProductAperture S lam)
    (fieldOneFiniteStageSplitProductAperture_measurable S lam)

theorem fieldOneFiniteStageSplitProductCutoff_ae (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)
    (f : FieldOneFiniteStageSplitProductL2 S) :
    fieldOneFiniteStageSplitProductCutoff S lam f =ᵐ[fieldOneFiniteStageSplitProductHaarMeasure S]
      (fieldOneFiniteStageSplitProductAperture S lam).indicator fun z => f z :=
  RHTower.lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ) (fieldOneFiniteStageSplitProductHaarMeasure S) 2
    (fieldOneFiniteStageSplitProductAperture S lam)
    (fieldOneFiniteStageSplitProductAperture_measurable S lam) f

/-- The class-to-split-product unitary carries `1_{|x|_S ≤ λ}` to the radial cutoff. -/
theorem fieldOneFiniteStageClassToSplitProductL2Unitary_supportCutoff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassToSplitProductL2Unitary S
        (fieldOneFiniteStageClassSupportCutoff S lam f) =
      fieldOneFiniteStageSplitProductCutoff S lam
        (fieldOneFiniteStageClassToSplitProductL2Unitary S f) := by
  apply Lp.ext
  filter_upwards [fieldOneFiniteStageClassToSplitProductL2Unitary_ae S
      (fieldOneFiniteStageClassSupportCutoff S lam f),
    fieldOneFiniteStageClassToSplitProductL2Unitary_ae S f,
    fieldOneFiniteStage_ae_comp_splitClassPoint S
      (fieldOneFiniteStageClassSupportCutoff_ae S lam f),
    fieldOneFiniteStageSplitProductCutoff_ae S lam
      (fieldOneFiniteStageClassToSplitProductL2Unitary S f)]
    with z hcut hf hpt hprod
  rw [hcut, hpt, hprod]
  have hiff : fieldOneFiniteStageSplitClassPoint S z ∈ fieldOneFiniteStageClassAperture S lam ↔
      z ∈ fieldOneFiniteStageSplitProductAperture S lam := by
    change (fieldOneFiniteStageClassModule S (fieldOneFiniteStageSplitClassPoint S z) : ℝ) ≤ lam ↔
      ((z.2 : ℝ≥0) : ℝ) ≤ lam
    rw [fieldOneFiniteStageClassModule_splitClassPoint]
  by_cases hz : z ∈ fieldOneFiniteStageSplitProductAperture S lam
  · rw [indicator_of_mem (hiff.mpr hz), indicator_of_mem hz, hf]
  · rw [indicator_of_notMem (mt hiff.mp hz), indicator_of_notMem hz, mul_zero]

/-- Radial inclusion intertwines the two radial cutoffs. -/
theorem fieldOneFiniteStageRadialInclusion_positiveUnitsCutoff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : FieldOnePositiveUnitsL2) :
    fieldOneFiniteStageRadialInclusion S (fieldOnePositiveUnitsCutoff lam f) =
      fieldOneFiniteStageSplitProductCutoff S lam (fieldOneFiniteStageRadialInclusion S f) := by
  apply Lp.ext
  have hsnd : (fun z : FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ =>
        fieldOnePositiveUnitsCutoff lam f z.2) =ᵐ[fieldOneFiniteStageSplitProductHaarMeasure S]
      fun z => (fieldOnePositiveUnitsAperture lam).indicator (fun u => f u) z.2 :=
    (measurePreserving_snd (μ := fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
      (ν := fieldOnePositiveUnitsHaarMeasure)).quasiMeasurePreserving.ae_eq_comp
      (fieldOnePositiveUnitsCutoff_ae lam f)
  filter_upwards [fieldOneFiniteStageRadialInclusion_ae S (fieldOnePositiveUnitsCutoff lam f),
    fieldOneFiniteStageRadialInclusion_ae S f, hsnd,
    fieldOneFiniteStageSplitProductCutoff_ae S lam (fieldOneFiniteStageRadialInclusion S f)]
    with z h1 h2 h3 h4
  rw [h1, h4, h3]
  by_cases hz : z.2 ∈ fieldOnePositiveUnitsAperture lam
  · rw [indicator_of_mem hz,
      indicator_of_mem (show z ∈ fieldOneFiniteStageSplitProductAperture S lam from hz), h2]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (show z ∉ fieldOneFiniteStageSplitProductAperture S lam from hz)]

/-- On `K_S`-fixed vectors, `w_S` carries `1_{|x|_S ≤ λ}` to the radial cutoff. -/
theorem fieldOneFiniteStage_supportCutoff_eq_zero_iff_sourceUnitary
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ)
    (x : fieldOneFiniteStageClassModuleOneInvariantSubmodule S) :
    fieldOneFiniteStageClassSupportCutoff S lam x.1 = 0 ↔
      fieldOnePositiveUnitsCutoff lam (fieldOneFiniteStageSourceUnitary S x) = 0 := by
  have key : fieldOneFiniteStageClassToSplitProductL2Unitary S
        (fieldOneFiniteStageClassSupportCutoff S lam x.1) =
      fieldOneFiniteStageRadialInclusion S
        (fieldOnePositiveUnitsCutoff lam (fieldOneFiniteStageSourceUnitary S x)) := by
    rw [fieldOneFiniteStageClassToSplitProductL2Unitary_supportCutoff,
      fieldOneFiniteStageClassToSplitProduct_sourceUnitary,
      fieldOneFiniteStageRadialInclusion_positiveUnitsCutoff]
  constructor
  · intro h
    rw [h, map_zero] at key
    exact (fieldOneFiniteStageRadialInclusion S).injective (key.symm.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero] at key
    exact (fieldOneFiniteStageClassToSplitProductL2Unitary S).injective
      (key.trans (map_zero _).symm)

/-! ## Support of the literal theta transport -/

theorem fieldOneFiniteStageSourceUnitary_literalThetaTransport
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageSourceUnitary S (fieldOneFiniteStageLiteralThetaTransportEquiv S f) =
      fieldOneThetaSourceNormalization •
        fieldOneEvenToPositiveUnitsHaarUnitary (fieldOneFiniteStageThetaEulerOperator S f) := by
  rw [fieldOneFiniteStageLiteralThetaTransportEquiv_apply, map_smul,
    fieldOneFiniteStageSourceUnitary_thetaTransport]

/-- `θ_S f` vanishes on `{|x|_S ≤ λ}` exactly when `E_S f` vanishes on `[-λ,λ]`. -/
theorem fieldOneFiniteStage_supportCutoff_literalTheta_eq_zero_iff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageClassSupportCutoff S lam
        (fieldOneFiniteStageLiteralThetaTransportEquiv S f).1 = 0 ↔
      RHTower.evenIndicatorCutoff lam (fieldOneFiniteStageThetaEulerOperator S f) = 0 := by
  rw [fieldOneFiniteStage_supportCutoff_eq_zero_iff_sourceUnitary,
    fieldOneFiniteStageSourceUnitary_literalThetaTransport, map_smul,
    ← fieldOneEvenToPositiveUnitsHaarUnitary_evenIndicatorCutoff, smul_eq_zero,
    LinearIsometryEquiv.map_eq_zero_iff]
  exact or_iff_right fieldOneThetaSourceNormalization_ne_zero

/-! ## Euler factors preserve vanishing on `[-λ, λ]` -/

/-- Even vectors vanishing on `[-λ, λ]`. -/
abbrev fieldOneEvenVanishing (lam : ℝ) : Submodule ℂ RHTower.evenSubspace :=
  LinearMap.ker (RHTower.evenIndicatorCutoff lam : RHTower.evenSubspace →ₗ[ℂ] RHTower.evenSubspace)

theorem mem_fieldOneEvenVanishing_iff (lam : ℝ) (f : RHTower.evenSubspace) :
    f ∈ fieldOneEvenVanishing lam ↔ RHTower.evenIndicatorCutoff lam f = 0 :=
  LinearMap.mem_ker

theorem fieldOneEvenVanishing_isClosed (lam : ℝ) :
    IsClosed (fieldOneEvenVanishing lam : Set RHTower.evenSubspace) :=
  ContinuousLinearMap.isClosed_ker (RHTower.evenIndicatorCutoff lam)

theorem fieldOne_indicatorCutoff_eq_zero_of_subset {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) {f : RHTower.SoninL2}
    (hf : RHTower.indicatorCutoff t ht f = 0) : RHTower.indicatorCutoff s hs f = 0 := by
  apply Lp.ext
  have h0 := RHTower.indicatorCutoff_ae t ht f
  rw [hf] at h0
  filter_upwards [RHTower.indicatorCutoff_ae s hs f, h0,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x h1 h2 h3
  rw [h1, h3]
  by_cases hx : x ∈ s
  · have h4 : t.indicator (fun y => f y) x = 0 := by rw [← h2, h3]; rfl
    rw [indicator_of_mem (hst hx)] at h4
    rw [indicator_of_mem hx, h4]
    rfl
  · rw [indicator_of_notMem hx]
    rfl

/-- The adjoint dilation `U_p^* f = p^{-1/2} f(·/p)` preserves vanishing on `[-λ,λ]`. -/
theorem fieldOne_evenDilationUnitary_symm_vanishing {p : ℝ} (hp : 1 < p) (lam : ℝ)
    {f : RHTower.evenSubspace} (hf : RHTower.evenIndicatorCutoff lam f = 0) :
    RHTower.evenIndicatorCutoff lam
      ((RHTower.evenDilationUnitary p (zero_lt_one.trans hp)).symm f) = 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hf' : RHTower.indicatorCutoff (RHTower.centralInterval lam)
      (RHTower.measurableSet_centralInterval lam) f.1 = 0 := congrArg Subtype.val hf
  have hsub : RHTower.centralInterval (p⁻¹ * lam) ⊆ RHTower.centralInterval lam := by
    intro x hx
    simp only [RHTower.centralInterval, mem_Icc] at hx ⊢
    have hinv0 : 0 < p⁻¹ := inv_pos.mpr hp0
    have hinv1 : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp.le
    have hlam : 0 ≤ lam := by
      by_contra hneg
      nlinarith [hx.1, hx.2, not_le.mp hneg]
    constructor <;> nlinarith [hx.1, hx.2]
  apply Subtype.ext
  change RHTower.indicatorCutoff (RHTower.centralInterval lam)
      (RHTower.measurableSet_centralInterval lam)
      (RHTower.dilation p⁻¹ (inv_pos.mpr hp0) f.1) = 0
  rw [RHTower.indicatorCutoff_dilation,
    fieldOne_indicatorCutoff_eq_zero_of_subset _ _ hsub hf', map_zero]

/-- If `A` preserves a closed subspace `K` and `‖A‖ < 1`, then `1 - A` maps `K` onto `K`. -/
theorem fieldOne_surjOn_one_sub_of_norm_lt_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (K : Submodule ℂ E) (hK : IsClosed (K : Set E))
    (A : E →L[ℂ] E) (hA : ∀ x ∈ K, A x ∈ K) (hnorm : ‖A‖ < 1) :
    Set.SurjOn ⇑(1 - A) (K : Set E) (K : Set E) := by
  intro x hx
  haveI : CompleteSpace K := hK.completeSpace_coe
  let AK : K →L[ℂ] K := A.restrict hA
  have hAK : ‖AK‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun y => ?_)
      hnorm
    change ‖A y‖ ≤ ‖A‖ * ‖(y : E)‖
    exact A.le_opNorm y
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one (R := K →L[ℂ] K) hAK
  let w : K := (↑u⁻¹ : K →L[ℂ] K) ⟨x, hx⟩
  have h1 : (↑u : K →L[ℂ] K) w = ⟨x, hx⟩ := by
    change ((↑u : K →L[ℂ] K) * ↑u⁻¹) ⟨x, hx⟩ = ⟨x, hx⟩
    rw [Units.mul_inv]
    rfl
  rw [hu] at h1
  refine ⟨w, w.2, ?_⟩
  have h2 := congrArg Subtype.val h1
  simpa [AK] using h2

/-- Each physical Euler factor `1 - p^{-1/2} U_p^*` maps the even vectors vanishing on
`[-λ,λ]` onto themselves. -/
theorem fieldOne_evenPrimeLocalFactor_mapsTo_surjOn {p : ℝ} (hp : 1 < p) (lam : ℝ) :
    Set.MapsTo (RHTower.evenPrimeLocalFactor p hp)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace) ∧
      Set.SurjOn (RHTower.evenPrimeLocalFactor p hp)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace) := by
  let K := fieldOneEvenVanishing lam
  let A : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace :=
    ((Real.sqrt p : ℂ)⁻¹) •
      ((RHTower.evenDilationUnitary p (zero_lt_one.trans hp)).symm :
        RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace)
  have hA : ∀ x ∈ K, A x ∈ K := by
    intro x hx
    rw [mem_fieldOneEvenVanishing_iff] at hx ⊢
    change RHTower.evenIndicatorCutoff lam ((Real.sqrt p : ℂ)⁻¹ •
      (RHTower.evenDilationUnitary p (zero_lt_one.trans hp)).symm x) = 0
    rw [map_smul, fieldOne_evenDilationUnitary_symm_vanishing hp lam hx, smul_zero]
  have hfac : RHTower.evenPrimeLocalFactor p hp = 1 - A := rfl
  have hnorm : ‖A‖ < 1 := by
    have hp0 : 0 < p := zero_lt_one.trans hp
    have hsqrt0 : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
    have hsqrt1 : 1 < Real.sqrt p := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one hp
    have hc : ‖(Real.sqrt p : ℂ)⁻¹‖ < 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt0]
      exact inv_lt_one_of_one_lt₀ hsqrt1
    calc ‖A‖ ≤ ‖(Real.sqrt p : ℂ)⁻¹‖ *
          ‖((RHTower.evenDilationUnitary p (zero_lt_one.trans hp)).symm :
            RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace)‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖(Real.sqrt p : ℂ)⁻¹‖ * 1 := by
          gcongr
          exact (RHTower.evenDilationUnitary p (zero_lt_one.trans hp)).symm.toLinearIsometry
            |>.norm_toContinuousLinearMap_le
      _ < 1 := by rwa [mul_one]
  rw [hfac]
  refine ⟨fun x hx => ?_, fieldOne_surjOn_one_sub_of_norm_lt_one K
    (fieldOneEvenVanishing_isClosed lam) A hA hnorm⟩
  change x - A x ∈ K
  exact K.sub_mem hx (hA x hx)

theorem fieldOne_list_prod_mapsTo_surjOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Set E) (l : List (E →L[ℂ] E))
    (h : ∀ T ∈ l, Set.MapsTo T K K ∧ Set.SurjOn T K K) :
    Set.MapsTo l.prod K K ∧ Set.SurjOn l.prod K K := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact ⟨fun x hx => hx, fun x hx => ⟨x, hx, rfl⟩⟩
  | cons T l ih =>
    rw [List.prod_cons]
    obtain ⟨h1, h2⟩ := h T List.mem_cons_self
    obtain ⟨h3, h4⟩ := ih fun U hU => h U (List.mem_cons_of_mem _ hU)
    refine ⟨fun x hx => h1 (h3 hx), fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := h2 hy
    obtain ⟨z, hz, rfl⟩ := h4 hx
    exact ⟨z, hz, rfl⟩

/-- The finite Euler operator `E_S` maps the even vectors vanishing on `[-λ,λ]` onto
themselves. -/
theorem fieldOneFiniteStageThetaEulerOperator_mapsTo_surjOn
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    Set.MapsTo (fieldOneFiniteStageThetaEulerOperator S)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace) ∧
      Set.SurjOn (fieldOneFiniteStageThetaEulerOperator S)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace)
        (fieldOneEvenVanishing lam : Set RHTower.evenSubspace) := by
  apply fieldOne_list_prod_mapsTo_surjOn
  intro T hT
  rw [List.mem_map] at hT
  obtain ⟨v, -, rfl⟩ := hT
  exact fieldOne_evenPrimeLocalFactor_mapsTo_surjOn _ lam

/-- `E_S f` vanishes on `[-λ,λ]` exactly when `f` does. -/
theorem fieldOneFiniteStageThetaEulerOperator_vanishing_iff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : RHTower.evenSubspace) :
    RHTower.evenIndicatorCutoff lam (fieldOneFiniteStageThetaEulerOperator S f) = 0 ↔
      RHTower.evenIndicatorCutoff lam f = 0 := by
  obtain ⟨hmaps, hsurj⟩ := fieldOneFiniteStageThetaEulerOperator_mapsTo_surjOn S lam
  constructor
  · intro h
    obtain ⟨z, hz, hzf⟩ := hsurj ((mem_fieldOneEvenVanishing_iff lam _).mpr h)
    have hzf' : z = f := (fieldOneFiniteStageThetaEulerEquiv S).injective hzf
    rw [← hzf']
    exact (mem_fieldOneEvenVanishing_iff lam z).mp hz
  · exact fun h => (mem_fieldOneEvenVanishing_iff lam _).mp
      (hmaps ((mem_fieldOneEvenVanishing_iff lam f).mpr h))

/-! ## Fourier compatibility `F_S θ_S = θ_S F` -/

theorem fieldOne_schwartzEvenPart_eq_self {g : SchwartzMap ℝ ℂ} (hg : ∀ x, g (-x) = g x) :
    RHTower.schwartzEvenPart g = g := by
  ext x
  rw [RHTower.schwartzEvenPart_apply, hg]
  ring

/-- For even Schwartz `f`, the inverse Fourier transform is the Fourier transform. -/
theorem fieldOne_fourierInv_eq_fourier_of_even {f : SchwartzMap ℝ ℂ} (hf : ∀ x, f (-x) = f x) :
    𝓕⁻ f = 𝓕 f := by
  ext w
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun x => f (-x)) = (f : ℝ → ℂ) := funext hf
  rw [hfun]

/-- The Fourier transform of an even Schwartz function is even. -/
theorem fieldOne_fourier_even_of_even {f : SchwartzMap ℝ ℂ} (hf : ∀ x, f (-x) = f x) (w : ℝ) :
    𝓕 f (-w) = 𝓕 f w := by
  have h : (𝓕 f) (-w) = (𝓕⁻ f) w := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  rw [h, fieldOne_fourierInv_eq_fourier_of_even hf]

theorem fieldOne_ccmEvenSchwartzSource_fourier_of_even {f : SchwartzMap ℝ ℂ}
    (hf : ∀ x, f (-x) = f x) :
    RHTower.ccmEvenSchwartzSource (𝓕 f) =
      RHTower.evenFourierTransform (RHTower.ccmEvenSchwartzSource f) := by
  apply Subtype.ext
  rw [RHTower.coe_evenFourierTransform_apply]
  change (RHTower.schwartzEvenPart (𝓕 f)).toLp 2 volume =
    RHTower.fourierUnitary ((RHTower.schwartzEvenPart f).toLp 2 volume)
  rw [fieldOne_schwartzEvenPart_eq_self hf,
    fieldOne_schwartzEvenPart_eq_self (fieldOne_fourier_even_of_even hf)]
  exact (SchwartzMap.toLp_fourier_eq f).symm

/-- **Fourier compatibility of `θ_S`.**  On all of `L²(ℝ)^ev`,
`F_S (θ_S f) = θ_S (F f)`. -/
theorem fieldOneFiniteStageClassFourierUnitary_literalTheta
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageClassFourierUnitary S
        (fieldOneFiniteStageLiteralThetaTransportEquiv S f).1 =
      (fieldOneFiniteStageLiteralThetaTransportEquiv S (RHTower.evenFourierTransform f)).1 := by
  let θ := fieldOneFiniteStageLiteralThetaTransportEquiv S
  have hcont1 : Continuous fun f : RHTower.evenSubspace =>
      fieldOneFiniteStageClassFourierUnitary S (θ f).1 :=
    (fieldOneFiniteStageClassFourierUnitary S).continuous.comp
      (continuous_subtype_val.comp θ.continuous)
  have hcont2 : Continuous fun f : RHTower.evenSubspace =>
      (θ (RHTower.evenFourierTransform f)).1 :=
    continuous_subtype_val.comp (θ.continuous.comp RHTower.evenFourierTransform.continuous)
  have hcore : ∀ g : FieldOneEvenSchwartzSource,
      fieldOneFiniteStageClassFourierUnitary S (θ (RHTower.ccmEvenSchwartzSource g.1)).1 =
        (θ (RHTower.evenFourierTransform (RHTower.ccmEvenSchwartzSource g.1))).1 := by
    intro g
    have heven : ∀ x, (𝓕⁻ g.1) (-x) = (𝓕⁻ g.1) x := by
      rw [fieldOne_fourierInv_eq_fourier_of_even g.2]
      exact fieldOne_fourier_even_of_even g.2
    rw [← fieldOne_ccmEvenSchwartzSource_fourier_of_even g.2,
      ← fieldOne_fourierInv_eq_fourier_of_even g.2]
    change fieldOneFiniteStageClassFourierUnitary S
        (fieldOneFiniteStageLiteralThetaTransportEquiv S (RHTower.ccmEvenSchwartzSource g.1)).1 =
      (fieldOneFiniteStageLiteralThetaTransportEquiv S
        (RHTower.ccmEvenSchwartzSource (𝓕⁻ g.1))).1
    rw [← fieldOneFiniteStageThetaInvariantBruhatCore_eq_literalTransport S g.1 g.2,
      ← fieldOneFiniteStageThetaInvariantBruhatCore_eq_literalTransport S (𝓕⁻ g.1) heven]
    exact fieldOneFiniteStageClassFourier_thetaClassCore S g.1
  have heq := fieldOneEvenSchwartzSource_denseRange.equalizer hcont1 hcont2 (funext hcore)
  exact congrFun heq f

/-! ## Theorem 4.6 -/

/-- Membership in the even archimedean Sonin carrier as two vanishing conditions. -/
theorem fieldOne_mem_evenCentralSoninCarrier_iff (lam : ℝ) (f : RHTower.evenSubspace) :
    f ∈ RHTower.evenCentralSoninCarrier lam ↔
      RHTower.evenIndicatorCutoff lam f = 0 ∧
        RHTower.evenIndicatorCutoff lam (RHTower.evenFourierTransform f) = 0 := by
  change f.1 ∈ (RHTower.centralPhysicalForbidden lam)ᗮ ∧
      f.1 ∈ (RHTower.centralFourierForbidden lam)ᗮ ↔ _
  rw [← Submodule.starProjection_apply_eq_zero_iff, ← Submodule.starProjection_apply_eq_zero_iff]
  change (RHTower.physicalForbidden (Set.Icc (-lam) lam) measurableSet_Icc).starProjection f.1 = 0 ∧
      (RHTower.fourierForbidden (Set.Icc (-lam) lam) measurableSet_Icc).starProjection f.1 = 0 ↔ _
  rw [← RHTower.indicatorCutoff_eq_physicalForbidden_starProjection,
    ← RHTower.fourierCutoff_eq_fourierForbidden_starProjection, RHTower.fourierCutoff_apply, LinearIsometryEquiv.map_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩

/-- `θ_S f` lies in the literal semilocal Sonin space exactly when `f` lies in the archimedean
Sonin space. -/
theorem fieldOneFiniteStage_literalTheta_mem_semilocalSonin_iff
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageLiteralThetaTransportEquiv S f ∈
        fieldOneFiniteStageSemilocalSoninSubmodule S lam ↔
      f ∈ RHTower.evenCentralSoninCarrier lam := by
  rw [fieldOneFiniteStage_mem_semilocalSonin_iff, fieldOneFiniteStageClassFourierUnitary_literalTheta,
    fieldOneFiniteStage_supportCutoff_literalTheta_eq_zero_iff,
    fieldOneFiniteStage_supportCutoff_literalTheta_eq_zero_iff,
    fieldOneFiniteStageThetaEulerOperator_vanishing_iff,
    fieldOneFiniteStageThetaEulerOperator_vanishing_iff,
    fieldOne_mem_evenCentralSoninCarrier_iff]

/-- **Connes--Consani--Moscovici, Theorem 4.6.**  For every finite set `S` of finite places and
every aperture `λ`, the literal theta transport restricts to a bounded linear isomorphism
`Sonin_λ(ℝ) ≃ Sonin_λ(X_S)`. -/
def fieldOneFiniteStageSoninThetaEquiv (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    RHTower.evenCentralSoninCarrier lam ≃L[ℂ] fieldOneFiniteStageSemilocalSoninSubmodule S lam where
  toFun f := ⟨fieldOneFiniteStageLiteralThetaTransportEquiv S f.1,
    (fieldOneFiniteStage_literalTheta_mem_semilocalSonin_iff S lam f.1).mpr f.2⟩
  invFun g := ⟨(fieldOneFiniteStageLiteralThetaTransportEquiv S).symm g.1,
    (fieldOneFiniteStage_literalTheta_mem_semilocalSonin_iff S lam _).mp (by
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact g.2)⟩
  left_inv f := by
    apply Subtype.ext
    exact (fieldOneFiniteStageLiteralThetaTransportEquiv S).symm_apply_apply f.1
  right_inv g := by
    apply Subtype.ext
    exact (fieldOneFiniteStageLiteralThetaTransportEquiv S).apply_symm_apply g.1
  map_add' f g := by
    apply Subtype.ext
    exact map_add (fieldOneFiniteStageLiteralThetaTransportEquiv S) f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (fieldOneFiniteStageLiteralThetaTransportEquiv S) c f.1
  continuous_toFun :=
    ((fieldOneFiniteStageLiteralThetaTransportEquiv S).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((fieldOneFiniteStageLiteralThetaTransportEquiv S).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem fieldOneFiniteStageSoninThetaEquiv_apply
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : RHTower.evenCentralSoninCarrier lam) :
    ((fieldOneFiniteStageSoninThetaEquiv S lam f :
        fieldOneFiniteStageClassModuleOneInvariantSubmodule S)) =
      fieldOneFiniteStageLiteralThetaTransportEquiv S f.1 := rfl

/-- The semilocal Sonin space is exactly the `θ_S`-image of the archimedean one. -/
theorem fieldOneFiniteStageSemilocalSonin_eq_map_literalTheta
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) :
    (RHTower.evenCentralSoninCarrier lam).map
        (fieldOneFiniteStageLiteralThetaTransportEquiv S).toLinearEquiv.toLinearMap =
      fieldOneFiniteStageSemilocalSoninSubmodule S lam := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (fieldOneFiniteStage_literalTheta_mem_semilocalSonin_iff S lam f).mpr hf
  · intro hg
    refine ⟨(fieldOneFiniteStageLiteralThetaTransportEquiv S).symm g, ?_, ?_⟩
    · apply (fieldOneFiniteStage_literalTheta_mem_semilocalSonin_iff S lam _).mp
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hg
    · exact (fieldOneFiniteStageLiteralThetaTransportEquiv S).apply_symm_apply g

/-- On the Sonin spaces `θ_S` intertwines the archimedean and semilocal Fourier transforms. -/
theorem fieldOneFiniteStageSoninThetaEquiv_fourier
    (S : Finset (HeightOneSpectrum ℤ)) (lam : ℝ) (f : RHTower.evenCentralSoninCarrier lam) :
    fieldOneFiniteStageClassFourierUnitary S (fieldOneFiniteStageSoninThetaEquiv S lam f).1.1 =
      (fieldOneFiniteStageLiteralThetaTransportEquiv S (RHTower.evenFourierTransform f.1)).1 :=
  fieldOneFiniteStageClassFourierUnitary_literalTheta S f.1

end

end GaloisForLFunctions.RHTower
