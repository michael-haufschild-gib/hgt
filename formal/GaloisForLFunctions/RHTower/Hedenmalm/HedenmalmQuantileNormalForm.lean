import GaloisForLFunctions.HTGeometry.PositiveDensityQuantile
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPinnedVolterraBoundaryDefect

/-!
# The quantile normal form of the Hedenmalm source inverse

For a continuous, positive, integrable source density `k` with total mass `M`, distribution
function `p` and quantile `Q`, the probability-integral transform

`(U f)(t) = √M · f(Q t) / k(Q t)`

is a unitary of the weighted source space `H_k = L²(ℝ, k⁻¹ dx)` onto `L²(0,1)`.  It is built here
as the composition of two positive-density unitaries with the pullback along `Q`, which is measure
preserving by inverse-transform sampling.

Under `U` the explicit Hedenmalm source inverse

`(B f)(x) = i ∫_{-∞}^x (f(y) - M⁻¹ (∫ f) k(y)) dy`

becomes `i` times the quantile speed `q(t) = M / k(Q t)` times the universal pinned primitive

`(C g)(t) = ∫₀ᵗ g - t ∫₀¹ g`.

All source dependence is therefore one positive diagonal multiplier; the nonlocal part of the
operator is source independent.  The pullback of the reciprocal quantile speed is ordinary
Lebesgue `L²`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem unitIntervalMeasure_eq : unitIntervalMeasure = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [unitIntervalMeasure]
  exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm

namespace HedenmalmQuantile

variable (S : PositiveDensitySource)

/-! ### The weighted source space -/

/-- The reciprocal source weight defining `H_k = L²(ℝ, k⁻¹ dx)`. -/
def sourceWeight (x : ℝ) : ℝ := (S.k x)⁻¹

theorem sourceWeight_pos (x : ℝ) : 0 < (sourceWeight S) x := inv_pos.mpr (S.pos_k x)

theorem measurable_sourceWeight : Measurable (sourceWeight S) :=
  (S.continuous_k.measurable).inv

/-- Hedenmalm's weighted source space `H_k = L²(ℝ, k⁻¹ dx)`. -/
abbrev SourceSpace : Type := WeightedL2 (μ := volume) (sourceWeight S)

/-- Multiplication by `k^(-1/2)`, from the source space to ordinary `L²(ℝ)`. -/
def sourceToLebesgue : (SourceSpace S) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  weightedDensityUnitary (sourceWeight S) (measurable_sourceWeight S) (sourceWeight_pos S)

/-- Multiplication by `(k/M)^(1/2)`, from the law space to ordinary `L²(ℝ)`. -/
def lawToLebesgue : Lp ℂ 2 S.law ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  weightedDensityUnitary S.normalized S.measurable_normalized S.normalized_pos

/-- The source-to-law unitary `f ↦ √M f / k`. -/
def sourceToLaw : (SourceSpace S) ≃ₗᵢ[ℂ] Lp ℂ 2 S.law :=
  (sourceToLebesgue S).trans (lawToLebesgue S).symm

theorem sourceToLaw_ae (f : (SourceSpace S)) :
    sourceToLaw S f =ᵐ[volume] fun x => (Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ) := by
  have h1 : (sourceToLebesgue S) f =ᵐ[volume] fun x => sqrtWeight (sourceWeight S) x * f x :=
    densityMul_ae (sourceWeight S) (measurable_sourceWeight S) (sourceWeight_pos S) f
  have h2 : (lawToLebesgue S).symm ((sourceToLebesgue S) f) =ᵐ[volume]
      fun x => (sqrtWeight S.normalized x)⁻¹ * (sourceToLebesgue S) f x :=
    densityDiv_ae S.normalized S.measurable_normalized S.normalized_pos _
  filter_upwards [h1, h2] with x hx1 hx2
  have hk : (0 : ℝ) < S.k x := S.pos_k x
  have hM : (0 : ℝ) < S.mass := S.mass_pos
  change (lawToLebesgue S).symm ((sourceToLebesgue S) f) x = _
  rw [hx2, hx1]
  have hsw : sqrtWeight (sourceWeight S) x = (((Real.sqrt (S.k x))⁻¹ : ℝ) : ℂ) := by
    rw [sqrtWeight]
    norm_cast
    rw [show sourceWeight S x = (S.k x)⁻¹ from rfl, Real.sqrt_inv]
  have hnw : sqrtWeight S.normalized x = ((Real.sqrt (S.k x) / Real.sqrt S.mass : ℝ) : ℂ) := by
    rw [sqrtWeight]
    norm_cast
    rw [show S.normalized x = S.k x / S.mass from rfl, Real.sqrt_div hk.le]
  have hkne : Real.sqrt (S.k x) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  have hMne : Real.sqrt S.mass ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  have hkc : ((Real.sqrt (S.k x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkne
  have hMc : ((Real.sqrt S.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hMne
  have hkk : ((S.k x : ℝ) : ℂ) = (Real.sqrt (S.k x) : ℂ) * (Real.sqrt (S.k x) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hk.le]
  rw [hsw, hnw, hkk]
  push_cast
  field_simp

/-! ### The probability-integral transform -/

theorem measurePreserving_quantile_unitInterval :
    MeasurePreserving S.quantileFun unitIntervalMeasure S.law := by
  rw [unitIntervalMeasure_eq]
  exact S.measurePreserving_quantileFun

theorem measurePreserving_cdf_unitInterval :
    MeasurePreserving S.cdfFun S.law unitIntervalMeasure := by
  rw [unitIntervalMeasure_eq]
  exact S.measurePreserving_cdfFun

theorem compMeasurePreserving_eq_self {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MeasurePreserving f μ μ)
    (hid : f =ᵐ[μ] id) (g : Lp ℂ 2 μ) : Lp.compMeasurePreserving f hf g = g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving g hf, hid] with x hx hidx
  rw [hx]
  change g (f x) = g x
  rw [show f x = x from hidx]

/-- Pullback along the quantile, a unitary from the law space onto `L²(0,1)`. -/
def lawToUnitInterval : Lp ℂ 2 S.law ≃ₗᵢ[ℂ] Lp ℂ 2 unitIntervalMeasure where
  __ := Lp.compMeasurePreservingₗᵢ ℂ S.quantileFun (measurePreserving_quantile_unitInterval S)
  invFun := Lp.compMeasurePreserving S.cdfFun (measurePreserving_cdf_unitInterval S)
  left_inv g := by
    have hcomp := Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) g
      (measurePreserving_quantile_unitInterval S) (measurePreserving_cdf_unitInterval S)
    change Lp.compMeasurePreserving S.cdfFun (measurePreserving_cdf_unitInterval S)
      (Lp.compMeasurePreserving S.quantileFun (measurePreserving_quantile_unitInterval S) g) = g
    rw [← hcomp]
    exact compMeasurePreserving_eq_self _
      (Filter.Eventually.of_forall fun x => S.quantile_cdfFun x) g
  right_inv h := by
    have hcomp := Lp.compMeasurePreserving_comp_apply (E := ℂ) (p := 2) h
      (measurePreserving_cdf_unitInterval S) (measurePreserving_quantile_unitInterval S)
    change Lp.compMeasurePreserving S.quantileFun (measurePreserving_quantile_unitInterval S)
      (Lp.compMeasurePreserving S.cdfFun (measurePreserving_cdf_unitInterval S) h) = h
    rw [← hcomp]
    refine compMeasurePreserving_eq_self _ ?_ h
    rw [unitIntervalMeasure_eq]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact S.cdfFun_quantile ht

theorem lawToUnitInterval_ae (g : Lp ℂ 2 S.law) :
    lawToUnitInterval S g =ᵐ[unitIntervalMeasure] fun t => g (S.quantileFun t) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_quantile_unitInterval S)

/-- **The probability-integral transform.**  `U f = √M · f ∘ Q / k ∘ Q` is a unitary of the
weighted source space `L²(ℝ, k⁻¹ dx)` onto `L²(0,1)`. -/
def quantileUnitary : (SourceSpace S) ≃ₗᵢ[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  (sourceToLaw S).trans (lawToUnitInterval S)

theorem quantileUnitary_ae (f : (SourceSpace S)) :
    quantileUnitary S f =ᵐ[unitIntervalMeasure]
      fun t => (Real.sqrt S.mass : ℂ) * f (S.quantileFun t) / (S.k (S.quantileFun t) : ℂ) := by
  have hlaw : (sourceToLaw S f : ℝ → ℂ) =ᵐ[S.law]
      fun x => (Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ) :=
    (S.law_ae_eq).mpr (sourceToLaw_ae S f)
  have hpull := hlaw.comp_tendsto
    (measurePreserving_quantile_unitInterval S).quasiMeasurePreserving.tendsto_ae
  filter_upwards [lawToUnitInterval_ae S (sourceToLaw S f), hpull] with t h1 h2
  change lawToUnitInterval S (sourceToLaw S f) t = _
  rw [h1]
  exact h2

/-! ### Integrability of source vectors and the change of variables -/

theorem memLp_sqrt_k : MemLp (fun x => ((Real.sqrt (S.k x) : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x => ((Real.sqrt (S.k x) : ℝ) : ℂ))
      (volume : Measure ℝ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp S.continuous_k)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  refine S.integrable_k.congr ?_
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (S.pos_k x).le]

/-- Every source vector is Lebesgue integrable: `∫|f| ≤ √M ‖f‖`. -/
theorem integrable_sourceSpace (f : (SourceSpace S)) :
    Integrable (fun x => (f x : ℂ)) (volume : Measure ℝ) := by
  have h1 : MemLp (fun x => sqrtWeight (sourceWeight S) x * f x) 2 (volume : Measure ℝ) :=
    (memLp_two_withDensity_iff (measurable_sourceWeight S) (sourceWeight_pos S)).mp (Lp.memLp f)
  have hprod := MemLp.integrable_mul h1 (memLp_sqrt_k S)
  refine hprod.congr ?_
  filter_upwards with x
  have hk : (0 : ℝ) < S.k x := S.pos_k x
  have hkne : Real.sqrt (S.k x) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  have hkc : ((Real.sqrt (S.k x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkne
  have hsw : sqrtWeight (sourceWeight S) x = (((Real.sqrt (S.k x))⁻¹ : ℝ) : ℂ) := by
    rw [sqrtWeight]
    norm_cast
    rw [show sourceWeight S x = (S.k x)⁻¹ from rfl, Real.sqrt_inv]
  show sqrtWeight (sourceWeight S) x * f x * ((Real.sqrt (S.k x) : ℝ) : ℂ) = f x
  rw [hsw]
  push_cast
  field_simp

/-- **Change of variables along the quantile.**  Integration of `g ∘ Q` over the unit interval is
integration of `g` against the normalized density. -/
theorem integral_comp_quantile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hgm : AEStronglyMeasurable g (volume : Measure ℝ)) :
    ∫ u in Ioo (0 : ℝ) 1, g (S.quantileFun u) = ∫ x, S.normalized x • g x := by
  rw [← S.integral_law g, ← S.map_quantileFun_eq]
  refine (integral_map S.measurable_quantileFun.aemeasurable ?_).symm
  rw [S.map_quantileFun_eq]
  exact (S.aestronglyMeasurable_law_iff).mpr hgm

theorem quantile_preimage_Iic {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Ioo (0 : ℝ) 1 ∩ S.quantileFun ⁻¹' (Iic (S.quantileFun t)) = Ioc 0 t := by
  ext u
  simp only [mem_inter_iff, mem_Ioo, mem_preimage, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨⟨hu0, hu1⟩, hq⟩
    refine ⟨hu0, ?_⟩
    by_contra hcon
    push Not at hcon
    exact absurd (S.strictMonoOn_quantileFun ht ⟨hu0, hu1⟩ hcon) (not_lt.mpr hq)
  · rintro ⟨hu0, hut⟩
    have humem : u ∈ Ioo (0 : ℝ) 1 := ⟨hu0, lt_of_le_of_lt hut ht.2⟩
    refine ⟨humem, ?_⟩
    rcases eq_or_lt_of_le hut with rfl | hlt
    · exact le_rfl
    · exact (S.strictMonoOn_quantileFun humem ht hlt).le

/-- **Truncated change of variables.**  The `Q`-pullback over `(0,t)` is the weighted integral over
the half line below `Q t`. -/
theorem setIntegral_comp_quantile {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hgm : AEStronglyMeasurable g (volume : Measure ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ u in Ioo (0 : ℝ) t, g (S.quantileFun u)
      = ∫ x in Iic (S.quantileFun t), S.normalized x • g x := by
  have hind : AEStronglyMeasurable ((Iic (S.quantileFun t)).indicator g) (volume : Measure ℝ) :=
    hgm.indicator measurableSet_Iic
  have hmain := integral_comp_quantile S ((Iic (S.quantileFun t)).indicator g) hind
  have hleft : ∫ u in Ioo (0 : ℝ) 1,
      (Iic (S.quantileFun t)).indicator g (S.quantileFun u)
      = ∫ u in Ioo (0 : ℝ) t, g (S.quantileFun u) := by
    have hrw : (fun u => (Iic (S.quantileFun t)).indicator g (S.quantileFun u))
        = (S.quantileFun ⁻¹' (Iic (S.quantileFun t))).indicator (fun u => g (S.quantileFun u)) := by
      funext u
      by_cases hu : S.quantileFun u ∈ Iic (S.quantileFun t)
      · rw [Set.indicator_of_mem hu,
          Set.indicator_of_mem (show u ∈ S.quantileFun ⁻¹' Iic (S.quantileFun t) from hu)]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show u ∉ S.quantileFun ⁻¹' Iic (S.quantileFun t) from hu)]
    rw [hrw, setIntegral_indicator (S.measurable_quantileFun measurableSet_Iic),
      quantile_preimage_Iic S ht]
    exact setIntegral_congr_set (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
  have hright : ∫ x, S.normalized x • (Iic (S.quantileFun t)).indicator g x
      = ∫ x in Iic (S.quantileFun t), S.normalized x • g x := by
    have hrw : (fun x => S.normalized x • (Iic (S.quantileFun t)).indicator g x)
        = (Iic (S.quantileFun t)).indicator (fun x => S.normalized x • g x) := by
      funext x
      by_cases hx : x ∈ Iic (S.quantileFun t)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero]
    rw [hrw, integral_indicator measurableSet_Iic]
  rw [← hleft, ← hright, hmain]

/-! ### The source operator in quantile coordinates -/

/-- The quantile speed `q(t) = M / k(Q t)`. -/
def quantileSpeed (t : ℝ) : ℝ := S.mass / S.k (S.quantileFun t)

theorem quantileSpeed_pos (t : ℝ) : 0 < quantileSpeed S t :=
  div_pos S.mass_pos (S.pos_k _)

/-- The probability-integral transform, at the level of functions. -/
def quantileTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt S.mass : ℂ) * f (S.quantileFun t) / (S.k (S.quantileFun t) : ℂ)

/-- Hedenmalm's source inverse in explicit primitive form,
`(B f)(x) = i ∫_{-∞}^x (f - M⁻¹ (∫ f) k)`. -/
def sourceInverse (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.I * ∫ y in Iic x, (f y - ((∫ z, f z) / (S.mass : ℂ)) * (S.k y : ℂ))

theorem aestronglyMeasurable_transformIntegrand {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x => (Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ))
      (volume : Measure ℝ) := by
  have hcont : Continuous fun x : ℝ => ((S.k x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp S.continuous_k
  have hinv : Continuous fun x : ℝ => ((S.k x : ℝ) : ℂ)⁻¹ :=
    hcont.inv₀ (fun x => by exact_mod_cast (S.pos_k x).ne')
  have hconst : AEStronglyMeasurable (fun _ : ℝ => ((Real.sqrt S.mass : ℝ) : ℂ))
      (volume : Measure ℝ) := aestronglyMeasurable_const
  have hmul := (hconst.mul hf).mul hinv.aestronglyMeasurable
  refine hmul.congr ?_
  filter_upwards with x
  simp [div_eq_mul_inv]

theorem normalized_smul_transformIntegrand (f : ℝ → ℂ) (x : ℝ) :
    S.normalized x • ((Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ))
      = f x / (Real.sqrt S.mass : ℂ) := by
  have hk : (0 : ℝ) < S.k x := S.pos_k x
  have hM : (0 : ℝ) < S.mass := S.mass_pos
  have hkc : ((S.k x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMc : ((Real.sqrt S.mass : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have hMM : ((Real.sqrt S.mass : ℝ) : ℂ) * (Real.sqrt S.mass : ℂ) = (S.mass : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hM.le]
  have hnorm : ((S.normalized x : ℝ) : ℂ) = (S.k x : ℂ) / (S.mass : ℂ) := by
    rw [show S.normalized x = S.k x / S.mass from rfl]
    push_cast
    ring
  rw [Complex.real_smul, hnorm, ← hMM]
  field_simp

/-- The truncated `Q`-average of the transform is the truncated average of the source. -/
theorem setIntegral_quantileTransform {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ u in Ioo (0 : ℝ) t, quantileTransform S f u
      = (∫ y in Iic (S.quantileFun t), f y) / (Real.sqrt S.mass : ℂ) := by
  have h := setIntegral_comp_quantile S
    (fun x => (Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ))
    (aestronglyMeasurable_transformIntegrand S hf) ht
  rw [show (fun u => quantileTransform S f u)
      = fun u => (Real.sqrt S.mass : ℂ) * f (S.quantileFun u) / (S.k (S.quantileFun u) : ℂ) from
    rfl, h]
  rw [setIntegral_congr_fun measurableSet_Iic
    (fun x _ => normalized_smul_transformIntegrand S f x)]
  exact MeasureTheory.integral_div _ _

/-- The full `Q`-average of the transform is the full average of the source. -/
theorem integral_quantileTransform {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) :
    ∫ u in Ioo (0 : ℝ) 1, quantileTransform S f u = (∫ y, f y) / (Real.sqrt S.mass : ℂ) := by
  have h := integral_comp_quantile S
    (fun x => (Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ))
    (aestronglyMeasurable_transformIntegrand S hf)
  rw [show (fun u => quantileTransform S f u)
      = fun u => (Real.sqrt S.mass : ℂ) * f (S.quantileFun u) / (S.k (S.quantileFun u) : ℂ) from
    rfl, h]
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun x => normalized_smul_transformIntegrand S f x))]
  exact MeasureTheory.integral_div _ _

theorem setIntegral_Iic_k (x : ℝ) :
    ∫ y in Iic x, (S.k y : ℂ) = ((S.mass * S.cdfFun x : ℝ) : ℂ) := by
  rw [integral_complex_ofReal]
  congr 1
  have hM : S.mass ≠ 0 := S.mass_ne_zero
  rw [show S.cdfFun x = (∫ y in Iic x, S.k y) / S.mass from rfl]
  field_simp

/-- The source inverse read at the quantile point is the pinned primitive of the source. -/
theorem sourceInverse_quantileFun {f : ℝ → ℂ} (hf : Integrable f) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    sourceInverse S f (S.quantileFun t)
      = Complex.I * ((∫ y in Iic (S.quantileFun t), f y) - (t : ℂ) * ∫ z, f z) := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) := S.integrable_k.ofReal
  rw [sourceInverse, MeasureTheory.integral_sub hf.integrableOn
    ((hkC.const_mul _).integrableOn), MeasureTheory.integral_const_mul,
    setIntegral_Iic_k, S.cdfFun_quantile ht]
  congr 1
  have hMc : ((S.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast S.mass_ne_zero
  push_cast
  field_simp

/-- **The quantile normal form.**  In the intrinsic probability coordinate the Hedenmalm source
inverse is `i` times the quantile speed times the universal pinned primitive. -/
theorem quantileTransform_sourceInverse {f : ℝ → ℂ} (hf : Integrable f) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantileTransform S (sourceInverse S f) t
      = Complex.I * (quantileSpeed S t : ℂ) *
        ((∫ u in Ioo (0 : ℝ) t, quantileTransform S f u)
          - (t : ℂ) * ∫ u in Ioo (0 : ℝ) 1, quantileTransform S f u) := by
  have hM : (0 : ℝ) < S.mass := S.mass_pos
  have hk : (0 : ℝ) < S.k (S.quantileFun t) := S.pos_k _
  have hkc : ((S.k (S.quantileFun t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMc : ((Real.sqrt S.mass : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have hMM : ((Real.sqrt S.mass : ℝ) : ℂ) * (Real.sqrt S.mass : ℂ) = (S.mass : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hM.le]
  rw [quantileTransform, sourceInverse_quantileFun S hf ht,
    setIntegral_quantileTransform S hf.aestronglyMeasurable ht,
    integral_quantileTransform S hf.aestronglyMeasurable, quantileSpeed]
  push_cast
  rw [← hMM]
  field_simp

/-! ### Identification with the universal pinned primitive -/

theorem Ioo_inter_Iic {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Ioo (0 : ℝ) 1 ∩ Iic t = Ioc 0 t := by
  ext u
  simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, lt_of_le_of_lt h.2 ht.2⟩, h.2⟩⟩

theorem pinnedMean_quantileUnitary (f : (SourceSpace S)) :
    pinnedMean (quantileUnitary S f)
      = ∫ u in Ioo (0 : ℝ) 1, quantileTransform S (fun x => f x) u := by
  rw [pinnedMean, integral_congr_ae (quantileUnitary_ae S f), unitIntervalMeasure_eq]
  rfl

theorem pinnedPrefix_quantileUnitary (f : (SourceSpace S)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    pinnedPrefix (quantileUnitary S f) t
      = ∫ u in Ioo (0 : ℝ) t, quantileTransform S (fun x => f x) u := by
  have hcongr : (fun u => (Iic t).indicator (fun u => (quantileUnitary S f) u) u)
      =ᵐ[unitIntervalMeasure]
      fun u => (Iic t).indicator (fun u => quantileTransform S (fun x => f x) u) u := by
    filter_upwards [quantileUnitary_ae S f] with u hu
    by_cases hut : u ∈ Iic t
    · rw [Set.indicator_of_mem hut, Set.indicator_of_mem hut]
      exact hu
    · rw [Set.indicator_of_notMem hut, Set.indicator_of_notMem hut]
  rw [pinnedPrefix, integral_congr_ae hcongr, unitIntervalMeasure_eq,
    setIntegral_indicator measurableSet_Iic, Ioo_inter_Iic ht]
  exact setIntegral_congr_set (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)

/-- **The complete source operator has the normal form `T = i M_q C`.**  In the intrinsic
probability coordinate of the source density, the Hedenmalm source inverse is `i` times the
quantile speed times the universal pinned primitive of `L²(0,1)`. -/
theorem quantileTransform_sourceInverse_eq_pinned (f : (SourceSpace S)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    quantileTransform S (sourceInverse S (fun x => f x)) t
      = Complex.I * (quantileSpeed S t : ℂ) * pinnedVolterraFun (quantileUnitary S f) t := by
  rw [pinnedVolterraFun, pinnedPrefix_quantileUnitary S f ht, pinnedMean_quantileUnitary S f]
  exact quantileTransform_sourceInverse S (integrable_sourceSpace S f) ht

/-! ### The canonical singular metric -/

theorem inv_quantileSpeed (t : ℝ) :
    (quantileSpeed S t)⁻¹ = S.k (S.quantileFun t) / S.mass := by
  rw [quantileSpeed, inv_div]

theorem normalized_smul_metricIntegrand (f : ℝ → ℂ) (x : ℝ) :
    S.normalized x •
        ((S.k x / S.mass) * ‖(Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ)‖ ^ 2)
      = ‖f x‖ ^ 2 / S.mass := by
  have hk : (0 : ℝ) < S.k x := S.pos_k x
  have hM : (0 : ℝ) < S.mass := S.mass_pos
  have hnorm : ‖(Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ)‖
      = Real.sqrt S.mass * ‖f x‖ / S.k x := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hk.le]
  rw [hnorm, smul_eq_mul, show S.normalized x = S.k x / S.mass from rfl]
  have hsq : (Real.sqrt S.mass * ‖f x‖ / S.k x) ^ 2
      = S.mass * ‖f x‖ ^ 2 / (S.k x) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hM.le]
  rw [hsq]
  field_simp

/-- **The canonical metric pullback.**  The reciprocal quantile speed pulls the source inner
product back to ordinary Lebesgue `L²`, rescaled by the total mass. -/
theorem quantileMetric_pullback (f : (SourceSpace S)) :
    ∫ u in Ioo (0 : ℝ) 1,
        (quantileSpeed S u)⁻¹ * ‖quantileTransform S (fun x => f x) u‖ ^ 2
      = (∫ x, ‖(f x : ℂ)‖ ^ 2) / S.mass := by
  have hfm : AEStronglyMeasurable (fun x => (f x : ℂ)) (volume : Measure ℝ) :=
    (aestronglyMeasurable_withDensity_realDensity_iff (measurable_sourceWeight S)
      (sourceWeight_pos S)).mp (Lp.aestronglyMeasurable f)
  have hgm : AEStronglyMeasurable
      (fun x => (S.k x / S.mass) * ‖(Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ)‖ ^ 2)
      (volume : Measure ℝ) :=
    (((S.continuous_k.div_const S.mass).aestronglyMeasurable).mul
      (((aestronglyMeasurable_transformIntegrand S hfm).norm).pow 2))
  have hmain := integral_comp_quantile S
    (fun x => (S.k x / S.mass) * ‖(Real.sqrt S.mass : ℂ) * f x / (S.k x : ℂ)‖ ^ 2) hgm
  rw [show (fun u => (quantileSpeed S u)⁻¹ * ‖quantileTransform S (fun x => f x) u‖ ^ 2)
      = fun u => (S.k (S.quantileFun u) / S.mass) *
          ‖(Real.sqrt S.mass : ℂ) * f (S.quantileFun u) / (S.k (S.quantileFun u) : ℂ)‖ ^ 2 from
    funext fun u => by rw [inv_quantileSpeed S u]; rfl]
  rw [hmain, integral_congr_ae (Filter.Eventually.of_forall
    (fun x => normalized_smul_metricIntegrand S (fun x => f x) x))]
  exact MeasureTheory.integral_div _ _

end HedenmalmQuantile

end

end RHTower
