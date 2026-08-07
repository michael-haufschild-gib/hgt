import GaloisForLFunctions.HTGeometry.PositiveDensityQuantile
import GaloisForLFunctions.RHTower.HedenmalmPinnedVolterraBoundaryDefect

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

end HedenmalmQuantile

end

end RHTower
