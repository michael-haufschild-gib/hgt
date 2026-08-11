import GaloisForLFunctions.RHTower.HedenmalmShiftedCokernel

/-!
# Exact two-ended solution of the shifted Hedenmalm source equation

This module identifies the unique closed-operator solution furnished by the exact shifted
Fredholm alternative with Hedenmalm's literal two-ended primitive.  No strip hypothesis remains:
all exponential moments of the theta source supply every complex tilt.
-/

open Complex Function MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmPrimeTranslation
  HedenmalmFredholmRange

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev HS := SourceSpace thetaSource

local instance factTwoNeTopShiftedSourceEquation : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-! ### Source-coordinate representative of the compact inverse -/

/-- Pulling both input and output of the compact quantile inverse back to source coordinates
identifies its output almost everywhere with the literal centered source primitive. -/
theorem sourceInverse_ae_eq_quantileSymm_thetaCompactSourceInverse (f : H) :
    let v : HS := (quantileUnitary thetaSource).symm f
    let w : HS := (quantileUnitary thetaSource).symm (thetaCompactSourceInverse f)
    sourceInverse thetaSource (fun x => v x) =ᵐ[(volume : Measure ℝ)]
      fun x => w x := by
  let v : HS := (quantileUnitary thetaSource).symm f
  let w : HS := (quantileUnitary thetaSource).symm (thetaCompactSourceInverse f)
  have hvf : quantileUnitary thetaSource v = f := by simp [v]
  have hwf : quantileUnitary thetaSource w = thetaCompactSourceInverse f := by simp [w]
  have hquantileV := quantileUnitary_ae thetaSource v
  rw [hvf] at hquantileV
  change (f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
    fun t => quantileTransform thetaSource (fun x => v x) t at hquantileV
  have hquantileW := quantileUnitary_ae thetaSource w
  rw [hwf] at hquantileW
  change ((thetaCompactSourceInverse f : H) : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
    fun t => quantileTransform thetaSource (fun x => w x) t at hquantileW
  have hsourceQuantile :
      (fun t => sourceInverse thetaSource (fun x => v x)
        (thetaSource.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => w (thetaSource.quantileFun t) := by
    filter_upwards
      [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f,
        hquantileV, hquantileW, ae_unitIntervalMeasure_mem_Ioo]
      with t hoperator hquantileV_t hquantileW_t ht
    have htransform :
        quantileTransform thetaSource
            (sourceInverse thetaSource (fun x => v x)) t =
          quantileTransform thetaSource (fun x => w x) t := by
      calc
        quantileTransform thetaSource
            (sourceInverse thetaSource (fun x => v x)) t =
            Complex.I * (quantileSpeed thetaSource t : ℂ) *
              pinnedVolterraFun (quantileUnitary thetaSource v) t :=
          quantileTransform_sourceInverse_eq_pinned thetaSource v ht
        _ = pinnedKernelField thetaSource t f := by
          rw [hvf]
          exact (pinnedKernelField_apply_eq_pinnedVolterraFun thetaSource t f).symm
        _ = (thetaCompactSourceInverse f : ℝ → ℂ) t := hoperator.symm
        _ = quantileTransform thetaSource (fun x => w x) t := hquantileW_t
    have hk : ((thetaSource.k (thetaSource.quantileFun t) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (thetaSource.pos_k _).ne'
    have hM : ((Real.sqrt thetaSource.mass : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
    unfold quantileTransform at htransform
    field_simp [hk, hM] at htransform
    exact htransform
  have hlaw := hsourceQuantile.comp_tendsto
    (measurePreserving_cdf_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  have hlaw' :
      sourceInverse thetaSource (fun x => v x) =ᵐ[thetaSource.law]
        fun x => w x := by
    filter_upwards [hlaw] with x hx
    change sourceInverse thetaSource (fun y => v y)
      (thetaSource.quantileFun (thetaSource.cdfFun x)) =
        w (thetaSource.quantileFun (thetaSource.cdfFun x)) at hx
    rw [thetaSource.quantile_cdfFun] at hx
    exact hx
  exact (thetaSource.law_ae_eq).mp hlaw'

end HedenmalmThetaSource

end

end RHTower
