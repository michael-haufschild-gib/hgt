import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDeterminantMultiplicity

/-!
# Exact point spectrum of the fixed Hedenmalm theta source inverse

This module proves the missing converse to the explicit divisor-mode construction.  An arbitrary
eigenvector of the fixed compact quantile operator is pulled back through the quantile unitary.
The kernel representative and the quantile normal form then show that its source representative
satisfies the source-inverse eigen-equation almost everywhere.  Subsequent regularity and endpoint
arguments identify the spectral parameter with a zero of the completed theta transform.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Every weighted source-space vector remains Lebesgue integrable after multiplication by any
complex source character.  The two `L²` factors are `v / √k` and `√k · exp(izx)`; the
all-shift theorem supplies the second factor for arbitrary `z`. -/
theorem integrable_sourceSpace_mul_sourceChar
    (v : SourceSpace thetaSource) (z : ℂ) :
    Integrable (fun x : ℝ => v x * sourceChar z x) (volume : Measure ℝ) := by
  have hv : MemLp
      (fun x => sqrtWeight (sourceWeight thetaSource) x * v x)
      2 (volume : Measure ℝ) :=
    (memLp_two_withDensity_iff (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (Lp.memLp v)
  have hchar : MemLp
      (fun x : ℝ => ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x)
      2 (volume : Measure ℝ) := by
    have hcont : Continuous
        (fun x : ℝ => ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x) :=
      (Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp thetaSource.continuous_k)).mul
          (continuous_sourceChar z)
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
    refine (integrable_exp_mul_thetaCuspFullSource (-2 * z.im)).congr ?_
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_sourceChar, mul_pow,
      Real.sq_sqrt (thetaSource.pos_k x).le, thetaSource_k]
    have hexp : Real.exp (-z.im * x) ^ 2 =
        Real.exp ((-2 * z.im) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    ring
  have hprod := MemLp.integrable_mul hv hchar
  refine hprod.congr ?_
  filter_upwards with x
  have hk : (0 : ℝ) < thetaSource.k x := thetaSource.pos_k x
  have hkne : Real.sqrt (thetaSource.k x) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  have hkc : ((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hkne
  have hsw : sqrtWeight (sourceWeight thetaSource) x =
      (((Real.sqrt (thetaSource.k x))⁻¹ : ℝ) : ℂ) := by
    rw [sqrtWeight]
    norm_cast
    rw [show sourceWeight thetaSource x = (thetaSource.k x)⁻¹ from rfl,
      Real.sqrt_inv]
  show sqrtWeight (sourceWeight thetaSource) x * v x *
      (((Real.sqrt (thetaSource.k x) : ℝ) : ℂ) * sourceChar z x) =
    v x * sourceChar z x
  rw [hsw]
  push_cast
  field_simp [hkc]

/-- Pulling an operator eigenvector back through the quantile unitary gives the literal
source-inverse eigen-equation almost everywhere on the source line. -/
theorem sourceInverse_ae_eq_smul_of_thetaCompactSourceInverse_eigen
    {c : ℂ} {f : Lp ℂ 2 unitIntervalMeasure}
    (hf : thetaCompactSourceInverse f = c • f) :
    let v : SourceSpace thetaSource := (quantileUnitary thetaSource).symm f
    sourceInverse thetaSource (fun x => v x) =ᵐ[(volume : Measure ℝ)]
      fun x => c * v x := by
  let v : SourceSpace thetaSource := (quantileUnitary thetaSource).symm f
  have hvf : quantileUnitary thetaSource v = f := by
    simp [v]
  have heigen :
      (thetaCompactSourceInverse f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
        fun t => c * f t := by
    filter_upwards [Lp.coeFn_smul c f] with t ht
    rw [hf]
    simpa [smul_eq_mul] using ht
  have hquantile := quantileUnitary_ae thetaSource v
  rw [hvf] at hquantile
  change (f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
    fun t => quantileTransform thetaSource (fun x => v x) t at hquantile
  have hsourceQuantile :
      (fun t => sourceInverse thetaSource (fun x => v x)
        (thetaSource.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => c * v (thetaSource.quantileFun t) := by
    filter_upwards
      [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f,
        heigen, hquantile, ae_unitIntervalMeasure_mem_Ioo]
      with t hoperator heigen_t hquantile_t ht
    have htransform :
        quantileTransform thetaSource
            (sourceInverse thetaSource (fun x => v x)) t =
          c * quantileTransform thetaSource (fun x => v x) t := by
      calc
        quantileTransform thetaSource
            (sourceInverse thetaSource (fun x => v x)) t =
            Complex.I * (quantileSpeed thetaSource t : ℂ) *
              pinnedVolterraFun (quantileUnitary thetaSource v) t :=
          quantileTransform_sourceInverse_eq_pinned thetaSource v ht
        _ = pinnedKernelField thetaSource t f := by
          rw [hvf]
          exact (pinnedKernelField_apply_eq_pinnedVolterraFun thetaSource t f).symm
        _ = (thetaCompactSourceInverse f : ℝ → ℂ) t := by
          exact hoperator.symm
        _ = c * f t := heigen_t
        _ = c * quantileTransform thetaSource (fun x => v x) t := by
          rw [hquantile_t]
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
        fun x => c * v x := by
    filter_upwards [hlaw] with x hx
    change sourceInverse thetaSource (fun y => v y)
      (thetaSource.quantileFun (thetaSource.cdfFun x)) =
        c * v (thetaSource.quantileFun (thetaSource.cdfFun x)) at hx
    rw [thetaSource.quantile_cdfFun] at hx
    exact hx
  exact (thetaSource.law_ae_eq).mp hlaw'

end HedenmalmThetaSource

end

end RHTower
