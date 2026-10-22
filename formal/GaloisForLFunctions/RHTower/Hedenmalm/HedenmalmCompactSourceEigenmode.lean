import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactDivisorEigenmode
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileMetric

/-!
# The compact source inverse of a positive density

For a continuous, positive, integrable density `k` with finite reciprocal-tail energy
`∫ p(1-p)/k < ∞`, the source inverse in the quantile coordinate,

`(B f)(t) = i q(t) (∫₀ᵗ f - t ∫₀¹ f)`,  `q(t) = M / k(Q t)`,

is a Hilbert--Schmidt operator on `L²(0,1)`.  For a bounded density the canonical metric
`D = M_{1/q}` is bounded, and

`D B - B† D = i P`

where `P` is the universal rank-two pinned boundary operator of kernel `1 - t - u`.

At a point `z ≠ 0` where the source mode `f_z = -z u_z` lies in `L²(ℝ, k⁻¹ dx)`, is integrable,
vanishes at `-∞` and carries the full mass, its quantile image is a nonzero eigenvector of `B`
with eigenvalue `-z⁻¹`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmCompactSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmHilbertSchmidt HedenmalmThetaSource

variable (S : PositiveDensitySource)

local instance factTwoNeTopCompactSourceEigenmode : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Integrable reciprocal-tail energy is the Hilbert--Schmidt kernel energy. -/
theorem hasFiniteKernelEnergy_of_integrable (h : Integrable (tailEnergyDensity S)) :
    HasFiniteKernelEnergy S := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (S.mass / S.k x) ^ (2 : ℕ) * (S.cdfFun x * (1 - S.cdfFun x)))
      (volume : Measure ℝ) := by
    refine (((continuous_const.div S.continuous_k fun x => (S.pos_k x).ne').pow 2).mul ?_
      ).aestronglyMeasurable
    exact S.continuous_cdfFun.mul (continuous_const.sub S.continuous_cdfFun)
  have hiff := S.integrableOn_comp_quantileFun_iff (g := fun x : ℝ =>
      (S.mass / S.k x) ^ (2 : ℕ) * (S.cdfFun x * (1 - S.cdfFun x))) hmeas
  have hright : Integrable (fun x : ℝ => S.normalized x •
      ((S.mass / S.k x) ^ (2 : ℕ) * (S.cdfFun x * (1 - S.cdfFun x)))) (volume : Measure ℝ) := by
    refine (h.const_mul S.mass).congr ?_
    filter_upwards with x
    have hk : S.k x ≠ 0 := (S.pos_k x).ne'
    have hM : S.mass ≠ 0 := S.mass_ne_zero
    show S.mass * (S.cdfFun x * (1 - S.cdfFun x) / S.k x)
      = (S.k x / S.mass) * ((S.mass / S.k x) ^ (2 : ℕ) * (S.cdfFun x * (1 - S.cdfFun x)))
    field_simp
  have hcongr : IntegrableOn
      (fun t : ℝ => quantileSpeed S t ^ (2 : ℕ) * (t * (1 - t))) (Ioo (0 : ℝ) 1) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun (hiff.mpr hright) (fun t ht => ?_)
      measurableSet_Ioo
    show (S.mass / S.k (S.quantileFun t)) ^ (2 : ℕ)
        * (S.cdfFun (S.quantileFun t) * (1 - S.cdfFun (S.quantileFun t)))
      = quantileSpeed S t ^ (2 : ℕ) * (t * (1 - t))
    rw [S.cdfFun_quantile ht, quantileSpeed]
  have hres : unitIntervalMeasure = (volume : Measure ℝ).restrict (Ioo 0 1) := by
    rw [unitIntervalMeasure, restrict_Ioo_eq_restrict_Icc]
  show Integrable _ unitIntervalMeasure
  rw [hres]
  exact hcongr

/-- The compact source inverse `B = i M_q C` on `L²(0,1)`. -/
def compactSourceInverse (hfin : HasFiniteKernelEnergy S) :
    Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure (pinnedKernelL2 S hfin)

theorem isHilbertSchmidt_compactSourceInverse (hfin : HasFiniteKernelEnergy S) :
    ContinuousLinearMap.IsHilbertSchmidt (compactSourceInverse S hfin) :=
  isHilbertSchmidt_pinnedKernelOperator S hfin

theorem isCompactOperator_compactSourceInverse (hfin : HasFiniteKernelEnergy S) :
    IsCompactOperator (compactSourceInverse S hfin) :=
  isCompactOperator_pinnedKernelOperator S hfin

/-! ### The singular metric commutator -/

/-- The metric cancels the quantile speed: `D B = i C`. -/
theorem metricOperator_mul_compactSourceInverse (hfin : HasFiniteKernelEnergy S) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    metricOperator S hC0 hC * compactSourceInverse S hfin = Complex.I • pinnedVolterraCLM := by
  apply ContinuousLinearMap.ext
  intro f
  change metricOperator S hC0 hC (compactSourceInverse S hfin f) =
    Complex.I • pinnedVolterraCLM f
  apply Lp.ext
  have hV := pinnedVolterra_coeFn f
  change (fun t => (pinnedVolterraCLM f) t) =ᵐ[unitIntervalMeasure]
    pinnedVolterraFun f at hV
  have hB : (fun t => (compactSourceInverse S hfin f) t) =ᵐ[unitIntervalMeasure]
      fun t => pinnedKernelField S t f := pinnedKernelOperator_ae S hfin f
  filter_upwards [metricOperator_coeFn S hC0 hC (compactSourceInverse S hfin f), hB, hV,
    Lp.coeFn_smul Complex.I (pinnedVolterraCLM f)] with t hG hBt hVt hsmul
  rw [hG, hBt, hsmul]
  change metricSymbol S t * pinnedKernelField S t f = Complex.I * (pinnedVolterraCLM f) t
  rw [hVt, pinnedKernelField_apply_eq_pinnedVolterraFun, metricSymbol_eq_inv_quantileSpeed]
  have hq : ((quantileSpeed S t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (quantileSpeed_pos S t).ne'
  push_cast
  field_simp

theorem adjoint_metricOperator {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    (metricOperator S hC0 hC).adjoint = metricOperator S hC0 hC := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact metricOperator_inner S hC0 hC

/-- The metric is a positive operator. -/
theorem re_inner_metricOperator_nonneg {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C)
    (f : Lp ℂ 2 unitIntervalMeasure) : 0 ≤ (inner ℂ (metricOperator S hC0 hC f) f : ℂ).re := by
  rw [L2.inner_def, ← RCLike.re_to_complex, ← integral_re]
  · refine integral_nonneg_of_ae ?_
    filter_upwards [metricOperator_coeFn S hC0 hC f] with t ht
    simp only [Pi.zero_apply]
    have hm : (starRingEnd ℂ) (metricSymbol S t) = metricSymbol S t := starRingEnd_metricSymbol S t
    rw [ht, RCLike.inner_apply, (starRingEnd ℂ).map_mul, hm, mul_left_comm, Complex.mul_conj',
      metricSymbol, ← Complex.ofReal_pow, ← Complex.ofReal_mul, RCLike.re_to_complex,
      Complex.ofReal_re]
    exact mul_nonneg (metricSymbol_pos S t).le (sq_nonneg _)
  · exact (L2.integrable_inner (metricOperator S hC0 hC f) f)

/-- The adjoint half: `B† D = -i C†`. -/
theorem compactSourceInverse_adjoint_mul_metricOperator (hfin : HasFiniteKernelEnergy S) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    ContinuousLinearMap.adjoint (compactSourceInverse S hfin) * metricOperator S hC0 hC =
      (-Complex.I) • ContinuousLinearMap.adjoint pinnedVolterraCLM := by
  have h := congrArg ContinuousLinearMap.adjoint
    (metricOperator_mul_compactSourceInverse S hfin hC0 hC)
  rw [ContinuousLinearMap.mul_def] at h
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint.map_smulₛₗ] at h
  rw [adjoint_metricOperator] at h
  change ContinuousLinearMap.adjoint (compactSourceInverse S hfin) ∘L metricOperator S hC0 hC =
    (starRingEnd ℂ) Complex.I • ContinuousLinearMap.adjoint pinnedVolterraCLM at h
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  rw [hI] at h
  simpa only [ContinuousLinearMap.mul_def] using h

/-- **Rank-two metric defect.** `D B - B† D = i P` with `P` the pinned boundary operator of kernel
`1 - t - u`. -/
theorem metricOperator_commutator_compactSourceInverse (hfin : HasFiniteKernelEnergy S) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    metricOperator S hC0 hC * compactSourceInverse S hfin -
        ContinuousLinearMap.adjoint (compactSourceInverse S hfin) * metricOperator S hC0 hC =
      Complex.I • pinnedBoundaryCLM := by
  rw [metricOperator_mul_compactSourceInverse, compactSourceInverse_adjoint_mul_metricOperator,
    ← adjoint_add_pinnedVolterraCLM_eq_pinnedBoundaryCLM]
  module

/-! ### Divisor eigenvectors -/

/-- The weighted source vector of a mode in `L²(ℝ, k⁻¹ dx)`. -/
def divisorSourceVector {z : ℂ}
    (hmem : MemLp (sourceModeF S z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight S)))) : SourceSpace S :=
  hmem.toLp _

theorem divisorSourceVector_ae {z : ℂ}
    (hmem : MemLp (sourceModeF S z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight S)))) :
    (divisorSourceVector S hmem : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] sourceModeF S z :=
  (withDensity_realDensity_ae_eq (measurable_sourceWeight S) (sourceWeight_pos S)).mp
    (MemLp.coeFn_toLp hmem)

/-- A mode carrying the full source mass is a nonzero vector. -/
theorem divisorSourceVector_ne_zero {z : ℂ}
    (hmem : MemLp (sourceModeF S z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight S))))
    (hmass : (∫ x, sourceModeF S z x) = (S.mass : ℂ)) :
    divisorSourceVector S hmem ≠ 0 := by
  intro hv
  have hae := divisorSourceVector_ae S hmem
  rw [hv] at hae
  have hzeroWeighted : ((0 : SourceSpace S) : ℝ → ℂ) =ᵐ[
      (volume : Measure ℝ).withDensity (realDensity (sourceWeight S))] fun _ => 0 :=
    Lp.coeFn_zero ℂ 2 _
  have hzeroLeb : ((0 : SourceSpace S) : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] fun _ => 0 :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight S) (sourceWeight_pos S)).mp
      hzeroWeighted
  have hfzero : sourceModeF S z =ᵐ[(volume : Measure ℝ)] fun _ => 0 := hae.symm.trans hzeroLeb
  have hmassZero : (S.mass : ℂ) = 0 := by rw [← hmass, integral_congr_ae hfzero, integral_zero]
  exact (by exact_mod_cast S.mass_ne_zero : (S.mass : ℂ) ≠ 0) hmassZero

/-- The quantile image of the mode. -/
def divisorEigenvector {z : ℂ}
    (hmem : MemLp (sourceModeF S z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight S)))) :
    Lp ℂ 2 unitIntervalMeasure :=
  quantileUnitary S (divisorSourceVector S hmem)

theorem divisorEigenvector_ne_zero {z : ℂ}
    (hmem : MemLp (sourceModeF S z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight S))))
    (hmass : (∫ x, sourceModeF S z x) = (S.mass : ℂ)) :
    divisorEigenvector S hmem ≠ 0 := by
  intro h
  apply divisorSourceVector_ne_zero S hmem hmass
  apply (quantileUnitary S).injective
  simpa only [divisorEigenvector, map_zero] using h

/-- **Divisor eigenvector.** Under the endpoint data of the mode, `B g_z = -z⁻¹ g_z`. -/
theorem compactSourceInverse_divisorEigenvector (hfin : HasFiniteKernelEnergy S) {z : ℂ}
    (hz0 : z ≠ 0) (hst : HasShiftedTail S z)
    (hmem : MemLp (sourceModeF S z) 2
      ((volume : Measure ℝ).withDensity (realDensity (sourceWeight S))))
    (hint : Integrable (sourceModeF S z) (volume : Measure ℝ))
    (hbot : Tendsto (sourceModeU S z) atBot (𝓝 0))
    (hmass : (∫ x, sourceModeF S z x) = (S.mass : ℂ)) :
    compactSourceInverse S hfin (divisorEigenvector S hmem) =
      (-z⁻¹) • divisorEigenvector S hmem := by
  set g : Lp ℂ 2 unitIntervalMeasure := divisorEigenvector S hmem
  apply Lp.ext
  set v : SourceSpace S := divisorSourceVector S hmem
  have hgv : g = quantileUnitary S v := rfl
  have hv : (v : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] sourceModeF S z := divisorSourceVector_ae S hmem
  have hvq : (fun t => v (S.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => sourceModeF S z (S.quantileFun t) :=
    ((S.law_ae_eq).mpr hv).comp_tendsto
      (measurePreserving_quantile_unitInterval S).quasiMeasurePreserving.tendsto_ae
  filter_upwards [pinnedKernelOperator_ae S hfin g, ae_unitIntervalMeasure_mem_Ioo,
    quantileUnitary_ae S v, hvq, Lp.coeFn_smul (-z⁻¹) g] with t hoperator ht hg hvqt hsmul
  rw [hsmul]
  change (compactSourceInverse S hfin g : ℝ → ℂ) t = (-z⁻¹) * g t
  rw [compactSourceInverse, hoperator, pinnedKernelField_apply_eq_pinnedVolterraFun, hgv,
    ← quantileTransform_sourceInverse_eq_pinned S v ht]
  unfold quantileTransform
  rw [sourceInverse_congr_ae S hv (S.quantileFun t),
    sourceInverse_sourceModeF_eq_smul S hz0 hst hint hbot hmass]
  rw [hg, hvqt]
  ring

end HedenmalmCompactSource

end

end RHTower
