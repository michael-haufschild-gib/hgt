import GaloisForLFunctions.RHTower.HedenmalmThetaRootModeDecay

/-!
# The endpoint hypotheses of the quantile flux identity are theorems

The quantile root mode is the source mode read in the quantile coordinate,

`h(t) = -(1/M) i u_z(Q t)`,

so the exponential decay of `u_z` at a zero of the completed transform gives all four endpoint
conditions of the flux identity: the two boundary limits, boundedness (hence integrability of the
value), and integrability of the energy after the quantile change of variables.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation

variable (S : PositiveDensitySource)

/-! ### The root primitive is the source primitive in quantile coordinates -/

theorem rootA_eq_sourceModeI (z : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    rootA S z t = sourceModeI S z (S.quantileFun t) / (S.mass : ℂ) := by
  have hmeas : AEStronglyMeasurable (sourceChar z) (volume : Measure ℝ) :=
    (continuous_sourceChar z).aestronglyMeasurable
  have h := setIntegral_comp_quantile S (sourceChar z) hmeas ht
  have hpt : ∀ x : ℝ, S.normalized x • sourceChar z x
      = (S.k x : ℂ) * sourceChar z x / (S.mass : ℂ) := by
    intro x
    rw [Complex.real_smul, show S.normalized x = S.k x / S.mass from rfl]
    push_cast
    ring
  rw [rootA, intervalIntegral.integral_of_le ht.1.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, h,
    setIntegral_congr_fun measurableSet_Iic (fun x _ => hpt x),
    MeasureTheory.integral_div, sourceModeI]

theorem norm_rootH_eq (z : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖rootH S z t‖ = ‖sourceModeU S z (S.quantileFun t)‖ / S.mass := by
  have hM : (0 : ℝ) < S.mass := S.mass_pos
  rw [rootH, norm_neg, norm_mul, rootA_eq_sourceModeI S z ht, sourceModeU, norm_mul, norm_mul,
    norm_neg, Complex.norm_I, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hM, rootFactor]
  ring

/-! ### The two boundary limits of the quantile coordinate -/

theorem tendsto_quantileFun_nhdsGT_zero : Tendsto S.quantileFun (𝓝[>] (0 : ℝ)) atBot := by
  refine tendsto_atBot.mpr fun M => ?_
  have hc : S.cdfFun M ∈ Ioo (0 : ℝ) 1 := S.cdfFun_mem_Ioo M
  have hmem : Ioo (0 : ℝ) (S.cdfFun M) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hc.1⟩
  filter_upwards [hmem] with t ht
  have htmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 hc.2⟩
  have hlt := S.strictMonoOn_quantileFun htmem hc ht.2
  rw [S.quantile_cdfFun] at hlt
  exact hlt.le

theorem tendsto_quantileFun_nhdsLT_one : Tendsto S.quantileFun (𝓝[<] (1 : ℝ)) atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  have hc : S.cdfFun M ∈ Ioo (0 : ℝ) 1 := S.cdfFun_mem_Ioo M
  have hmem : Ioo (S.cdfFun M) (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsWithin_Iio ⟨hc.2, le_rfl⟩
  filter_upwards [hmem] with t ht
  have htmem : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hc.1 ht.1, ht.2⟩
  have hlt := S.strictMonoOn_quantileFun hc htmem ht.1
  rw [S.quantile_cdfFun] at hlt
  exact hlt.le

end HedenmalmThetaSource

end

end RHTower
