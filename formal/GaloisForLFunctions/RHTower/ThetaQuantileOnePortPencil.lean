import GaloisForLFunctions.RHTower.ThetaQuantileFourierQuotient
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPinnedBoundaryTwoPort

/-!
# The exact one-port pencil of the theta quotient

On the mean-zero space `H₀` put `T = P M_h P` (`h = 1/q` the theta quantile metric),
`A = i P V P` (`V` the pinned primitive), `b = P h` and `β(f) = ∫₀¹ Bf`.  Because `h q = 1`,
`M_h B = i V`; splitting `B f = PBf + β(f)·1` gives the exact pencil

`T D = A − b β`  on `H₀`,

with `T` positive and injective on `H₀` and `A` self-adjoint (`V + V*` has rank two and vanishes
on `H₀ × H₀`).  Consequently an eigenvector of `D` in the neutral-port subspace `ker β` has a real
eigenvalue.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The constant mode -/

theorem constMode_eq_pinnedOne : constMode = pinnedOne := by
  apply Lp.ext
  filter_upwards [coeFn_unitFourierBasis 0, pinnedOne_coeFn] with t h1 h2
  rw [h1, h2, fourierMode_zero]

theorem inner_constMode_eq_pinnedMean (f : ThetaL2) : ⟪constMode, f⟫_ℂ = pinnedMean f := by
  rw [constMode_eq_pinnedOne, inner_lp_eq, pinnedMean]
  apply integral_congr_ae
  filter_upwards [pinnedOne_coeFn] with t ht
  rw [ht]
  simp

theorem mem_meanZeroSpace_iff (f : ThetaL2) : f ∈ meanZeroSpace ↔ ⟪constMode, f⟫_ℂ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

theorem meanZeroProj_eq_self {f : ThetaL2} (hf : f ∈ meanZeroSpace) : meanZeroProj f = f := by
  rw [meanZeroProj_apply, (mem_meanZeroSpace_iff f).1 hf, zero_smul, sub_zero]

theorem meanZeroProj_mem (f : ThetaL2) : meanZeroProj f ∈ meanZeroSpace := by
  rw [meanZeroProj]
  exact Submodule.starProjection_apply_mem _ f

theorem inner_constMode_self : ⟪constMode, constMode⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, unitFourierBasis.orthonormal.1 0]; simp

theorem meanZeroProj_constMode : meanZeroProj constMode = 0 := by
  rw [meanZeroProj_apply, inner_constMode_self, one_smul, sub_self]

theorem inner_meanZeroProj_left (f g : ThetaL2) : ⟪meanZeroProj f, g⟫_ℂ = ⟪f, meanZeroProj g⟫_ℂ := by
  rw [meanZeroProj]
  exact Submodule.inner_starProjection_left_eq_right _ f g

/-! ## The operators of the pencil -/

/-- The metric compression `T = P M_h P`. -/
def onePortMetric : ThetaL2 →L[ℂ] ThetaL2 := meanZeroProj ∘L thetaMetricOperator ∘L meanZeroProj

/-- The compressed primitive `A = i P V P`. -/
def onePortPrimitive : ThetaL2 →L[ℂ] ThetaL2 :=
  Complex.I • (meanZeroProj ∘L pinnedVolterraCLM ∘L meanZeroProj)

/-- The input port `β(f) = ∫₀¹ Bf = ⟨1, Bf⟩`. -/
def onePortInput : ThetaL2 →L[ℂ] ℂ := innerSL ℂ constMode ∘L thetaKernelOperator

/-- The output vector `b = P h`. -/
def onePortOutputVector : ThetaL2 := meanZeroProj (thetaMetricOperator constMode)

theorem onePortInput_apply (f : ThetaL2) : onePortInput f = ⟪constMode, thetaKernelOperator f⟫_ℂ := rfl

/-- `h q = 1`: the metric undoes the quantile speed of the source inverse, `M_h B = i V`. -/
theorem thetaMetricOperator_thetaKernelOperator (f : ThetaL2) :
    thetaMetricOperator (thetaKernelOperator f) = Complex.I • pinnedVolterraCLM f := by
  apply Lp.ext
  filter_upwards [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le (thetaKernelOperator f),
    thetaKernelOperator_ae f, Lp.coeFn_smul Complex.I (pinnedVolterraCLM f),
    pinnedVolterra_coeFn f] with t h1 h2 h3 h4
  rw [show thetaMetricOperator = metricOperator thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le from rfl, h1, h2, h3, Pi.smul_apply, smul_eq_mul]
  change _ = Complex.I * (pinnedVolterra f) t
  rw [h4, metricSymbol_eq_inv_quantileSpeed]
  have hq := thetaQuantileSpeed_pos t
  have hq' : ((thetaQuantileSpeed t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [thetaQuantileSpeed] at hq' ⊢
  push_cast
  field_simp

/-- `PB f = Bf − β(f)·1`. -/
theorem meanZeroProj_thetaKernelOperator (f : ThetaL2) :
    meanZeroProj (thetaKernelOperator f) = thetaKernelOperator f - onePortInput f • constMode := by
  rw [meanZeroProj_apply, onePortInput_apply]

/-- **The exact one-port pencil** `T D = A − b β` on `H₀`. -/
theorem onePortMetric_thetaQuotientOperator {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    onePortMetric (thetaQuotientOperator f) =
      onePortPrimitive f - onePortInput f • onePortOutputVector := by
  have hPf := meanZeroProj_eq_self hf
  have hPP : meanZeroProj (meanZeroProj (thetaKernelOperator f)) =
      meanZeroProj (thetaKernelOperator f) :=
    meanZeroProj_eq_self (meanZeroProj_mem _)
  rw [onePortMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    thetaQuotientOperator_apply, hPP, meanZeroProj_thetaKernelOperator, map_sub, map_smul,
    thetaMetricOperator_thetaKernelOperator, map_sub, map_smul, map_smul, onePortPrimitive,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPf,
    onePortOutputVector]

/-! ## Symmetry and positivity -/

/-- `V + V*` vanishes on `H₀ × H₀`: the compressed primitive is skew. -/
theorem inner_pinnedVolterra_add_adjoint {f g : ThetaL2} (hf : f ∈ meanZeroSpace) (hg : g ∈ meanZeroSpace) :
    ⟪g, pinnedVolterraCLM f⟫_ℂ = -⟪pinnedVolterraCLM g, f⟫_ℂ := by
  have h1 : ⟪g, pinnedBoundaryCLM f⟫_ℂ = 0 := by
    rw [pinnedBoundaryCLM_eq_rankOne]
    simp only [sub_apply, InnerProductSpace.rankOne_apply, inner_sub_right, inner_smul_right]
    have hf0 : ⟪pinnedOne, f⟫_ℂ = 0 := by rw [← constMode_eq_pinnedOne]; exact (mem_meanZeroSpace_iff f).1 hf
    have hg0 : ⟪g, pinnedOne⟫_ℂ = 0 := by
      rw [← constMode_eq_pinnedOne, ← inner_conj_symm, (mem_meanZeroSpace_iff g).1 hg, map_zero]
    rw [hf0, hg0]; ring
  rw [← adjoint_add_pinnedVolterraCLM_eq_pinnedBoundaryCLM, add_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right] at h1
  linear_combination h1

theorem isSelfAdjoint_onePortPrimitive : IsSelfAdjoint onePortPrimitive := by
  refine ContinuousLinearMap.isSelfAdjoint_iff'.2 ?_
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  rw [onePortPrimitive, smul_apply, smul_apply, inner_smul_left, inner_smul_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_meanZeroProj_left, ← inner_meanZeroProj_left x]
  rw [inner_pinnedVolterra_add_adjoint (meanZeroProj_mem y) (meanZeroProj_mem x)]
  simp only [Complex.conj_I]
  ring

theorem inner_thetaMetricOperator (f : ThetaL2) :
    ⟪f, thetaMetricOperator f⟫_ℂ = ((∫ t, ‖metricSymbol thetaSource t‖ * ‖f t‖ ^ 2 ∂unitIntervalMeasure : ℝ) : ℂ) := by
  rw [inner_lp_eq, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le f] with t ht
  rw [show thetaMetricOperator = metricOperator thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le from rfl, ht, norm_metricSymbol, metricSymbol]
  rw [mul_left_comm, Complex.conj_mul']
  push_cast
  ring

theorem integrable_metric_mul_norm_sq (f : ThetaL2) :
    Integrable (fun t => ‖metricSymbol thetaSource t‖ * ‖f t‖ ^ 2) unitIntervalMeasure := by
  have hf2 : Integrable (fun t => ‖f t‖ ^ 2) unitIntervalMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  refine (hf2.const_mul (thetaBound / thetaSource.mass)).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact ((measurable_metricSymbol thetaSource).norm.aestronglyMeasurable).mul hf2.1
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (norm_metricSymbol_thetaSource_le t) (by positivity)

/-- `⟨f, Tf⟩ = ∫ h |Pf|²`. -/
theorem inner_onePortMetric (f : ThetaL2) :
    ⟪f, onePortMetric f⟫_ℂ = ⟪meanZeroProj f, thetaMetricOperator (meanZeroProj f)⟫_ℂ := by
  rw [onePortMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← inner_meanZeroProj_left]

theorem isPositive_onePortMetric : onePortMetric.IsPositive := by
  have hsa : IsSelfAdjoint onePortMetric := by
    refine ContinuousLinearMap.isSelfAdjoint_iff'.2 ?_
    symm
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
    rw [onePortMetric, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_meanZeroProj_left,
      show thetaMetricOperator = metricOperator thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le from rfl, metricOperator_inner, ← inner_meanZeroProj_left]
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨hsa.isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re,
    inner_onePortMetric, inner_thetaMetricOperator, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun t => by positivity

/-- The metric energy `∫ h |f|²` of a mean-zero vector. -/
def metricEnergy (f : ThetaL2) : ℝ := ∫ t, ‖metricSymbol thetaSource t‖ * ‖f t‖ ^ 2 ∂unitIntervalMeasure

theorem inner_onePortMetric_of_mem {f : ThetaL2} (hf : f ∈ meanZeroSpace) :
    ⟪f, onePortMetric f⟫_ℂ = (metricEnergy f : ℂ) := by
  rw [inner_onePortMetric, meanZeroProj_eq_self hf, inner_thetaMetricOperator, metricEnergy]

theorem metricEnergy_nonneg (f : ThetaL2) : 0 ≤ metricEnergy f :=
  integral_nonneg fun t => by positivity

theorem eq_zero_of_metricEnergy_eq_zero {f : ThetaL2} (h : metricEnergy f = 0) : f = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => by positivity)
    (integrable_metric_mul_norm_sq f)).1 h
  apply Lp.eq_zero_iff_ae_eq_zero.2
  filter_upwards [hae] with t ht
  have hpos : 0 < ‖metricSymbol thetaSource t‖ := norm_pos_iff.2 (metricSymbol_ne_zero thetaSource t)
  simp only [Pi.zero_apply] at ht ⊢
  have : ‖f t‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 ht with h | h
    · exact absurd h hpos.ne'
    · exact h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

theorem metricEnergy_pos {f : ThetaL2} (hne : f ≠ 0) : 0 < metricEnergy f :=
  (metricEnergy_nonneg f).lt_of_ne fun h => hne (eq_zero_of_metricEnergy_eq_zero h.symm)

/-- **`T` is injective on `H₀`.** -/
theorem onePortMetric_injOn {f : ThetaL2} (hf : f ∈ meanZeroSpace) (h0 : onePortMetric f = 0) : f = 0 := by
  have hin : ⟪f, onePortMetric f⟫_ℂ = 0 := by rw [h0, inner_zero_right]
  rw [inner_onePortMetric_of_mem hf, Complex.ofReal_eq_zero] at hin
  exact eq_zero_of_metricEnergy_eq_zero hin

/-- **Neutral-port eigenvalues are real**: an eigenvector of `D` in `H₀ ∩ ker β` has a real
eigenvalue. -/
theorem im_eq_zero_of_onePortInput_eq_zero {f : ThetaL2} {μ : ℂ} (hf : f ∈ meanZeroSpace) (hne : f ≠ 0)
    (heig : thetaQuotientOperator f = μ • f) (hβ : onePortInput f = 0) : μ.im = 0 := by
  have hpencil := onePortMetric_thetaQuotientOperator hf
  rw [heig, hβ, zero_smul, sub_zero, map_smul] at hpencil
  have h1 : μ * (metricEnergy f : ℂ) = ⟪f, onePortPrimitive f⟫_ℂ := by
    rw [← inner_onePortMetric_of_mem hf, ← inner_smul_right, hpencil]
  have hA : (⟪f, onePortPrimitive f⟫_ℂ).im = 0 := by
    have hsym : ⟪onePortPrimitive f, f⟫_ℂ = ⟪f, onePortPrimitive f⟫_ℂ :=
      isSelfAdjoint_onePortPrimitive.isSymmetric f f
    rw [← inner_conj_symm] at hsym
    exact Complex.conj_eq_iff_im.1 hsym
  have him := congrArg Complex.im h1
  rw [hA, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add] at him
  rcases mul_eq_zero.1 him with h | h
  · exact h
  · exact absurd h (metricEnergy_pos hne).ne'

end

end RHTower
