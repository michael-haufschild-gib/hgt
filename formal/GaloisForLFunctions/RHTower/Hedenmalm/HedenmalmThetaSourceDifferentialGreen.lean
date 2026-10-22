import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceDifferentialPencil
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaActualStageGreenBalance
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricPencil
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPinnedBoundaryTwoPort
import GaloisForLFunctions.HTGeometry.ClosedGraphTransformAdjoint
import GaloisForLFunctions.HTGeometry.GraphSaturationCore

/-!
# Green law for the closed source-faithful theta differential pencil

The literal theta source inverse satisfies a singular-metric two-port commutator.  The closed
source-faithful differential pencil replaces its centered inverse coordinate by
`k + z • (B k - mean(B k) • 1)`.  This file transports the Green identity exactly through that
closed-graph coordinate.  The two monopole terms remain visible; omitting either would recover a
different pencil and lose the literal Xi divisor.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative
  HedenmalmFredholmRange GaloisForLFunctions.HTGeometry

private abbrev H := Lp ℂ 2 unitIntervalMeasure

private local instance thetaSourceDifferentialGreenComplete : CompleteSpace thetaCentered :=
  thetaCentered_isClosed.completeSpace_coe

section MetricRoot

local instance hedenmalmThetaSourceDifferentialGreenInst1 : ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The positive square root of the literal singular theta metric.  This is the dense energy
coordinate for a rigged completion; it is not a bounded similarity because the metric has no
lower bound. -/
noncomputable def thetaMetricRoot : H →L[ℂ] H := CFC.sqrt thetaMetricOperator

/-- Positivity of the source metric in operator order. -/
theorem thetaMetricOperator_nonneg : (0 : H →L[ℂ] H) ≤ thetaMetricOperator :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr thetaMetricOperator_isPositive

/-- The square-root energy coordinate factors the literal metric exactly. -/
theorem thetaMetricRoot_sq : thetaMetricRoot * thetaMetricRoot = thetaMetricOperator := by
  exact CFC.sqrt_mul_sqrt_self thetaMetricOperator thetaMetricOperator_nonneg

/-- The energy coordinate is self-adjoint in the original Hilbert space. -/
theorem thetaMetricRoot_selfAdjoint :
    ContinuousLinearMap.adjoint thetaMetricRoot = thetaMetricRoot := by
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg thetaMetricOperator)

/-- The energy coordinate remains injective, so it cannot erase a literal source fibre. -/
theorem thetaMetricRoot_injective : Function.Injective thetaMetricRoot := by
  intro x y hxy
  apply RHTower.thetaMetricOperator_injective
  rw [← thetaMetricRoot_sq]
  change thetaMetricRoot (thetaMetricRoot x) = thetaMetricRoot (thetaMetricRoot y)
  exact congrArg thetaMetricRoot hxy

/-- The energy-coordinate image is dense.  It therefore realizes the metric completion without
changing the ambient Hilbert carrier. -/
theorem thetaMetricRoot_dense_range : Dense (thetaMetricRoot.range : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  rw [thetaMetricRoot.orthogonal_range, thetaMetricRoot_selfAdjoint]
  exact LinearMap.ker_eq_bot.mpr thetaMetricRoot_injective

/-- The old singular Green pairing is exactly the ordinary Hilbert pairing after the energy
coordinate. -/
theorem thetaMetricRoot_energy (f g : H) :
    inner ℂ (thetaMetricRoot f) (thetaMetricRoot g) =
      inner ℂ (thetaMetricOperator f) g := by
  rw [← ContinuousLinearMap.adjoint_inner_left, thetaMetricRoot_selfAdjoint]
  change inner ℂ ((thetaMetricRoot * thetaMetricRoot) f) g = _
  rw [thetaMetricRoot_sq]


/-- The reciprocal-speed cutoff on a compact quantile interval.  It is the exact test vector
whose ordinary monopole and metric-root energy both recover the quantile increment. -/
private def thetaQuantileSpeedIntervalSymbol (a b : ℝ) : ℝ → ℂ :=
  (Ico a b).indicator fun t => (quantileSpeed thetaSource t : ℂ)

private theorem measurable_thetaQuantileSpeedIntervalSymbol (a b : ℝ) :
    Measurable (thetaQuantileSpeedIntervalSymbol a b) := by
  unfold thetaQuantileSpeedIntervalSymbol
  exact (Complex.measurable_ofReal.comp
    (measurable_const.div
      (thetaSource.continuous_k.measurable.comp thetaSource.measurable_quantileFun))).indicator
        measurableSet_Ico

private noncomputable def thetaQuantileSpeedIntervalCutoff (a b C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖thetaQuantileSpeedIntervalSymbol a b t‖ ≤ C) : H :=
  lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure)
    (measurable_thetaQuantileSpeedIntervalSymbol a b) hC0 hC pinnedOne

private theorem thetaQuantileSpeedIntervalCutoff_coeFn (a b C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖thetaQuantileSpeedIntervalSymbol a b t‖ ≤ C) :
    (thetaQuantileSpeedIntervalCutoff a b C hC0 hC : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      thetaQuantileSpeedIntervalSymbol a b := by
  unfold thetaQuantileSpeedIntervalCutoff
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure)
      (measurable_thetaQuantileSpeedIntervalSymbol a b) hC0 hC pinnedOne,
    pinnedOne_coeFn] with t ht h1
  rw [ht, h1, mul_one]

private theorem exists_thetaQuantileSpeedIntervalBound {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖thetaQuantileSpeedIntervalSymbol a b t‖ ≤ C := by
  have hcont : ContinuousOn (quantileSpeed thetaSource) (Icc a b) :=
    (HedenmalmQuantile.continuousOn_quantileSpeed thetaSource).mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg (quantileSpeed thetaSource a)) (hC a ⟨le_rfl, hab⟩)
  refine ⟨C, hC0, ?_⟩
  intro t
  by_cases ht : t ∈ Ico a b
  · rw [thetaQuantileSpeedIntervalSymbol, Set.indicator_of_mem ht]
    simpa [Real.norm_eq_abs, abs_of_pos (quantileSpeed_pos thetaSource t)] using
      hC t ⟨ht.1, ht.2.le⟩
  · rw [thetaQuantileSpeedIntervalSymbol, Set.indicator_of_notMem ht, norm_zero]
    exact hC0

/-- A compact reciprocal-speed cutoff has monopole exactly equal to the quantile increment. -/
private theorem pinnedMean_thetaQuantileSpeedIntervalCutoff (a b C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖thetaQuantileSpeedIntervalSymbol a b t‖ ≤ C)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    pinnedMean (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) =
      (thetaSource.quantileFun b - thetaSource.quantileFun a : ℂ) := by
  rw [← thetaPinnedMeanCLM_apply]
  change inner ℂ pinnedOne (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) = _
  rw [inner_lp_eq]
  calc
    (∫ t, (starRingEnd ℂ) ((pinnedOne : H) t) *
        (thetaQuantileSpeedIntervalCutoff a b C hC0 hC : H) t ∂unitIntervalMeasure) =
        ∫ t, (((Ico a b).indicator (fun t => quantileSpeed thetaSource t) t : ℝ) : ℂ)
          ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [pinnedOne_coeFn,
        thetaQuantileSpeedIntervalCutoff_coeFn a b C hC0 hC] with t h1 h2
      rw [h1, h2, map_one, one_mul, thetaQuantileSpeedIntervalSymbol]
      by_cases ht : t ∈ Ico a b
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
        norm_num
    _ = ((∫ t, (Ico a b).indicator (fun t => quantileSpeed thetaSource t) t
        ∂unitIntervalMeasure : ℝ) : ℂ) := by
      rw [integral_complex_ofReal]
    _ = thetaSource.quantileFun b - thetaSource.quantileFun a := by
      exact_mod_cast integral_quantileSpeed_indicator_Ico thetaSource ha hb hab

/-- The metric sends the reciprocal-speed cutoff to the ordinary interval indicator. -/
private theorem thetaMetricOperator_thetaQuantileSpeedIntervalCutoff (a b C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖thetaQuantileSpeedIntervalSymbol a b t‖ ≤ C)
    (hfin : unitIntervalMeasure (Ico a b) ≠ ∞) :
    thetaMetricOperator (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) =
      indicatorConstLp 2 measurableSet_Ico hfin (1 : ℂ) := by
  change metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le
      (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) =
    indicatorConstLp 2 measurableSet_Ico hfin (1 : ℂ)
  apply Lp.ext
  filter_upwards [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le (thetaQuantileSpeedIntervalCutoff a b C hC0 hC),
    thetaQuantileSpeedIntervalCutoff_coeFn a b C hC0 hC,
    indicatorConstLp_coeFn (p := 2) (μ := unitIntervalMeasure)
      (s := Ico a b) (hs := measurableSet_Ico) (hμs := hfin) (c := (1 : ℂ))]
      with t hM hF hI
  rw [hM, hF, hI, thetaQuantileSpeedIntervalSymbol]
  by_cases ht : t ∈ Ico a b
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
      metricSymbol_eq_inv_quantileSpeed]
    have hq : ((quantileSpeed thetaSource t : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (quantileSpeed_pos thetaSource t).ne'
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ hq
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]

/-- The metric-root energy of the reciprocal-speed cutoff is the same quantile increment as
its monopole.  This is the analytic source of the free completed monopole coordinate. -/
private theorem inner_thetaMetricRoot_thetaQuantileSpeedIntervalCutoff (a b C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖thetaQuantileSpeedIntervalSymbol a b t‖ ≤ C)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b)
    (hfin : unitIntervalMeasure (Ico a b) ≠ ∞) :
    inner ℂ (thetaMetricRoot (thetaQuantileSpeedIntervalCutoff a b C hC0 hC))
      (thetaMetricRoot (thetaQuantileSpeedIntervalCutoff a b C hC0 hC)) =
        (thetaSource.quantileFun b - thetaSource.quantileFun a : ℂ) := by
  have hmetric := thetaMetricOperator_thetaQuantileSpeedIntervalCutoff a b C hC0 hC hfin
  have hqint : ∫ t in Ico a b, quantileSpeed thetaSource t ∂unitIntervalMeasure =
      thetaSource.quantileFun b - thetaSource.quantileFun a := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ico]
    exact integral_quantileSpeed_indicator_Ico thetaSource ha hb hab
  calc
    inner ℂ (thetaMetricRoot (thetaQuantileSpeedIntervalCutoff a b C hC0 hC))
        (thetaMetricRoot (thetaQuantileSpeedIntervalCutoff a b C hC0 hC)) =
        inner ℂ (thetaMetricOperator (thetaQuantileSpeedIntervalCutoff a b C hC0 hC))
          (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) :=
      thetaMetricRoot_energy _ _
    _ = inner ℂ (indicatorConstLp 2 measurableSet_Ico hfin (1 : ℂ))
          (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) := by rw [hmetric]
    _ = ∫ t in Ico a b, (thetaQuantileSpeedIntervalCutoff a b C hC0 hC : H) t
          ∂unitIntervalMeasure :=
      MeasureTheory.L2.inner_indicatorConstLp_one measurableSet_Ico hfin _
    _ = ∫ t in Ico a b, (quantileSpeed thetaSource t : ℂ)
          ∂unitIntervalMeasure := by
      apply setIntegral_congr_ae measurableSet_Ico
      filter_upwards [thetaQuantileSpeedIntervalCutoff_coeFn a b C hC0 hC] with t ht
      intro hmem
      rw [ht, thetaQuantileSpeedIntervalSymbol, Set.indicator_of_mem hmem]
    _ = ((∫ t in Ico a b, quantileSpeed thetaSource t ∂unitIntervalMeasure : ℝ) : ℂ) := by
      rw [integral_complex_ofReal]
    _ = thetaSource.quantileFun b - thetaSource.quantileFun a := by
      exact_mod_cast hqint

end MetricRoot

/-- The constant mode has no metric-root preimage.  Compact reciprocal-speed cutoffs have
monopole and squared root energy both equal to an arbitrarily prescribed quantile increment,
which contradicts Cauchy--Schwarz for a putative preimage. -/
theorem thetaPinnedOne_not_mem_thetaMetricRoot_range :
    pinnedOne ∉ thetaMetricRoot.range := by
  rintro ⟨y, hy⟩
  let R : ℝ := ‖y‖ ^ 2 + 1
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  let a : ℝ := thetaSource.cdfFun (-R)
  let b : ℝ := thetaSource.cdfFun 0
  have ha : a ∈ Ioo (0 : ℝ) 1 := by
    dsimp [a]
    exact thetaSource.cdfFun_mem_Ioo _
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    dsimp [b]
    exact thetaSource.cdfFun_mem_Ioo _
  have hab : a ≤ b := by
    change thetaSource.cdfFun (-R) ≤ thetaSource.cdfFun 0
    exact (thetaSource.strictMono_cdfFun (neg_lt_zero.mpr hRpos)).le
  have hsub : Ico a b ⊆ Icc (0 : ℝ) 1 := by
    rintro t ⟨hta, htb⟩
    exact ⟨ha.1.le.trans hta, htb.le.trans hb.2.le⟩
  have hfin : unitIntervalMeasure (Ico a b) ≠ ∞ := by
    rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Ico,
      Set.inter_eq_self_of_subset_left hsub, Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  obtain ⟨C, hC0, hC⟩ := exists_thetaQuantileSpeedIntervalBound ha hb hab
  let f : H := thetaQuantileSpeedIntervalCutoff a b C hC0 hC
  have hinc : thetaSource.quantileFun b - thetaSource.quantileFun a = R := by
    dsimp [a, b]
    rw [thetaSource.quantile_cdfFun, thetaSource.quantile_cdfFun]
    ring
  have hincC : (thetaSource.quantileFun b : ℂ) - thetaSource.quantileFun a = (R : ℂ) := by
    exact_mod_cast hinc
  have hmean0 := pinnedMean_thetaQuantileSpeedIntervalCutoff a b C hC0 hC ha hb hab
  have henergy0 := inner_thetaMetricRoot_thetaQuantileSpeedIntervalCutoff
    a b C hC0 hC ha hb hab hfin
  have hmean : pinnedMean f = (R : ℂ) := by
    change pinnedMean (thetaQuantileSpeedIntervalCutoff a b C hC0 hC) = (R : ℂ)
    rw [hmean0, hincC]
  have henergy : inner ℂ (thetaMetricRoot f) (thetaMetricRoot f) = (R : ℂ) := by
    change inner ℂ (thetaMetricRoot (thetaQuantileSpeedIntervalCutoff a b C hC0 hC))
      (thetaMetricRoot (thetaQuantileSpeedIntervalCutoff a b C hC0 hC)) = (R : ℂ)
    rw [henergy0, hincC]
  have hmean_inner : pinnedMean f = inner ℂ pinnedOne f := by
    rw [← thetaPinnedMeanCLM_apply]
    rfl
  have hroot_transpose : inner ℂ (thetaMetricRoot y) f =
      inner ℂ y (thetaMetricRoot f) := by
    have h := ContinuousLinearMap.adjoint_inner_left thetaMetricRoot f y
    rw [thetaMetricRoot_selfAdjoint] at h
    exact h
  have hpair : (R : ℂ) = inner ℂ y (thetaMetricRoot f) := by
    calc
      (R : ℂ) = pinnedMean f := hmean.symm
      _ = inner ℂ pinnedOne f := hmean_inner
      _ = inner ℂ (thetaMetricRoot y) f :=
        congrArg (fun u : H => inner ℂ u f) hy.symm
      _ = inner ℂ y (thetaMetricRoot f) := hroot_transpose
  have hbound : R ≤ ‖y‖ * ‖thetaMetricRoot f‖ := by
    calc
      R = ‖(R : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
      _ = ‖inner ℂ y (thetaMetricRoot f)‖ := by rw [hpair]
      _ ≤ ‖y‖ * ‖thetaMetricRoot f‖ := norm_inner_le_norm _ _
  have henergyReal : ‖thetaMetricRoot f‖ ^ 2 = R := by
    calc
      ‖thetaMetricRoot f‖ ^ 2 =
          (inner ℂ (thetaMetricRoot f) (thetaMetricRoot f)).re :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = ((R : ℂ)).re := congrArg Complex.re henergy
      _ = R := Complex.ofReal_re _
  have hboundSq : R ^ 2 ≤ (‖y‖ * ‖thetaMetricRoot f‖) ^ 2 :=
    (sq_le_sq₀ hRpos.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hbound
  rw [mul_pow, henergyReal] at hboundSq
  dsimp [R] at hboundSq
  nlinarith [sq_nonneg ‖y‖]

/-- The exact graph that retains both the metric-root energy coordinate and the free monopole. -/
def thetaMonopoleEnergyGraph : Submodule ℂ (WithLp 2 (H × ℂ)) :=
  linearGraphSubmodule (thetaMetricRoot.comp thetaCenteredSourceInverse).toLinearMap
    (thetaPinnedMeanCLM.comp thetaCenteredSourceInverse).toLinearMap

/-- The free monopole removes every joint annihilator of the metric-root source graph. -/
theorem thetaMonopoleEnergyGraph_jointAnnihilator
    (x : H) (c : ℂ)
    (h : ∀ k : thetaCentered,
      inner ℂ (thetaMetricRoot (thetaCenteredSourceInverse k)) x +
        inner ℂ (pinnedMean (thetaCenteredSourceInverse k)) c = 0) :
    x = 0 ∧ c = 0 := by
  have hrelation : thetaMetricRoot x + c • pinnedOne = 0 := by
    apply thetaCenteredSourceInverse_dense_range.eq_zero_of_inner_right ℂ
    rintro _ ⟨k, rfl⟩
    have hk := h k
    have hroot : inner ℂ (thetaMetricRoot (thetaCenteredSourceInverse k)) x =
        inner ℂ (thetaCenteredSourceInverse k) (thetaMetricRoot x) := by
      have ht := ContinuousLinearMap.adjoint_inner_left thetaMetricRoot x
        (thetaCenteredSourceInverse k)
      rw [thetaMetricRoot_selfAdjoint] at ht
      exact ht
    have hmean : inner ℂ (pinnedMean (thetaCenteredSourceInverse k)) c =
        inner ℂ (thetaCenteredSourceInverse k) (c • pinnedOne) := by
      calc
        inner ℂ (pinnedMean (thetaCenteredSourceInverse k)) c =
            inner ℂ (thetaPinnedMeanCLM (thetaCenteredSourceInverse k)) c := by
          rw [thetaPinnedMeanCLM_apply]
        _ = inner ℂ (inner ℂ pinnedOne (thetaCenteredSourceInverse k)) c := rfl
        _ = inner ℂ (thetaCenteredSourceInverse k) (c • pinnedOne) := by
          rw [RCLike.inner_apply', inner_smul_right,
            inner_conj_symm (thetaCenteredSourceInverse k) pinnedOne]
          ring
    calc
      inner ℂ (thetaCenteredSourceInverse k) (thetaMetricRoot x + c • pinnedOne) =
          inner ℂ (thetaCenteredSourceInverse k) (thetaMetricRoot x) +
            inner ℂ (thetaCenteredSourceInverse k) (c • pinnedOne) :=
        inner_add_right _ _ _
      _ = inner ℂ (thetaMetricRoot (thetaCenteredSourceInverse k)) x +
            inner ℂ (pinnedMean (thetaCenteredSourceInverse k)) c := by
        rw [← hroot, ← hmean]
      _ = 0 := hk
  have hc : c = 0 := by
    by_contra hc
    apply thetaPinnedOne_not_mem_thetaMetricRoot_range
    refine ⟨-c⁻¹ • x, ?_⟩
    have hrootx : thetaMetricRoot x = -(c • pinnedOne) :=
      eq_neg_of_add_eq_zero_left hrelation
    calc
      thetaMetricRoot (-c⁻¹ • x) = -c⁻¹ • thetaMetricRoot x := by
        rw [map_smul]
      _ = -c⁻¹ • (-(c • pinnedOne)) := by rw [hrootx]
      _ = pinnedOne := by simp [smul_smul, hc]
  refine ⟨?_, hc⟩
  apply thetaMetricRoot_injective
  simpa [hc] using hrelation

/-- Completion of the literal energy--monopole graph is the full Hilbert product. -/
theorem thetaMonopoleEnergyGraph_closure_eq_top :
    thetaMonopoleEnergyGraph.topologicalClosure = ⊤ := by
  change (linearGraphSubmodule
    (thetaMetricRoot.comp thetaCenteredSourceInverse).toLinearMap
    (thetaPinnedMeanCLM.comp thetaCenteredSourceInverse).toLinearMap).topologicalClosure = ⊤
  apply linearGraphSubmodule_closure_eq_top_of_annihilator
  intro x c h
  apply thetaMonopoleEnergyGraph_jointAnnihilator x c
  intro k
  have hk := h k
  change inner ℂ (thetaMetricRoot (thetaCenteredSourceInverse k)) x +
      inner ℂ (thetaPinnedMeanCLM (thetaCenteredSourceInverse k)) c = 0 at hk
  simpa only [thetaPinnedMeanCLM_apply] using hk

/-- On the centered coordinate hyperplane, the closed-pencil inverse coordinate is the literal
theta source inverse. -/
theorem thetaCenteredSourceInverse_eq_thetaKernelOperator (k : thetaCentered) :
    thetaCenteredSourceInverse k = thetaKernelOperator (k : H) := by
  rw [thetaCenteredSourceInverse, ContinuousLinearMap.comp_apply]
  change thetaCompactSourceInverse (k : H) = thetaKernelOperator (k : H)
  rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]

/-- Green identity in the bounded coordinates that parameterize the closed differential domain. -/
theorem thetaCenteredSourceInverse_metricGreen (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) -
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) =
        -Complex.I * inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) := by
  have hgreen := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T (k : H)) (l : H) : ℂ))
    thetaMetric_commutator_thetaKernelOperator
  have hsub :
      (thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) =
        (thetaMetricOperator * thetaKernelOperator) (k : H) -
          (ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) := by
    change
      ((↑(thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) : H →ₗ[ℂ] H)
        (k : H)) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  rw [hsub, mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_left,
    smul_apply, inner_smul_left, ContinuousLinearMap.adjoint_inner_left] at hgreen
  rw [← thetaCenteredSourceInverse_eq_thetaKernelOperator k,
    ← thetaCenteredSourceInverse_eq_thetaKernelOperator l] at hgreen
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := by
    exact Complex.conj_I
  rw [hconjI] at hgreen
  simpa only [neg_mul] using hgreen

/-- The bounded Green defect is exactly the difference of its incoming and outgoing scalar-port
pairings. -/
theorem inner_pinnedBoundaryCLM_eq_twoPort_pair (k l : H) :
    (inner ℂ (pinnedBoundaryCLM k) l : ℂ) =
      (starRingEnd ℂ) (pinnedBoundaryInPort k) * pinnedBoundaryInPort l -
        (starRingEnd ℂ) (pinnedBoundaryOutPort k) * pinnedBoundaryOutPort l := by
  have hsub :
      (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) k =
        (pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort) k -
          (pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) k := by
    change
      ((↑(pinnedBoundaryInPort.adjoint.comp pinnedBoundaryInPort -
        pinnedBoundaryOutPort.adjoint.comp pinnedBoundaryOutPort) : H →ₗ[ℂ] H) k) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  have hports := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T k) l : ℂ)) pinnedBoundaryCLM_eq_port_difference
  rw [hsub, ContinuousLinearMap.comp_apply,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left] at hports
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] at hports
  simpa only [RCLike.inner_apply'] using hports

/-- The boundary form vanishes between any two centered source coordinates.  It can still send a
centered vector to the constant mode, but that mode is orthogonal to the entire centered carrier. -/
theorem inner_pinnedBoundaryCLM_thetaCentered_eq_zero (k l : thetaCentered) :
    (inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) : ℂ) = 0 := by
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  have hl : pinnedMean (l : H) = 0 :=
    (mem_thetaCentered_iff (l : H)).mp l.property
  have hinnerl : inner ℂ pinnedOne (l : H) = 0 := by
    change thetaPinnedMeanCLM (l : H) = 0
    rw [thetaPinnedMeanCLM_apply, hl]
  rw [pinnedBoundaryCLM_eq_affine_combination, hk]
  simp only [zero_sub, zero_smul, sub_zero, inner_smul_left]
  rw [hinnerl]
  simp

/-- Restoring the omitted scalar coordinate exposes the exact monopole--dipole normal form of
the boundary defect.  The defect pairs this scalar with the centered dipole; neither component
alone carries a nonzero boundary form. -/
theorem pinnedBoundaryCLM_thetaCentered_add_scalar (k : thetaCentered) (m : ℂ) :
    pinnedBoundaryCLM ((k : H) + m • pinnedOne) =
      (-pinnedFirstMoment (k : H)) • pinnedOne - m • pinnedCenter := by
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  rw [pinnedBoundaryCLM_eq_affine_combination,
    pinnedMean_add, pinnedMean_smul, pinnedMean_pinnedOne, hk,
    pinnedFirstMoment_add, pinnedFirstMoment_smul, pinnedFirstMoment_pinnedOne]
  simp only [zero_add, mul_one]
  rw [pinnedCenter]
  module

/-- On the centered source coordinate, the singular-metric commutator leaves exactly one
transverse constant channel.  This identifies the channel that a minimal Pontryagin realization
must couple to; the centered compression itself has no defect. -/
theorem thetaMetric_commutator_thetaCentered_eq_monopole (k : thetaCentered) :
    (thetaMetricOperator * thetaKernelOperator -
      ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) (k : H) =
        (-Complex.I * pinnedFirstMoment (k : H)) • pinnedOne := by
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  rw [thetaMetric_commutator_thetaKernelOperator, smul_apply,
    pinnedBoundaryCLM_eq_affine_combination, hk]
  module

/-- The centered dipole is a bounded trace in the ordinary Hilbert topology.  It is recorded
separately because its continuity in the singular metric is the capacity bottleneck. -/
def thetaCenteredDipoleTrace : thetaCentered →L[ℂ] ℂ :=
  (innerSL ℂ pinnedCenter).comp thetaCentered.subtypeL

theorem thetaCenteredDipoleTrace_apply (k : thetaCentered) :
    thetaCenteredDipoleTrace k = pinnedFirstMoment (k : H) := by
  change inner ℂ pinnedCenter (k : H) = pinnedFirstMoment (k : H)
  have hk : pinnedMean (k : H) = 0 :=
    (mem_thetaCentered_iff (k : H)).mp k.property
  have hinnerk : inner ℂ pinnedOne (k : H) = 0 := by
    change thetaPinnedMeanCLM (k : H) = 0
    rw [thetaPinnedMeanCLM_apply, hk]
  rw [pinnedCenter, inner_sub_left, inner_smul_left, hinnerk, mul_zero, sub_zero]
  rw [inner_lp_eq, pinnedFirstMoment]
  apply integral_congr_ae
  filter_upwards [pinnedCoordinate_coeFn] with t ht
  rw [ht]
  simp

/-- Closed graph-energy coordinate carrying the literal differential graph and its transverse
dipole trace.  The added trace repairs continuity at the singular boundary without changing the
source coordinate or its Xi kernel. -/
def thetaSourceDifferentialGraphEnergyCoordinate (z : ℂ) :
    thetaCentered →L[ℂ] ((H × H) × ℂ) :=
  (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)).prod
    thetaCenteredDipoleTrace

/-- Adding the dipole trace preserves the exact graph lower bound. -/
theorem thetaSourceDifferentialGraphEnergyCoordinate_antilipschitz (z : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c (thetaSourceDifferentialGraphEnergyCoordinate z) := by
  rcases thetaSourceDifferentialGraphMap_antilipschitz z with ⟨c, hc⟩
  refine ⟨c, (thetaSourceDifferentialGraphEnergyCoordinate z).antilipschitz_of_bound ?_⟩
  intro k
  have hbound := hc.le_mul_dist k 0
  simp only [dist_zero_right, map_zero] at hbound
  refine hbound.trans ?_
  gcongr
  exact norm_fst_le (thetaSourceDifferentialGraphEnergyCoordinate z k)

/-- The dipole-enriched graph coordinate has closed range, yielding a concrete closed energy
carrier for the monopole--dipole completion candidate. -/
theorem thetaSourceDifferentialGraphEnergyCoordinate_isClosed_range (z : ℂ) :
    IsClosed (Set.range (thetaSourceDifferentialGraphEnergyCoordinate z)) := by
  rcases thetaSourceDifferentialGraphEnergyCoordinate_antilipschitz z with ⟨c, hc⟩
  exact hc.isClosed_range (thetaSourceDifferentialGraphEnergyCoordinate z).uniformContinuous

/-- The closed boundary coordinate keeps both channels of the singular Green defect: the source
mean of the primitive and the dipole of the centered derivative coordinate.  It is deliberately
not a quotient of either channel, so its vertical fibre still represents the literal pencil
kernel. -/
def thetaSourceDifferentialBoundaryCoordinate (z : ℂ) :
    thetaCentered →L[ℂ] ((H × H) × (ℂ × ℂ)) :=
  (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)).prod
    ((thetaPinnedMeanCLM.comp thetaCenteredSourceInverse).prod thetaCenteredDipoleTrace)

theorem thetaSourceDifferentialBoundaryCoordinate_apply (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryCoordinate z k =
      ((thetaCenteredSourceInverse k, thetaSourceDifferentialRangeMap z k),
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)) := by
  simp [thetaSourceDifferentialBoundaryCoordinate, thetaPinnedMeanCLM_apply]

/-- The full monopole--dipole coordinate remains an antilipschitz parametrization of its source
carrier.  Hence adjoining the two boundary channels cannot introduce a spurious closure point. -/
theorem thetaSourceDifferentialBoundaryCoordinate_antilipschitz (z : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c (thetaSourceDifferentialBoundaryCoordinate z) := by
  rcases thetaSourceDifferentialGraphMap_antilipschitz z with ⟨c, hc⟩
  refine ⟨c, (thetaSourceDifferentialBoundaryCoordinate z).antilipschitz_of_bound ?_⟩
  intro k
  have hbound := hc.le_mul_dist k 0
  simp only [dist_zero_right, map_zero] at hbound
  calc
    ‖k‖ ≤ c * ‖(thetaCenteredSourceInverse.prod
        (thetaSourceDifferentialRangeMap z)) k‖ := hbound
    _ ≤ c * ‖thetaSourceDifferentialBoundaryCoordinate z k‖ := by
      gcongr
      have hfst : (thetaSourceDifferentialBoundaryCoordinate z k).1 =
          (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k := rfl
      rw [← hfst]
      exact norm_fst_le _

/-- The source-defined closed relation used for the singular completion candidate.  Its first
pair is the literal closed differential graph; its second pair is the complete hyperbolic
boundary record. -/
def thetaSourceDifferentialBoundaryRelation (z : ℂ) : Submodule ℂ ((H × H) × (ℂ × ℂ)) :=
  LinearMap.range (thetaSourceDifferentialBoundaryCoordinate z).toLinearMap

theorem thetaSourceDifferentialBoundaryRelation_isClosed (z : ℂ) :
    IsClosed (thetaSourceDifferentialBoundaryRelation z : Set ((H × H) × (ℂ × ℂ))) := by
  change IsClosed (Set.range (thetaSourceDifferentialBoundaryCoordinate z))
  rcases thetaSourceDifferentialBoundaryCoordinate_antilipschitz z with ⟨c, hc⟩
  exact hc.isClosed_range (thetaSourceDifferentialBoundaryCoordinate z).uniformContinuous

/-- Membership in the closed relation has a unique source witness.  This explicit presentation
prevents completion from silently replacing the source differential by a different graph. -/
theorem thetaSourceDifferentialBoundaryRelation_mem_iff
    (z : ℂ) (r : ((H × H) × (ℂ × ℂ))) :
    r ∈ thetaSourceDifferentialBoundaryRelation z ↔
      ∃ k : thetaCentered, thetaSourceDifferentialBoundaryCoordinate z k = r := by
  rfl

/-- The literal primitive coordinate of the closed boundary relation. -/
def thetaSourceDifferentialBoundarySourceProjection (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] H :=
  (ContinuousLinearMap.fst ℂ H H).comp
    ((ContinuousLinearMap.fst ℂ (H × H) (ℂ × ℂ)).comp
      (thetaSourceDifferentialBoundaryRelation z).subtypeL)

/-- The source leg of the closed boundary relation, realized in the dense square-root energy
coordinate. -/
def thetaSourceDifferentialBoundaryEnergyEmbedding (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] H :=
  thetaMetricRoot.comp (thetaSourceDifferentialBoundarySourceProjection z)

/-- The differential leg of the closed boundary relation in the same energy coordinate. -/
def thetaSourceDifferentialBoundaryEnergyReadout (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] H :=
  thetaMetricRoot.comp
    ((ContinuousLinearMap.snd ℂ H H).comp
      ((ContinuousLinearMap.fst ℂ (H × H) (ℂ × ℂ)).comp
        (thetaSourceDifferentialBoundaryRelation z).subtypeL))

/-- The canonical point of the closed boundary relation corresponding to a literal centered
source vector. -/
def thetaSourceDifferentialBoundaryCoordinateElement (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryRelation z :=
  ⟨thetaSourceDifferentialBoundaryCoordinate z k, ⟨k, rfl⟩⟩

/-- The complete monopole--dipole boundary record, read directly from an arbitrary element of
the closed source relation. -/
def thetaSourceDifferentialBoundaryPort (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℂ (H × H) (ℂ × ℂ)).comp
    (thetaSourceDifferentialBoundaryRelation z).subtypeL

theorem thetaSourceDifferentialBoundaryPort_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryPort z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k) := by
  simp [thetaSourceDifferentialBoundaryPort,
    thetaSourceDifferentialBoundaryCoordinateElement,
    thetaSourceDifferentialBoundaryCoordinate_apply]

theorem thetaSourceDifferentialBoundarySourceProjection_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundarySourceProjection z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      thetaCenteredSourceInverse k := by
  simp [thetaSourceDifferentialBoundarySourceProjection,
    thetaSourceDifferentialBoundaryCoordinateElement,
    thetaSourceDifferentialBoundaryCoordinate_apply]

theorem thetaSourceDifferentialBoundaryEnergyEmbedding_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryEnergyEmbedding z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      thetaMetricRoot (thetaCenteredSourceInverse k) := by
  simp [thetaSourceDifferentialBoundaryEnergyEmbedding,
    thetaSourceDifferentialBoundarySourceProjection_apply]

theorem thetaSourceDifferentialBoundaryEnergyReadout_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryEnergyReadout z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
      thetaMetricRoot (thetaSourceDifferentialRangeMap z k) := by
  simp [thetaSourceDifferentialBoundaryEnergyReadout,
    thetaSourceDifferentialBoundaryCoordinateElement,
    thetaSourceDifferentialBoundaryCoordinate_apply]

/-- The closed relation retains its source coordinate injectively. -/
theorem thetaSourceDifferentialBoundarySourceProjection_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundarySourceProjection z) := by
  intro r s hrs
  apply Subtype.ext
  have hrs' : r.1.1.1 = s.1.1.1 := by
    simpa [thetaSourceDifferentialBoundarySourceProjection] using hrs
  obtain ⟨k, hk⟩ := (thetaSourceDifferentialBoundaryRelation_mem_iff z r).mp r.property
  obtain ⟨l, hl⟩ := (thetaSourceDifferentialBoundaryRelation_mem_iff z s).mp s.property
  have hsource : thetaCenteredSourceInverse k = thetaCenteredSourceInverse l := by
    calc
      thetaCenteredSourceInverse k = r.1.1.1 := by
        have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.1) hk
        simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h
      _ = s.1.1.1 := hrs'
      _ = thetaCenteredSourceInverse l := by
        have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.1) hl
        simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h.symm
  have hkl : k = l := thetaCenteredSourceInverse_injective hsource
  calc
    (r : ((H × H) × (ℂ × ℂ))) = thetaSourceDifferentialBoundaryCoordinate z k := hk.symm
    _ = thetaSourceDifferentialBoundaryCoordinate z l := by rw [hkl]
    _ = s := hl

/-- The dense literal source range is retained by the closed-relation source projection. -/
theorem thetaSourceDifferentialBoundarySourceProjection_dense_range (z : ℂ) :
    Dense ((thetaSourceDifferentialBoundarySourceProjection z).range : Set H) := by
  apply thetaCenteredSourceInverse_dense_range.mono
  rintro x ⟨k, rfl⟩
  refine ⟨thetaSourceDifferentialBoundaryCoordinateElement z k, ?_⟩
  exact thetaSourceDifferentialBoundarySourceProjection_apply z k

/-- The square-root energy embedding of the closed relation is injective: it preserves every
literal source fibre while replacing the singular metric by ordinary Hilbert energy. -/
theorem thetaSourceDifferentialBoundaryEnergyEmbedding_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundaryEnergyEmbedding z) := by
  intro r s hrs
  apply thetaSourceDifferentialBoundarySourceProjection_injective z
  apply thetaMetricRoot_injective
  simpa [thetaSourceDifferentialBoundaryEnergyEmbedding] using hrs

/-- The energy embedding of the closed relation has dense range.  Together with the relation's
closedness, this supplies the source-faithful rigged Hilbert test embedding. -/
theorem thetaSourceDifferentialBoundaryEnergyEmbedding_dense_range (z : ℂ) :
    Dense ((thetaSourceDifferentialBoundaryEnergyEmbedding z).range : Set H) := by
  change DenseRange (fun r => thetaMetricRoot
    (thetaSourceDifferentialBoundarySourceProjection z r))
  exact DenseRange.comp thetaMetricRoot_dense_range
    (thetaSourceDifferentialBoundarySourceProjection_dense_range z)
    thetaMetricRoot.continuous

/-- The Riesz map of the energy relation into its continuous complex dual. It is necessarily
conjugate-linear in the ambient Hilbert coordinate: complex Hilbert spaces embed in the
continuous anti-dual, rather than linearly in the ordinary dual. -/
noncomputable def thetaSourceDifferentialBoundaryEnergyAntiDualLM (z : ℂ) :
    H →ₛₗ[starRingEnd ℂ]
      (thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ) where
  toFun := fun h => (innerSL ℂ h).comp
    (thetaSourceDifferentialBoundaryEnergyEmbedding z)
  map_add' := by
    intro x y
    apply ContinuousLinearMap.ext
    intro e
    change inner ℂ (x + y) (thetaSourceDifferentialBoundaryEnergyEmbedding z e) =
      inner ℂ x (thetaSourceDifferentialBoundaryEnergyEmbedding z e) +
        inner ℂ y (thetaSourceDifferentialBoundaryEnergyEmbedding z e)
    rw [inner_add_left]
  map_smul' := by
    intro q x
    apply ContinuousLinearMap.ext
    intro e
    change inner ℂ (q • x) (thetaSourceDifferentialBoundaryEnergyEmbedding z e) =
      (starRingEnd ℂ q) * inner ℂ x (thetaSourceDifferentialBoundaryEnergyEmbedding z e)
    rw [inner_smul_left]

/-- Continuous anti-dual realization of the literal dense energy embedding. -/
noncomputable def thetaSourceDifferentialBoundaryEnergyAntiDual (z : ℂ) :
    H →SL[starRingEnd ℂ]
      (thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ) :=
  @LinearMap.mkContinuous ℂ ℂ H
    (thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ) _ _ _ _ _ _
    (starRingEnd ℂ) (thetaSourceDifferentialBoundaryEnergyAntiDualLM z)
    ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ (by
      intro h
      change ‖(innerSL ℂ h).comp (thetaSourceDifferentialBoundaryEnergyEmbedding z)‖ ≤
        ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖h‖
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro e
      change ‖inner ℂ h (thetaSourceDifferentialBoundaryEnergyEmbedding z e)‖ ≤
        ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖h‖ * ‖e‖
      calc
        ‖inner ℂ h (thetaSourceDifferentialBoundaryEnergyEmbedding z e)‖ ≤
            ‖h‖ * ‖thetaSourceDifferentialBoundaryEnergyEmbedding z e‖ :=
          norm_inner_le_norm h (thetaSourceDifferentialBoundaryEnergyEmbedding z e)
        _ ≤ ‖h‖ * (‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖e‖) := by
          gcongr
          exact (thetaSourceDifferentialBoundaryEnergyEmbedding z).le_opNorm e
        _ = ‖thetaSourceDifferentialBoundaryEnergyEmbedding z‖ * ‖h‖ * ‖e‖ := by ring)

@[simp] theorem thetaSourceDifferentialBoundaryEnergyAntiDual_apply
    (z : ℂ) (h : H) (e : thetaSourceDifferentialBoundaryRelation z) :
    thetaSourceDifferentialBoundaryEnergyAntiDual z h e =
      inner ℂ h (thetaSourceDifferentialBoundaryEnergyEmbedding z e) := rfl

/-- Dense energy range makes the anti-dual embedding injective. -/
theorem thetaSourceDifferentialBoundaryEnergyAntiDual_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundaryEnergyAntiDual z) := by
  intro x y hxy
  apply (thetaSourceDifferentialBoundaryEnergyEmbedding_dense_range z).eq_of_inner_left ℂ
  rintro _ ⟨e, rfl⟩
  have he := congrArg (fun φ : thetaSourceDifferentialBoundaryRelation z →L[ℂ] ℂ => φ e) hxy
  simpa using he

/-- A nonzero vertical fibre of the closed relation is exactly a nonzero source vector killed by
the range coordinate. -/
theorem thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff (z : ℂ) :
    (∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
      r.1.2 = 0 ∧ r.1.1 ≠ 0) ↔
      ∃ k : thetaCentered, thetaSourceDifferentialRangeMap z k = 0 ∧
        thetaCenteredSourceInverse k ≠ 0 := by
  constructor
  · rintro ⟨r, hr, hrange, hsource⟩
    obtain ⟨k, hk⟩ := (thetaSourceDifferentialBoundaryRelation_mem_iff z r).mp hr
    refine ⟨k, ?_, ?_⟩
    · have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.2) hk
      simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h.trans hrange
    · have h := congrArg (fun x : ((H × H) × (ℂ × ℂ)) => x.1.1) hk
      intro hzero
      apply hsource
      simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using h.symm.trans hzero
  · rintro ⟨k, hrange, hsource⟩
    refine ⟨thetaSourceDifferentialBoundaryCoordinate z k,
      (thetaSourceDifferentialBoundaryRelation_mem_iff z _).mpr ⟨k, rfl⟩, ?_, ?_⟩
    · simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using hrange
    · simpa only [thetaSourceDifferentialBoundaryCoordinate_apply] using hsource

/-- The vertical fibre of the closed boundary relation is source-faithful: it is nontrivial
exactly when the literal closed differential pencil has a nontrivial kernel. -/
theorem thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff_pencil_kernel (z : ℂ) :
    (∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
      r.1.2 = 0 ∧ r.1.1 ≠ 0) ↔
      ∃ f : H, f ≠ 0 ∧ ∃ hf : f ∈ (thetaSourceDifferentialPencil z).domain,
        thetaSourceDifferentialPencil z ⟨f, hf⟩ = 0 := by
  rw [thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff]
  constructor
  · rintro ⟨k, hrange, hsource⟩
    refine ⟨thetaCenteredSourceInverse k, hsource, ?_⟩
    exact ⟨(thetaSourceDifferentialPencil_apply_B z k).1,
      (thetaSourceDifferentialPencil_apply_B z k).2.trans hrange⟩
  · rintro ⟨f, hf, hfdom, hdiff⟩
    have hfrange : f ∈ thetaCenteredSourceInverse.range := by
      simpa only [thetaSourceDifferentialPencil, closedGraphTransform_domain] using hfdom
    obtain ⟨k, hk⟩ := hfrange
    have hkdom : thetaCenteredSourceInverse k ∈ (thetaSourceDifferentialPencil z).domain :=
      (thetaSourceDifferentialPencil_apply_B z k).1
    have heq : (⟨f, hfdom⟩ : (thetaSourceDifferentialPencil z).domain) =
        ⟨thetaCenteredSourceInverse k, hkdom⟩ := Subtype.ext hk.symm
    have hrange : thetaSourceDifferentialRangeMap z k = 0 := by
      calc
        thetaSourceDifferentialRangeMap z k =
            thetaSourceDifferentialPencil z ⟨thetaCenteredSourceInverse k, hkdom⟩ :=
          (thetaSourceDifferentialPencil_apply_B z k).2.symm
        _ = thetaSourceDifferentialPencil z ⟨f, hfdom⟩ := congrArg
          (thetaSourceDifferentialPencil z) heq.symm
        _ = 0 := hdiff
    refine ⟨k, hrange, ?_⟩
    intro hzero
    apply hf
    rw [← hk]
    exact hzero

/-- The closed hyperbolic boundary relation retains the exact completed-Xi divisor rather than a
surrogate spectral equation. -/
theorem XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical (z : ℂ) :
    XiC z = 0 ↔
      ∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
        r.1.2 = 0 ∧ r.1.1 ≠ 0 := by
  exact (XiC_eq_zero_iff_exists_thetaSourceDifferentialPencil_kernel z).trans
    (thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff_pencil_kernel z).symm

/-- Bounded projection that removes precisely the pinned scalar mode retained by the source
correction.  This is the spectral weight in the literal differential pencil. -/
def thetaPinnedMeanProjection : H →L[ℂ] H :=
  1 - thetaPinnedMeanCLM.smulRight pinnedOne

theorem thetaPinnedMeanProjection_apply (f : H) :
    thetaPinnedMeanProjection f = f - pinnedMean f • pinnedOne := by
  simp [thetaPinnedMeanProjection, thetaPinnedMeanCLM_apply]

/-- The repaired differential pencil and the closed weighted derivative have the same source
domain. -/
theorem thetaSourceDifferentialPencil_domain (z : ℂ) :
    (thetaSourceDifferentialPencil z).domain = thetaWeightedDerivative.domain := by
  rw [thetaSourceDifferentialPencil, closedGraphTransform_domain,
    thetaWeightedDerivative, closedHyperplaneInverse_domain]

/-- **Source action identity.** On its literal closed graph the repaired pencil is exactly the
closed weighted derivative plus `z` times the pinned-mean projection.  In particular this does
not replace the Xi source equation by a different compact model. -/
theorem thetaSourceDifferentialPencil_apply_weightedDerivative
    (z : ℂ) (x : (thetaSourceDifferentialPencil z).domain) :
    thetaSourceDifferentialPencil z x =
      thetaWeightedDerivative
          ⟨(x : H), by simpa [thetaSourceDifferentialPencil_domain] using x.property⟩ +
        z • thetaPinnedMeanProjection (x : H) := by
  have hxrange : (x : H) ∈ thetaCenteredSourceInverse.range := by
    simpa only [thetaSourceDifferentialPencil, closedGraphTransform_domain] using x.property
  rcases hxrange with ⟨k, hk⟩
  have hxDiff : x =
      ⟨thetaCenteredSourceInverse k,
        (thetaSourceDifferentialPencil_apply_B z k).1⟩ :=
    Subtype.ext hk.symm
  have hxA : thetaCenteredSourceInverse k ∈ thetaWeightedDerivative.domain :=
    (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective k).1
  have hxeqA :
      (⟨(x : H), by simpa [thetaSourceDifferentialPencil_domain] using x.property⟩ :
        thetaWeightedDerivative.domain) =
      ⟨thetaCenteredSourceInverse k, hxA⟩ := Subtype.ext hk.symm
  have hDiffApply := (thetaSourceDifferentialPencil_apply_B z k).2
  have hAApply := (closedHyperplaneInverse_apply_B thetaCentered
    thetaCenteredSourceInverse thetaCenteredSourceInverse_injective k).2
  have hAApply' :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ = (k : H) := by
    change closedHyperplaneInverse thetaCentered thetaCenteredSourceInverse
      ⟨thetaCenteredSourceInverse k, hxA⟩ = (k : H)
    exact hAApply
  calc
    thetaSourceDifferentialPencil z x =
        thetaSourceDifferentialPencil z
          ⟨thetaCenteredSourceInverse k,
            (thetaSourceDifferentialPencil_apply_B z k).1⟩ :=
      congrArg (thetaSourceDifferentialPencil z) hxDiff
    _ = thetaSourceDifferentialRangeMap z k := hDiffApply
    _ = (k : H) + z •
        (thetaCenteredSourceInverse k -
          pinnedMean (thetaCenteredSourceInverse k) • pinnedOne) :=
      thetaSourceDifferentialRangeMap_apply z k
    _ = thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ +
        z • thetaPinnedMeanProjection (thetaCenteredSourceInverse k) := by
      rw [hAApply', thetaPinnedMeanProjection_apply]
    _ = thetaWeightedDerivative
          ⟨(x : H), by simpa [thetaSourceDifferentialPencil_domain] using x.property⟩ +
        z • thetaPinnedMeanProjection (x : H) := by
      rw [hxeqA]
      exact congrArg (fun y : H =>
        thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ +
          z • thetaPinnedMeanProjection y) hk

/-- The reverse pinned primitive sends the normalized constant precisely to the negative centered
coordinate.  This identifies the dual channel of the source mean. -/
theorem pinnedVolterraAdjoint_pinnedOne_eq_neg_center :
    pinnedVolterraAdjoint pinnedOne = -pinnedCenter := by
  change pinnedVolterraAdjointCLM pinnedOne = -pinnedCenter
  calc
    pinnedVolterraAdjointCLM pinnedOne =
        pinnedVolterraCLM pinnedOne + pinnedVolterraAdjointCLM pinnedOne := by
      rw [pinnedVolterraCLM_pinnedOne, zero_add]
    _ = pinnedBoundaryCLM pinnedOne := by rfl
    _ = (1 / 2 : ℂ) • pinnedOne - pinnedCoordinate :=
      pinnedBoundaryCLM_pinnedOne
    _ = -pinnedCenter := by
      rw [pinnedCenter]
      module

/-- The source trace dual to the pinned mean is exactly the centered dipole.  Thus the two scalar
channels in the spectral-weight Green defect are already present in the closed graph-energy
coordinate: `mean (B k)` and `firstMoment k`. -/
theorem inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse
    (k : thetaCentered) :
    (inner ℂ pinnedOne (thetaMetricOperator (thetaCenteredSourceInverse k)) : ℂ) =
      -Complex.I * thetaCenteredDipoleTrace k := by
  have hGB : thetaMetricOperator (thetaCenteredSourceInverse k) =
      Complex.I • pinnedVolterraCLM (k : H) := by
    rw [thetaCenteredSourceInverse_eq_thetaKernelOperator]
    change (thetaMetricOperator * thetaKernelOperator) (k : H) =
      (Complex.I • pinnedVolterraCLM) (k : H)
    rw [thetaMetricOperator_mul_thetaKernelOperator]
  have hVright :
      (inner ℂ (pinnedVolterra (k : H)) pinnedOne : ℂ) =
        inner ℂ (k : H) (pinnedVolterraAdjoint pinnedOne) :=
    inner_pinnedVolterra_eq_inner_pinnedVolterraAdjoint (k : H) pinnedOne
  have hVleft :
      (inner ℂ pinnedOne (pinnedVolterraCLM (k : H)) : ℂ) =
        -inner ℂ pinnedCenter (k : H) := by
    change (inner ℂ pinnedOne (pinnedVolterra (k : H)) : ℂ) = _
    rw [← inner_conj_symm, hVright, pinnedVolterraAdjoint_pinnedOne_eq_neg_center,
      inner_neg_right, map_neg, inner_conj_symm]
  have hdipole : inner ℂ pinnedCenter (k : H) = thetaCenteredDipoleTrace k := by
    rfl
  rw [hGB, inner_smul_right, hVleft, hdipole]
  ring

/-- The centered dipole is already a Riesz functional of the square-root energy source leg.
This exact rigidity determines one boundary coordinate inside the Hilbert energy completion. -/
theorem thetaCenteredDipoleTrace_eq_thetaMetricRoot_energy
    (k : thetaCentered) :
    thetaCenteredDipoleTrace k =
      Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
        (thetaMetricRoot (thetaCenteredSourceInverse k)) := by
  have henergy :
      inner ℂ (thetaMetricRoot pinnedOne)
        (thetaMetricRoot (thetaCenteredSourceInverse k)) =
        inner ℂ pinnedOne
          (thetaMetricOperator (thetaCenteredSourceInverse k)) := by
    calc
      inner ℂ (thetaMetricRoot pinnedOne)
          (thetaMetricRoot (thetaCenteredSourceInverse k)) =
          inner ℂ (thetaMetricOperator pinnedOne)
            (thetaCenteredSourceInverse k) :=
        thetaMetricRoot_energy pinnedOne (thetaCenteredSourceInverse k)
      _ = inner ℂ pinnedOne
          (thetaMetricOperator (thetaCenteredSourceInverse k)) := by
        calc
          inner ℂ (thetaMetricOperator pinnedOne)
              (thetaCenteredSourceInverse k) =
              inner ℂ (thetaMetricOperator.adjoint pinnedOne)
                (thetaCenteredSourceInverse k) := by
            rw [adjoint_thetaMetricOperator]
          _ = inner ℂ pinnedOne
              (thetaMetricOperator (thetaCenteredSourceInverse k)) := by
            rw [ContinuousLinearMap.adjoint_inner_left]
  rw [henergy, inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse]
  calc
    thetaCenteredDipoleTrace k = (1 : ℂ) * thetaCenteredDipoleTrace k := by ring
    _ = -(Complex.I * Complex.I) * thetaCenteredDipoleTrace k := by
      rw [Complex.I_mul_I]
      ring
    _ = Complex.I * (-Complex.I * thetaCenteredDipoleTrace k) := by ring

/-- **One-channel hyperbolic Green factorization.** The bounded spectral weight in the literal
source pencil has a metric skew defect only through the source mean and centered dipole.  Its
Hermitian boundary form is one hyperbolic plane, hence carries exactly one negative direction
once the closed relation action is completed. -/
theorem thetaPinnedMeanProjection_metricSkew_thetaCenteredSourceInverse
    (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
      (thetaCenteredSourceInverse l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)) =
      Complex.I *
        ((starRingEnd ℂ) (pinnedMean (thetaCenteredSourceInverse k)) *
            thetaCenteredDipoleTrace l +
          pinnedMean (thetaCenteredSourceInverse l) *
            (starRingEnd ℂ) (thetaCenteredDipoleTrace k)) := by
  have hleft :
      (inner ℂ (thetaMetricOperator pinnedOne)
        (thetaCenteredSourceInverse l) : ℂ) =
        inner ℂ pinnedOne
          (thetaMetricOperator (thetaCenteredSourceInverse l)) := by
    calc
      inner ℂ (thetaMetricOperator pinnedOne) (thetaCenteredSourceInverse l) =
          inner ℂ (thetaMetricOperator.adjoint pinnedOne)
            (thetaCenteredSourceInverse l) := by rw [adjoint_thetaMetricOperator]
      _ = inner ℂ pinnedOne
          (thetaMetricOperator (thetaCenteredSourceInverse l)) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
  have hright :
      (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) pinnedOne : ℂ) =
        (starRingEnd ℂ)
          (inner ℂ pinnedOne
            (thetaMetricOperator (thetaCenteredSourceInverse k))) := by
    rw [inner_conj_symm]
  rw [thetaPinnedMeanProjection_apply, thetaPinnedMeanProjection_apply,
    map_sub, map_smul, inner_sub_left, inner_smul_left,
    inner_sub_right, inner_smul_right, hleft, hright,
    inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse k,
    inner_pinnedOne_thetaMetric_thetaCenteredSourceInverse l]
  simp only [map_neg, map_mul, Complex.conj_I]
  ring

/-- Hermitian hyperbolic form on the source mean--dipole boundary pair. -/
def thetaMonopoleDipoleHyperbolicForm (u v : ℂ × ℂ) : ℂ :=
  (starRingEnd ℂ) u.1 * v.2 + v.1 * (starRingEnd ℂ) u.2

/-- Literal conjugation on the source monopole--dipole boundary plane. -/
def thetaMonopoleDipoleBoundaryConj (u : ℂ × ℂ) : ℂ × ℂ :=
  (-(starRingEnd ℂ u.1), (starRingEnd ℂ u.2))

/-- The Hodge operator forced by the source boundary reflection and exchange of the two
hyperbolic channels. -/
def thetaMonopoleDipoleHodge (u : ℂ × ℂ) : ℂ × ℂ :=
  (-(starRingEnd ℂ u.2), (starRingEnd ℂ u.1))

/-- The source boundary Hodge operator is anti-complex with square `-1`. -/
theorem thetaMonopoleDipoleHodge_sq (u : ℂ × ℂ) :
    thetaMonopoleDipoleHodge (thetaMonopoleDipoleHodge u) = -u := by
  ext <;> simp [thetaMonopoleDipoleHodge]

theorem thetaMonopoleDipoleHodge_add (u v : ℂ × ℂ) :
    thetaMonopoleDipoleHodge (u + v) =
      thetaMonopoleDipoleHodge u + thetaMonopoleDipoleHodge v := by
  ext <;> simp [thetaMonopoleDipoleHodge, map_add, add_comm]

theorem thetaMonopoleDipoleHodge_smul (c : ℂ) (u : ℂ × ℂ) :
    thetaMonopoleDipoleHodge (c • u) =
      (starRingEnd ℂ c) • thetaMonopoleDipoleHodge u := by
  ext <;> simp [thetaMonopoleDipoleHodge, smul_eq_mul]

/-- The source boundary Hodge operator as a conjugate-semilinear map. -/
def thetaMonopoleDipoleHodgeSLM :
    (ℂ × ℂ) →ₛₗ[starRingEnd ℂ] (ℂ × ℂ) where
  toFun := thetaMonopoleDipoleHodge
  map_add' := thetaMonopoleDipoleHodge_add
  map_smul' := thetaMonopoleDipoleHodge_smul

/-- Bilinear boundary cup form obtained from the literal reflected hyperbolic Green form. -/
def thetaMonopoleDipoleCup (u v : ℂ × ℂ) : ℂ :=
  -thetaMonopoleDipoleHyperbolicForm (thetaMonopoleDipoleBoundaryConj u) v

/-- The reflected hyperbolic boundary plane has a positive Hodge diagonal. -/
theorem thetaMonopoleDipoleCup_hodge (u : ℂ × ℂ) :
    thetaMonopoleDipoleCup u (thetaMonopoleDipoleHodge u) =
      (Complex.normSq u.1 : ℂ) + (Complex.normSq u.2 : ℂ) := by
  simp only [thetaMonopoleDipoleCup, thetaMonopoleDipoleHyperbolicForm,
    thetaMonopoleDipoleBoundaryConj, thetaMonopoleDipoleHodge, map_neg,
    starRingEnd_self_apply, neg_mul]
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  ring

/-- Diagonal coordinates split the boundary form into one positive and one negative complex
line.  This is the exact rank-one negative channel required by the singular completion. -/
theorem thetaMonopoleDipoleHyperbolicForm_diagonal
    (m d m' d' : ℂ) :
    thetaMonopoleDipoleHyperbolicForm (m, d) (m', d') =
      (1 / 2 : ℂ) *
        ((starRingEnd ℂ) (m + d) * (m' + d') -
          (starRingEnd ℂ) (m - d) * (m' - d')) := by
  simp only [thetaMonopoleDipoleHyperbolicForm, map_add, map_sub]
  ring

theorem thetaMonopoleDipoleHyperbolicForm_positive_unit :
    thetaMonopoleDipoleHyperbolicForm ((1 : ℂ), 1) (1, 1) = 2 := by
  norm_num [thetaMonopoleDipoleHyperbolicForm]

theorem thetaMonopoleDipoleHyperbolicForm_negative_unit :
    thetaMonopoleDipoleHyperbolicForm ((1 : ℂ), -1) (1, -1) = -2 := by
  norm_num [thetaMonopoleDipoleHyperbolicForm]

/-- The spectral-weight Green defect is exactly the hyperbolic mean--dipole boundary form of
the closed source relation. -/
theorem thetaPinnedMeanProjection_metricSkew_eq_hyperbolic
    (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
      (thetaCenteredSourceInverse l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)) =
      Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l) := by
  simpa only [thetaMonopoleDipoleHyperbolicForm] using
    thetaPinnedMeanProjection_metricSkew_thetaCenteredSourceInverse k l

/-- The unperturbed closed source action is symmetric for the singular theta metric on its exact
source graph.  Thus every failure of a Pontryagin realization of `D_z` is concentrated in the
bounded pinned-mean spectral weight and its one transverse defect channel. -/
theorem thetaWeightedDerivative_metricSymmetric_on_sourceGraph
    (k l : thetaCentered)
    (hk : thetaCenteredSourceInverse k ∈ thetaWeightedDerivative.domain)
    (hl : thetaCenteredSourceInverse l ∈ thetaWeightedDerivative.domain) :
    (inner ℂ (thetaMetricOperator
        (thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hk⟩))
      (thetaCenteredSourceInverse l) : ℂ) =
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaWeightedDerivative ⟨thetaCenteredSourceInverse l, hl⟩) := by
  have hgreen := thetaCenteredSourceInverse_metricGreen k l
  have hzero := inner_pinnedBoundaryCLM_thetaCentered_eq_zero k l
  rw [hzero, mul_zero] at hgreen
  have hswap :
      inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) =
        inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) :=
    sub_eq_zero.mp hgreen
  have hkApply :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hk⟩ = (k : H) := by
    have h := (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective k).2
    have h' : thetaWeightedDerivative
        ⟨thetaCenteredSourceInverse k,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective k).1⟩ = (k : H) := by
      simpa only [thetaWeightedDerivative] using h
    have heq : (⟨thetaCenteredSourceInverse k, hk⟩ : thetaWeightedDerivative.domain) =
        ⟨thetaCenteredSourceInverse k,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective k).1⟩ := Subtype.ext rfl
    exact (congrArg thetaWeightedDerivative heq).trans h'
  have hlApply :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse l, hl⟩ = (l : H) := by
    have h := (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective l).2
    have h' : thetaWeightedDerivative
        ⟨thetaCenteredSourceInverse l,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective l).1⟩ = (l : H) := by
      simpa only [thetaWeightedDerivative] using h
    have heq : (⟨thetaCenteredSourceInverse l, hl⟩ : thetaWeightedDerivative.domain) =
        ⟨thetaCenteredSourceInverse l,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective l).1⟩ := Subtype.ext rfl
    exact (congrArg thetaWeightedDerivative heq).trans h'
  rw [hkApply, hlApply]
  exact hswap.symm

/-- The two scalar boundary ports are hyperbolically isotropic on the exact bounded coordinate of
the closed source pencil.  Thus this coordinate alone cannot supply its required negative square. -/
theorem thetaCentered_twoPort_isotropic (k l : thetaCentered) :
    (starRingEnd ℂ) (pinnedBoundaryInPort (k : H)) * pinnedBoundaryInPort (l : H) =
      (starRingEnd ℂ) (pinnedBoundaryOutPort (k : H)) * pinnedBoundaryOutPort (l : H) := by
  have hzero := inner_pinnedBoundaryCLM_thetaCentered_eq_zero k l
  rw [inner_pinnedBoundaryCLM_eq_twoPort_pair] at hzero
  exact sub_eq_zero.mp hzero

/-- Green identity in the literal incoming/outgoing coordinates on the closed-pencil graph. -/
theorem thetaCenteredSourceInverse_twoPortGreen (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) -
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) =
        -Complex.I *
          ((starRingEnd ℂ) (pinnedBoundaryInPort (k : H)) *
              pinnedBoundaryInPort (l : H) -
            (starRingEnd ℂ) (pinnedBoundaryOutPort (k : H)) *
              pinnedBoundaryOutPort (l : H)) := by
  rw [thetaCenteredSourceInverse_metricGreen,
    inner_pinnedBoundaryCLM_eq_twoPort_pair]

/-- On the centered coordinate, the source inverse is symmetric for the singular metric. -/
theorem thetaCenteredSourceInverse_metricSymmetric (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k)) (l : H) : ℂ) =
      inner ℂ (thetaMetricOperator (k : H)) (thetaCenteredSourceInverse l) := by
  apply sub_eq_zero.mp
  rw [thetaCenteredSourceInverse_metricGreen,
    inner_pinnedBoundaryCLM_thetaCentered_eq_zero]
  ring

/-- Exact parameterized Green law for the closed source-faithful differential pencil.  The
additional two terms are its required monopole correction; they are not a removable boundary
normalization. -/
theorem thetaSourceDifferentialRangeMap_metricGreen
    (z w : ℂ) (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap w l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
      -Complex.I * inner ℂ (pinnedBoundaryCLM (k : H)) (l : H) +
        w * inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
          (thetaCenteredSourceInverse l -
            pinnedMean (thetaCenteredSourceInverse l) • pinnedOne) -
        (starRingEnd ℂ) z *
          inner ℂ (thetaMetricOperator
            (thetaCenteredSourceInverse k -
              pinnedMean (thetaCenteredSourceInverse k) • pinnedOne))
            (thetaCenteredSourceInverse l) := by
  rw [thetaSourceDifferentialRangeMap_apply,
    thetaSourceDifferentialRangeMap_apply,
    map_add, map_smul, inner_add_right, inner_smul_right,
    inner_add_left, inner_smul_left]
  linear_combination thetaCenteredSourceInverse_metricGreen k l

/-- Conjugate spectral parameters expose only the one hyperbolic boundary plane.  The full
closed source relation therefore has an exact Green law compatible with Schwarz reflection while
retaining its literal `XiC` vertical fibre. -/
theorem thetaSourceDifferentialRangeMap_metricGreen_conj
    (z : ℂ) (k l : thetaCentered) :
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
  have hgreen := thetaSourceDifferentialRangeMap_metricGreen z (starRingEnd ℂ z) k l
  have hzero := inner_pinnedBoundaryCLM_thetaCentered_eq_zero k l
  rw [hzero, mul_zero, zero_add,
    ← thetaPinnedMeanProjection_apply (thetaCenteredSourceInverse l),
    ← thetaPinnedMeanProjection_apply (thetaCenteredSourceInverse k)] at hgreen
  have hskew := thetaPinnedMeanProjection_metricSkew_eq_hyperbolic k l
  calc
    (inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
        (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l) : ℂ) -
      inner ℂ (thetaMetricOperator (thetaSourceDifferentialRangeMap z k))
        (thetaCenteredSourceInverse l) =
        (starRingEnd ℂ) z *
            inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
              (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)) -
          (starRingEnd ℂ) z *
            inner ℂ (thetaMetricOperator
              (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
              (thetaCenteredSourceInverse l) := hgreen
    _ = -(starRingEnd ℂ z *
        ((inner ℂ (thetaMetricOperator
            (thetaPinnedMeanProjection (thetaCenteredSourceInverse k)))
          (thetaCenteredSourceInverse l) : ℂ) -
          inner ℂ (thetaMetricOperator (thetaCenteredSourceInverse k))
            (thetaPinnedMeanProjection (thetaCenteredSourceInverse l)))) := by ring
    _ = -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
      rw [hskew]
      ring

/-- The exact conjugate-parameter Green law on the closed, dense energy test relation.  Both
legs remain the literal source primitive and differential coordinates, while the right-hand side
is the single hyperbolic monopole--dipole boundary plane. -/
theorem thetaSourceDifferentialBoundaryEnergy_green_conj
    (z : ℂ) (k l : thetaCentered) :
    (inner ℂ
        (thetaSourceDifferentialBoundaryEnergyEmbedding z
          (thetaSourceDifferentialBoundaryCoordinateElement z k))
        (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z)
          (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l)) : ℂ) -
      inner ℂ
        (thetaSourceDifferentialBoundaryEnergyReadout z
          (thetaSourceDifferentialBoundaryCoordinateElement z k))
        (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z)
          (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l)) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
  rw [thetaSourceDifferentialBoundaryEnergyEmbedding_apply,
    thetaSourceDifferentialBoundaryEnergyReadout_apply,
    thetaSourceDifferentialBoundaryEnergyReadout_apply,
    thetaSourceDifferentialBoundaryEnergyEmbedding_apply,
    thetaMetricRoot_energy, thetaMetricRoot_energy]
  exact thetaSourceDifferentialRangeMap_metricGreen_conj z k l

/-- The same Green defect expressed in the only complex-linear dual category available to the
energy relation: the first term is the conjugate of an anti-dual evaluation, while the second
is a reflected anti-dual evaluation. -/
theorem thetaSourceDifferentialBoundaryEnergyAntiDual_green_conj
    (z : ℂ) (k l : thetaCentered) :
    (starRingEnd ℂ)
        (thetaSourceDifferentialBoundaryEnergyAntiDual z
          (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z)
            (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l))
          (thetaSourceDifferentialBoundaryCoordinateElement z k)) -
      thetaSourceDifferentialBoundaryEnergyAntiDual (starRingEnd ℂ z)
        (thetaSourceDifferentialBoundaryEnergyReadout z
          (thetaSourceDifferentialBoundaryCoordinateElement z k))
        (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (pinnedMean (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k)
        (pinnedMean (thetaCenteredSourceInverse l), thetaCenteredDipoleTrace l)) := by
  rw [thetaSourceDifferentialBoundaryEnergyAntiDual_apply,
    thetaSourceDifferentialBoundaryEnergyAntiDual_apply, inner_conj_symm]
  exact thetaSourceDifferentialBoundaryEnergy_green_conj z k l

/-- Universal anti-dual Green identity.  Every closed-relation element has a unique literal
source representative, so the hyperbolic boundary defect is a relation invariant rather than a
formula limited to chosen coordinates. -/
theorem thetaSourceDifferentialBoundaryEnergyAntiDual_green_conj_all
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z)
    (s : thetaSourceDifferentialBoundaryRelation (starRingEnd ℂ z)) :
    (starRingEnd ℂ)
        (thetaSourceDifferentialBoundaryEnergyAntiDual z
          (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z) s) r) -
      thetaSourceDifferentialBoundaryEnergyAntiDual (starRingEnd ℂ z)
        (thetaSourceDifferentialBoundaryEnergyReadout z r) s =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (thetaSourceDifferentialBoundaryPort z r)
        (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) := by
  obtain ⟨k, hk⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff z (r : ((H × H) × (ℂ × ℂ)))).mp r.property
  obtain ⟨l, hl⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff (starRingEnd ℂ z)
      (s : ((H × H) × (ℂ × ℂ)))).mp s.property
  have hr : r = thetaSourceDifferentialBoundaryCoordinateElement z k := by
    apply Subtype.ext
    exact hk.symm
  have hs : s = thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l := by
    apply Subtype.ext
    exact hl.symm
  rw [hr, hs, thetaSourceDifferentialBoundaryPort_apply,
    thetaSourceDifferentialBoundaryPort_apply]
  exact thetaSourceDifferentialBoundaryEnergyAntiDual_green_conj z k l

/-- Universal energy-form Green identity on the closed source relation.  Unique literal source
witnesses transport the coordinate calculation to every completed relation element. -/
theorem thetaSourceDifferentialBoundaryEnergy_green_conj_all
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z)
    (s : thetaSourceDifferentialBoundaryRelation (starRingEnd ℂ z)) :
    (inner ℂ
        (thetaSourceDifferentialBoundaryEnergyEmbedding z r)
        (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z) s) : ℂ) -
      inner ℂ
        (thetaSourceDifferentialBoundaryEnergyReadout z r)
        (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z) s) =
      -(starRingEnd ℂ z * Complex.I * thetaMonopoleDipoleHyperbolicForm
        (thetaSourceDifferentialBoundaryPort z r)
        (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) := by
  obtain ⟨k, hk⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff z
      (r : ((H × H) × (ℂ × ℂ)))).mp r.property
  obtain ⟨l, hl⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff (starRingEnd ℂ z)
      (s : ((H × H) × (ℂ × ℂ)))).mp s.property
  have hr : r = thetaSourceDifferentialBoundaryCoordinateElement z k := by
    apply Subtype.ext
    exact hk.symm
  have hs : s = thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l := by
    apply Subtype.ext
    exact hl.symm
  rw [hr, hs, thetaSourceDifferentialBoundaryPort_apply,
    thetaSourceDifferentialBoundaryPort_apply]
  exact thetaSourceDifferentialBoundaryEnergy_green_conj z k l

/-- The completed source embedding retains both the literal energy vector and its complete
monopole--dipole boundary record. -/
def thetaSourceDifferentialBoundaryAugmentedEmbedding (z : ℂ)
    (r : thetaSourceDifferentialBoundaryRelation z) : H × (ℂ × ℂ) :=
  (thetaSourceDifferentialBoundaryEnergyEmbedding z r,
    thetaSourceDifferentialBoundaryPort z r)

/-- The unique scalar boundary flow which cancels the exact Green defect of the closed source
relation. -/
def thetaSourceDifferentialBoundaryAugmentedReadout (z : ℂ)
    (r : thetaSourceDifferentialBoundaryRelation z) : H × (ℂ × ℂ) :=
  (thetaSourceDifferentialBoundaryEnergyReadout z r,
    (Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)

/-- Energy plus the source monopole--dipole Green form on the augmented carrier. -/
def thetaSourceDifferentialBoundaryAugmentedGreenPair
    (x y : H × (ℂ × ℂ)) : ℂ :=
  inner ℂ x.1 y.1 + thetaMonopoleDipoleHyperbolicForm x.2 y.2

/-- The augmented closed source relation satisfies an exact conjugate-parameter Green law.
The coefficient `I / 2` is forced: its boundary skew term cancels the literal rank-two defect. -/
theorem thetaSourceDifferentialBoundaryAugmented_green_conj
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z)
    (s : thetaSourceDifferentialBoundaryRelation (starRingEnd ℂ z)) :
    thetaSourceDifferentialBoundaryAugmentedGreenPair
        (thetaSourceDifferentialBoundaryAugmentedEmbedding z r)
        (thetaSourceDifferentialBoundaryAugmentedReadout (starRingEnd ℂ z) s) =
      thetaSourceDifferentialBoundaryAugmentedGreenPair
        (thetaSourceDifferentialBoundaryAugmentedReadout z r)
        (thetaSourceDifferentialBoundaryAugmentedEmbedding (starRingEnd ℂ z) s) := by
  unfold thetaSourceDifferentialBoundaryAugmentedGreenPair
    thetaSourceDifferentialBoundaryAugmentedEmbedding
    thetaSourceDifferentialBoundaryAugmentedReadout
  dsimp only
  have hgreen := thetaSourceDifferentialBoundaryEnergy_green_conj_all z r s
  have hboundary :
      thetaMonopoleDipoleHyperbolicForm
          (thetaSourceDifferentialBoundaryPort z r)
          ((Complex.I / 2 * (starRingEnd ℂ z)) •
            thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) -
        thetaMonopoleDipoleHyperbolicForm
          ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)
          (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) =
        Complex.I * (starRingEnd ℂ z) *
          thetaMonopoleDipoleHyperbolicForm
            (thetaSourceDifferentialBoundaryPort z r)
            (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) := by
    simp only [thetaMonopoleDipoleHyperbolicForm, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, map_mul, map_div₀, Complex.conj_I, map_ofNat]
    ring
  calc
    _ =
        (inner ℂ (thetaSourceDifferentialBoundaryEnergyEmbedding z r)
            (thetaSourceDifferentialBoundaryEnergyReadout (starRingEnd ℂ z) s) -
          inner ℂ (thetaSourceDifferentialBoundaryEnergyReadout z r)
            (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z) s)) +
          (thetaMonopoleDipoleHyperbolicForm
              (thetaSourceDifferentialBoundaryPort z r)
              ((Complex.I / 2 * (starRingEnd ℂ z)) •
                thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s) -
            thetaMonopoleDipoleHyperbolicForm
              ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)
              (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) +
            (inner ℂ (thetaSourceDifferentialBoundaryEnergyReadout z r)
                (thetaSourceDifferentialBoundaryEnergyEmbedding (starRingEnd ℂ z) s) +
              thetaMonopoleDipoleHyperbolicForm
                ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z r)
                (thetaSourceDifferentialBoundaryPort (starRingEnd ℂ z) s)) := by ring
    _ = _ := by rw [hgreen, hboundary]; ring

/-- The Hilbert completion of the finite monopole--dipole boundary plane.  Raw products carry
the Banach product norm, so the `WithLp` carrier is required before taking Hilbert adjoints. -/
private abbrev thetaMonopoleDipoleHilbert : Type := WithLp 2 (ℂ × ℂ)

/-- The true Hilbert carrier for energy plus its complete finite source boundary. -/
private abbrev thetaSourceDifferentialBoundaryAugmentedHilbert : Type :=
  WithLp 2 (H × thetaMonopoleDipoleHilbert)

/-- The channel exchange on the raw boundary coordinates. -/
def thetaMonopoleDipoleFundamentalSymmetryRaw :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)

/-- Isometric packing of the raw boundary pair into its Hilbert completion. -/
noncomputable def thetaMonopoleDipoleHilbertPack :
    (ℂ × ℂ) →L[ℂ] thetaMonopoleDipoleHilbert :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap

@[simp] theorem thetaMonopoleDipoleHilbertPack_ofLp (u : ℂ × ℂ) :
    (thetaMonopoleDipoleHilbertPack u).ofLp = u := rfl

/-- Fundamental symmetry of the completed finite boundary carrier. -/
noncomputable def thetaMonopoleDipoleFundamentalSymmetry :
    thetaMonopoleDipoleHilbert →L[ℂ] thetaMonopoleDipoleHilbert :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.toContinuousLinearMap).comp
    (thetaMonopoleDipoleFundamentalSymmetryRaw.comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).toContinuousLinearMap)

@[simp] theorem thetaMonopoleDipoleFundamentalSymmetry_ofLp
    (u : thetaMonopoleDipoleHilbert) :
    (thetaMonopoleDipoleFundamentalSymmetry u).ofLp =
      (u.ofLp.2, u.ofLp.1) := rfl

/-- Pack energy and finite source boundary into the genuine orthogonal Hilbert sum. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedHilbertPack :
    (H × (ℂ × ℂ)) →L[ℂ] thetaSourceDifferentialBoundaryAugmentedHilbert :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).symm :
    H × thetaMonopoleDipoleHilbert →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedHilbert).comp
      ((ContinuousLinearMap.fst ℂ H (ℂ × ℂ)).prod
        (thetaMonopoleDipoleHilbertPack.comp
          (ContinuousLinearMap.snd ℂ H (ℂ × ℂ))))

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedHilbertPack_ofLp
    (x : H × (ℂ × ℂ)) :
    (thetaSourceDifferentialBoundaryAugmentedHilbertPack x).ofLp =
      (x.1, thetaMonopoleDipoleHilbertPack x.2) := rfl

/-- Fundamental symmetry on the completed energy--boundary Hilbert carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedHilbert :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).symm :
    H × thetaMonopoleDipoleHilbert →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedHilbert).comp
      (((ContinuousLinearMap.fst ℂ H thetaMonopoleDipoleHilbert).prod
        (thetaMonopoleDipoleFundamentalSymmetry.comp
          (ContinuousLinearMap.snd ℂ H thetaMonopoleDipoleHilbert))).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert) :
          thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
            H × thetaMonopoleDipoleHilbert))

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_ofLp
    (x : thetaSourceDifferentialBoundaryAugmentedHilbert) :
    (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x).ofLp =
      (x.ofLp.1, thetaMonopoleDipoleFundamentalSymmetry x.ofLp.2) := rfl

/-- Energy coordinate on the completed source--boundary Hilbert carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedEnergyProjection :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] H :=
  (ContinuousLinearMap.fst ℂ H thetaMonopoleDipoleHilbert).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert) :
      thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
        H × thetaMonopoleDipoleHilbert)

/-- Completed monopole projection. -/
noncomputable def thetaMonopoleDipoleHilbertMonopoleProjection :
    thetaMonopoleDipoleHilbert →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ) :
      thetaMonopoleDipoleHilbert →L[ℂ] ℂ × ℂ)

/-- Completed dipole projection. -/
noncomputable def thetaMonopoleDipoleHilbertDipoleProjection :
    thetaMonopoleDipoleHilbert →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ) :
      thetaMonopoleDipoleHilbert →L[ℂ] ℂ × ℂ)

/-- Monopole coordinate on the completed source--boundary Hilbert carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedMonopoleProjection :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] ℂ :=
  thetaMonopoleDipoleHilbertMonopoleProjection.comp
    ((ContinuousLinearMap.snd ℂ H thetaMonopoleDipoleHilbert).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert) :
        thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
          H × thetaMonopoleDipoleHilbert))

/-- Dipole coordinate on the completed source--boundary Hilbert carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleProjection :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] ℂ :=
  thetaMonopoleDipoleHilbertDipoleProjection.comp
    ((ContinuousLinearMap.snd ℂ H thetaMonopoleDipoleHilbert).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert) :
        thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
          H × thetaMonopoleDipoleHilbert))

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedEnergyProjection_pack
    (x : H × (ℂ × ℂ)) :
    thetaSourceDifferentialBoundaryAugmentedEnergyProjection
      (thetaSourceDifferentialBoundaryAugmentedHilbertPack x) = x.1 := rfl

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedMonopoleProjection_pack
    (x : H × (ℂ × ℂ)) :
    thetaSourceDifferentialBoundaryAugmentedMonopoleProjection
      (thetaSourceDifferentialBoundaryAugmentedHilbertPack x) = x.2.1 := rfl

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjection_pack
    (x : H × (ℂ × ℂ)) :
    thetaSourceDifferentialBoundaryAugmentedDipoleProjection
      (thetaSourceDifferentialBoundaryAugmentedHilbertPack x) = x.2.2 := rfl

/-- The closed constraint forced by the dipole Riesz law. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleConstraint :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] ℂ :=
  thetaSourceDifferentialBoundaryAugmentedDipoleProjection -
    Complex.I • ((innerSL ℂ (thetaMetricRoot pinnedOne)).comp
      thetaSourceDifferentialBoundaryAugmentedEnergyProjection)

/-- The closed source polarization: dipole equals its exact energy Riesz functional. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :
    Submodule ℂ thetaSourceDifferentialBoundaryAugmentedHilbert :=
  LinearMap.ker thetaSourceDifferentialBoundaryAugmentedDipoleConstraint.toLinearMap

/-- The swapped closed constraint on the monopole coordinate. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] ℂ :=
  thetaSourceDifferentialBoundaryAugmentedMonopoleProjection -
    Complex.I • ((innerSL ℂ (thetaMetricRoot pinnedOne)).comp
      thetaSourceDifferentialBoundaryAugmentedEnergyProjection)

/-- The Hodge-swapped source polarization. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :
    Submodule ℂ thetaSourceDifferentialBoundaryAugmentedHilbert :=
  LinearMap.ker thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint.toLinearMap

theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_isClosed :
    IsClosed (thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :
      Set thetaSourceDifferentialBoundaryAugmentedHilbert) :=
  ContinuousLinearMap.isClosed_ker _

theorem thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier_isClosed :
    IsClosed (thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :
      Set thetaSourceDifferentialBoundaryAugmentedHilbert) :=
  ContinuousLinearMap.isClosed_ker _

/-- The literal Green pairing is the ordinary Hilbert pairing after finite completion and the
fundamental symmetry. -/
theorem thetaSourceDifferentialBoundaryAugmented_inner_fundamentalSymmetry_pack
    (u v : H × (ℂ × ℂ)) :
    inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedHilbertPack u))
        (thetaSourceDifferentialBoundaryAugmentedHilbertPack v) =
      thetaSourceDifferentialBoundaryAugmentedGreenPair u v := by
  rw [WithLp.prod_inner_apply,
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_ofLp,
    thetaSourceDifferentialBoundaryAugmentedHilbertPack_ofLp,
    thetaSourceDifferentialBoundaryAugmentedHilbertPack_ofLp,
    WithLp.prod_inner_apply,
    thetaMonopoleDipoleFundamentalSymmetry_ofLp,
    thetaMonopoleDipoleHilbertPack_ofLp,
    thetaMonopoleDipoleHilbertPack_ofLp,
    thetaSourceDifferentialBoundaryAugmentedGreenPair,
    thetaMonopoleDipoleHyperbolicForm]
  simp only [RCLike.inner_apply']
  ring

/-- Complete monopole--dipole source port, before passing to the Hilbert boundary carrier. -/
def thetaSourceDifferentialBoundaryPortSource : thetaCentered →L[ℂ] (ℂ × ℂ) :=
  (thetaPinnedMeanCLM.comp thetaCenteredSourceInverse).prod thetaCenteredDipoleTrace

/-- Bounded source embedding into the completed Hilbert Green carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (_z : ℂ) :
    thetaCentered →L[ℂ] thetaSourceDifferentialBoundaryAugmentedHilbert :=
  thetaSourceDifferentialBoundaryAugmentedHilbertPack.comp
    ((thetaMetricRoot.comp thetaCenteredSourceInverse).prod
      thetaSourceDifferentialBoundaryPortSource)

/-- Bounded differential readout into the completed Hilbert Green carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedReadoutCLM (z : ℂ) :
    thetaCentered →L[ℂ] thetaSourceDifferentialBoundaryAugmentedHilbert :=
  thetaSourceDifferentialBoundaryAugmentedHilbertPack.comp
    ((thetaMetricRoot.comp (thetaSourceDifferentialRangeMap z)).prod
      ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPortSource))

theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k =
      thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaSourceDifferentialBoundaryAugmentedEmbedding z
          (thetaSourceDifferentialBoundaryCoordinateElement z k)) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  apply Prod.ext
  · exact (thetaSourceDifferentialBoundaryEnergyEmbedding_apply z k).symm
  · change thetaMonopoleDipoleHilbertPack
      (thetaSourceDifferentialBoundaryPortSource k) =
        thetaMonopoleDipoleHilbertPack
          (thetaSourceDifferentialBoundaryPort z
            (thetaSourceDifferentialBoundaryCoordinateElement z k))
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    simpa [thetaSourceDifferentialBoundaryPortSource, thetaPinnedMeanCLM_apply] using
      (thetaSourceDifferentialBoundaryPort_apply z k).symm

theorem thetaSourceDifferentialBoundaryAugmentedReadoutCLM_apply
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k =
      thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaSourceDifferentialBoundaryAugmentedReadout z
          (thetaSourceDifferentialBoundaryCoordinateElement z k)) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  apply Prod.ext
  · exact (thetaSourceDifferentialBoundaryEnergyReadout_apply z k).symm
  · change thetaMonopoleDipoleHilbertPack
      ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPortSource k) =
        thetaMonopoleDipoleHilbertPack
          ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z
            (thetaSourceDifferentialBoundaryCoordinateElement z k))
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    change (Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPortSource k =
      (Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPort z
        (thetaSourceDifferentialBoundaryCoordinateElement z k)
    rw [thetaSourceDifferentialBoundaryPort_apply]
    simp [thetaSourceDifferentialBoundaryPortSource, thetaPinnedMeanCLM_apply]

/-- The completed Hilbert embedding retains every literal source fibre. -/
theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z) := by
  intro k l hkl
  apply thetaCenteredSourceInverse_injective
  apply thetaMetricRoot_injective
  have hfst := congrArg
    (fun x : thetaSourceDifferentialBoundaryAugmentedHilbert => x.ofLp.1) hkl
  exact hfst

/-- Every literal source vector lands in the exact dipole-constrained polarization. -/
theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_mem_dipoleCarrier
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k ∈
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier := by
  change thetaSourceDifferentialBoundaryAugmentedDipoleConstraint
      (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k) = 0
  change thetaCenteredDipoleTrace k -
      Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
        (thetaMetricRoot (thetaCenteredSourceInverse k)) = 0
  rw [thetaCenteredDipoleTrace_eq_thetaMetricRoot_energy]
  ring

/-- Bounded raw parametrization of the closed dipole carrier by energy and free monopole. -/
noncomputable def thetaEnergyMonopoleToDipoleRaw :
    (H × ℂ) →L[ℂ] (H × (ℂ × ℂ)) :=
  (ContinuousLinearMap.fst ℂ H ℂ).prod
    ((ContinuousLinearMap.snd ℂ H ℂ).prod
      ((Complex.I • innerSL ℂ (thetaMetricRoot pinnedOne)).comp
        (ContinuousLinearMap.fst ℂ H ℂ)))

/-- The bounded graph of the dipole Riesz coordinate inside the exact carrier. -/
noncomputable def thetaEnergyMonopoleToDipoleCarrier :
    WithLp 2 (H × ℂ) →L[ℂ] thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  (thetaSourceDifferentialBoundaryAugmentedHilbertPack.comp
    (thetaEnergyMonopoleToDipoleRaw.comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).toContinuousLinearMap)).codRestrict
        thetaSourceDifferentialBoundaryAugmentedDipoleCarrier (by
          intro u
          change Complex.I * inner ℂ (thetaMetricRoot pinnedOne) u.ofLp.1 -
            Complex.I * inner ℂ (thetaMetricRoot pinnedOne) u.ofLp.1 = 0
          ring)

/-- The graph map has exactly the prescribed energy, monopole, and dipole coordinates. -/
theorem thetaEnergyMonopoleToDipoleCarrier_apply (u : WithLp 2 (H × ℂ)) :
    ((thetaEnergyMonopoleToDipoleCarrier u :
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier) :
        thetaSourceDifferentialBoundaryAugmentedHilbert) =
      thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (u.ofLp.1, (u.ofLp.2,
          Complex.I * inner ℂ (thetaMetricRoot pinnedOne) u.ofLp.1)) := by
  rfl

/-- Every dipole-carrier vector is recovered from its energy and monopole coordinates. -/
theorem thetaEnergyMonopoleToDipoleCarrier_surjective :
    Function.Surjective thetaEnergyMonopoleToDipoleCarrier := by
  intro u
  let v : WithLp 2 (H × ℂ) := WithLp.toLp 2
    (thetaSourceDifferentialBoundaryAugmentedEnergyProjection (u :
      thetaSourceDifferentialBoundaryAugmentedHilbert),
      thetaSourceDifferentialBoundaryAugmentedMonopoleProjection (u :
        thetaSourceDifferentialBoundaryAugmentedHilbert))
  have hu : thetaSourceDifferentialBoundaryAugmentedDipoleProjection (u :
      thetaSourceDifferentialBoundaryAugmentedHilbert) =
      Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
        (thetaSourceDifferentialBoundaryAugmentedEnergyProjection (u :
          thetaSourceDifferentialBoundaryAugmentedHilbert)) := by
    have hmem := u.property
    change thetaSourceDifferentialBoundaryAugmentedDipoleConstraint
      (u : thetaSourceDifferentialBoundaryAugmentedHilbert) = 0 at hmem
    exact sub_eq_zero.mp hmem
  refine ⟨v, ?_⟩
  apply Subtype.ext
  rw [thetaEnergyMonopoleToDipoleCarrier_apply]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  apply Prod.ext
  · change v.ofLp.1 = thetaSourceDifferentialBoundaryAugmentedEnergyProjection
      (u : thetaSourceDifferentialBoundaryAugmentedHilbert)
    rfl
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    apply Prod.ext
    · change v.ofLp.2 = thetaSourceDifferentialBoundaryAugmentedMonopoleProjection
        (u : thetaSourceDifferentialBoundaryAugmentedHilbert)
      rfl
    · change Complex.I * inner ℂ (thetaMetricRoot pinnedOne) v.ofLp.1 =
        thetaSourceDifferentialBoundaryAugmentedDipoleProjection (u :
          thetaSourceDifferentialBoundaryAugmentedHilbert)
      rw [show v.ofLp.1 = thetaSourceDifferentialBoundaryAugmentedEnergyProjection
        (u : thetaSourceDifferentialBoundaryAugmentedHilbert) by rfl]
      exact hu.symm

/-- Literal source admission into the dense energy--monopole graph completion. -/
noncomputable def thetaMonopoleEnergyGraphAdmission : thetaCentered →L[ℂ] WithLp 2 (H × ℂ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    ((thetaMetricRoot.comp thetaCenteredSourceInverse).prod
      (thetaPinnedMeanCLM.comp thetaCenteredSourceInverse))

@[simp] theorem thetaMonopoleEnergyGraphAdmission_ofLp (k : thetaCentered) :
    (thetaMonopoleEnergyGraphAdmission k).ofLp =
      (thetaMetricRoot (thetaCenteredSourceInverse k),
        thetaPinnedMeanCLM (thetaCenteredSourceInverse k)) := rfl

/-- The literal source is dense after adjoining its free monopole coordinate. -/
theorem thetaMonopoleEnergyGraphAdmission_dense : DenseRange thetaMonopoleEnergyGraphAdmission := by
  change Dense (thetaMonopoleEnergyGraph : Set (WithLp 2 (H × ℂ)))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    thetaMonopoleEnergyGraph_closure_eq_top

/-- The actual source embedding with codomain restricted to its exact dipole carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM (z : ℂ) :
    thetaCentered →L[ℂ] thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z).codRestrict
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier
    (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_mem_dipoleCarrier z)

/-- The literal source embedding is exactly the bounded dipole graph over its energy--monopole
admission. -/
theorem thetaEnergyMonopoleToDipoleCarrier_comp_graphAdmission (z : ℂ) :
    thetaEnergyMonopoleToDipoleCarrier.comp thetaMonopoleEnergyGraphAdmission =
      thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z := by
  apply ContinuousLinearMap.ext
  intro k
  apply Subtype.ext
  change ((thetaEnergyMonopoleToDipoleCarrier
    (thetaMonopoleEnergyGraphAdmission k) :
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier) :
        thetaSourceDifferentialBoundaryAugmentedHilbert) =
    thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k
  rw [thetaEnergyMonopoleToDipoleCarrier_apply]
  change thetaSourceDifferentialBoundaryAugmentedHilbertPack
      (thetaMetricRoot (thetaCenteredSourceInverse k),
        (thetaPinnedMeanCLM (thetaCenteredSourceInverse k),
          Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
            (thetaMetricRoot (thetaCenteredSourceInverse k)))) =
    thetaSourceDifferentialBoundaryAugmentedHilbertPack
      (thetaMetricRoot (thetaCenteredSourceInverse k),
        (thetaPinnedMeanCLM (thetaCenteredSourceInverse k), thetaCenteredDipoleTrace k))
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  apply Prod.ext
  · rfl
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    apply Prod.ext
    · rfl
    · rw [thetaCenteredDipoleTrace_eq_thetaMetricRoot_energy]

/-- The literal source is dense in its exact dipole-constrained Hilbert carrier. -/
theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM_dense (z : ℂ) :
    DenseRange (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z) := by
  have hcomp := (thetaEnergyMonopoleToDipoleCarrier_surjective.denseRange).comp
    thetaMonopoleEnergyGraphAdmission_dense thetaEnergyMonopoleToDipoleCarrier.continuous
  change DenseRange (fun k => thetaEnergyMonopoleToDipoleCarrier
    (thetaMonopoleEnergyGraphAdmission k)) at hcomp
  change DenseRange (fun k => thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k)
  have heq : (fun k => thetaEnergyMonopoleToDipoleCarrier
      (thetaMonopoleEnergyGraphAdmission k)) =
      (fun k => thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) := by
    funext k
    exact congrArg (fun T : thetaCentered →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier => T k)
      (thetaEnergyMonopoleToDipoleCarrier_comp_graphAdmission z)
  rw [heq] at hcomp
  exact hcomp

/-- The fundamental symmetry exchanges the exact dipole and monopole constraints. -/
theorem thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint_comp_fundamentalSymmetry :
    thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint.comp
      thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry =
    thetaSourceDifferentialBoundaryAugmentedDipoleConstraint := by
  apply ContinuousLinearMap.ext
  intro x
  change x.ofLp.2.ofLp.2 - Complex.I *
      inner ℂ (thetaMetricRoot pinnedOne) x.ofLp.1 =
    x.ofLp.2.ofLp.2 - Complex.I *
      inner ℂ (thetaMetricRoot pinnedOne) x.ofLp.1
  rfl

/-- The finite fundamental symmetry carries the source polarization to its exact swapped
polarization. -/
theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_maps_dipoleCarrier :
    Set.MapsTo thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier := by
  intro x hx
  change thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x) = 0
  change thetaSourceDifferentialBoundaryAugmentedDipoleConstraint x = 0 at hx
  have hconstraint := congrArg
    (fun T : thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] ℂ => T x)
    thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint_comp_fundamentalSymmetry
  exact hconstraint.trans hx

/-- The finite symmetry is involutive on the completed energy--boundary Hilbert carrier. -/
theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply_apply
    (x : thetaSourceDifferentialBoundaryAugmentedHilbert) :
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x) = x := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  change (x.ofLp.1,
    thetaMonopoleDipoleFundamentalSymmetry
      (thetaMonopoleDipoleFundamentalSymmetry x.ofLp.2)) =
    (x.ofLp.1, x.ofLp.2)
  apply Prod.ext
  · rfl
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    change (x.ofLp.2.ofLp.1, x.ofLp.2.ofLp.2) =
      (x.ofLp.2.ofLp.1, x.ofLp.2.ofLp.2)
    rfl

theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_sq :
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
      thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  simpa using thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply_apply x

/-- The symmetry also transports the swapped monopole constraint back to the dipole constraint. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleConstraint_comp_fundamentalSymmetry :
    thetaSourceDifferentialBoundaryAugmentedDipoleConstraint.comp
      thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry =
    thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint := by
  apply ContinuousLinearMap.ext
  intro x
  change x.ofLp.2.ofLp.1 - Complex.I *
      inner ℂ (thetaMetricRoot pinnedOne) x.ofLp.1 =
    x.ofLp.2.ofLp.1 - Complex.I *
      inner ℂ (thetaMetricRoot pinnedOne) x.ofLp.1
  rfl

/-- The fundamental symmetry carries the swapped monopole polarization back to the dipole one. -/
theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_maps_monopoleCarrier :
    Set.MapsTo thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier := by
  intro x hx
  change thetaSourceDifferentialBoundaryAugmentedDipoleConstraint
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry x) = 0
  change thetaSourceDifferentialBoundaryAugmentedMonopoleConstraint x = 0 at hx
  have hconstraint := congrArg
    (fun T : thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ] ℂ => T x)
    thetaSourceDifferentialBoundaryAugmentedDipoleConstraint_comp_fundamentalSymmetry
  exact hconstraint.trans hx

/-- Restricted symmetry from dipole to swapped monopole carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.subtypeL).codRestrict
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier (by
        intro x
        exact thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_maps_dipoleCarrier
          x.property)

/-- Restricted symmetry from swapped monopole to dipole carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedMonopoleToDipole :
    thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
    thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.subtypeL).codRestrict
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier (by
        intro x
        exact thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_maps_monopoleCarrier
          x.property)

/-- The restricted dipole--monopole symmetry is onto. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole_surjective :
    Function.Surjective thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole := by
  intro y
  refine ⟨thetaSourceDifferentialBoundaryAugmentedMonopoleToDipole y, ?_⟩
  apply Subtype.ext
  exact thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_apply_apply y

/-- The finite correction has become a literal Hilbert Green law on the source Hilbert space. -/
theorem thetaSourceDifferentialBoundaryAugmentedHilbert_green_conj
    (z : ℂ) (k l : thetaCentered) :
    inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k))
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l) =
      inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k))
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z) l) := by
  rw [thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_apply,
    thetaSourceDifferentialBoundaryAugmentedReadoutCLM_apply,
    thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_apply,
    thetaSourceDifferentialBoundaryAugmentedReadoutCLM_apply,
    thetaSourceDifferentialBoundaryAugmented_inner_fundamentalSymmetry_pack,
    thetaSourceDifferentialBoundaryAugmented_inner_fundamentalSymmetry_pack]
  exact thetaSourceDifferentialBoundaryAugmented_green_conj z
    (thetaSourceDifferentialBoundaryCoordinateElement z k)
    (thetaSourceDifferentialBoundaryCoordinateElement (starRingEnd ℂ z) l)

/-- Exact bounded adjoint transport forced by the literal finite Green completion.  The source
embedding is now dense in its exact dipole carrier; maximal transport next requires the explicit
closed-transform comparison between the dipole and symmetry-swapped monopole carriers. -/
theorem thetaSourceDifferentialBoundaryAugmented_adjoint_intertwining (z : ℂ) :
    (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z)).adjoint.comp
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z)) =
    (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z)).adjoint.comp
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry.comp
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z)) := by
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_right ℂ
  intro l
  simp only [ContinuousLinearMap.comp_apply]
  rw [
    (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z)).adjoint_inner_left,
    (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z)).adjoint_inner_left]
  exact thetaSourceDifferentialBoundaryAugmentedHilbert_green_conj z k l

/-! ### Exact two-carrier maximal-adjoint transport -/

local instance thetaSourceDifferentialBoundaryAugmentedDipoleCarrierComplete :
    CompleteSpace thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_isClosed.completeSpace_coe

local instance thetaSourceDifferentialBoundaryAugmentedMonopoleCarrierComplete :
    CompleteSpace thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier_isClosed.completeSpace_coe

local instance thetaSourceDifferentialBoundaryAugmentedDipoleCarrierHasProjection :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

local instance thetaSourceDifferentialBoundaryAugmentedMonopoleCarrierHasProjection :
    thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Orthogonal projection of a Green vector into the exact dipole polarization. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleCarrierProjectCLM :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection.codRestrict
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier
    (fun x => thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection_apply_mem x)

/-- Orthogonal projection of a Green vector into the swapped monopole polarization. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedMonopoleCarrierProjectCLM :
    thetaSourceDifferentialBoundaryAugmentedHilbert →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.starProjection.codRestrict
    thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier
    (fun x => thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.starProjection_apply_mem x)

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrierProjectCLM_coe
    (x : thetaSourceDifferentialBoundaryAugmentedHilbert) :
    ((thetaSourceDifferentialBoundaryAugmentedDipoleCarrierProjectCLM x :
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier) :
        thetaSourceDifferentialBoundaryAugmentedHilbert) =
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection x := rfl

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedMonopoleCarrierProjectCLM_coe
    (x : thetaSourceDifferentialBoundaryAugmentedHilbert) :
    ((thetaSourceDifferentialBoundaryAugmentedMonopoleCarrierProjectCLM x :
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier) :
        thetaSourceDifferentialBoundaryAugmentedHilbert) =
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.starProjection x := rfl

/-- The unique finite-boundary normal forced by the dipole Riesz constraint.  Removing a
multiple of this vector changes a metric-root lift only by the literal root of `pinnedOne`. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal :
    thetaSourceDifferentialBoundaryAugmentedHilbert :=
  thetaSourceDifferentialBoundaryAugmentedHilbertPack
    (Complex.I • thetaMetricRoot pinnedOne, (0, 1))

/-- The finite-boundary normal is orthogonal to every exact dipole carrier vector. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal_mem_orthogonal :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal ∈
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrierᗮ := by
  intro w hw
  rw [inner_eq_zero_symm]
  have hwconstraint :
      thetaSourceDifferentialBoundaryAugmentedDipoleProjection w =
        Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
          (thetaSourceDifferentialBoundaryAugmentedEnergyProjection w) := by
    change thetaSourceDifferentialBoundaryAugmentedDipoleConstraint w = 0 at hw
    exact sub_eq_zero.mp hw
  change w.ofLp.2.ofLp.2 =
    Complex.I * inner ℂ (thetaMetricRoot pinnedOne) w.ofLp.1 at hwconstraint
  change inner ℂ
    (thetaSourceDifferentialBoundaryAugmentedHilbertPack
      (Complex.I • thetaMetricRoot pinnedOne, (0, 1))) w = 0
  rw [WithLp.prod_inner_apply,
    thetaSourceDifferentialBoundaryAugmentedHilbertPack_ofLp,
    WithLp.prod_inner_apply,
    thetaMonopoleDipoleHilbertPack_ofLp,
    inner_smul_left, RCLike.inner_apply', hwconstraint]
  simp

/-- Once a scalar multiple of the finite normal lands in the exact carrier, it is exactly the
orthogonal correction.  This turns projection regularity into a scalar boundary equation. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_eq_sub_smul_normal
    (x : thetaSourceDifferentialBoundaryAugmentedHilbert) (c : ℂ)
    (hmem : x - c • thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal ∈
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier) :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection x =
      x - c • thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  have hnormal : inner ℂ thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal w = 0 :=
    inner_eq_zero_symm.mp
      (thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal_mem_orthogonal w hw)
  have hsub : x - (x - c • thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal) =
      c • thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal := by
    module
  rw [hsub, inner_smul_left, hnormal, mul_zero]

/-- The exact dipole-carrier candidate obtained by a finite normal correction of a metric-root
lift. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate
    (q : H) (m c : ℂ) : thetaSourceDifferentialBoundaryAugmentedHilbert :=
  thetaSourceDifferentialBoundaryAugmentedHilbertPack
    (thetaMetricRoot (q - (c * Complex.I) • pinnedOne),
      (m, Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
        (thetaMetricRoot (q - (c * Complex.I) • pinnedOne))))

/-- The corrected candidate satisfies the exact dipole Riesz constraint. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate_mem
    (q : H) (m c : ℂ) :
    thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate q m c ∈
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier := by
  change Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
      (thetaMetricRoot (q - (c * Complex.I) • pinnedOne)) -
        Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
          (thetaMetricRoot (q - (c * Complex.I) • pinnedOne)) = 0
  ring

/-- The scalar boundary equation identifies the normal correction with the explicit
metric-root candidate. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjection_input_sub_normal_eq_candidate
    (q : H) (m d c : ℂ)
    (hc : d =
      Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
        (thetaMetricRoot (q - (c * Complex.I) • pinnedOne)) + c) :
    thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaMetricRoot q, (m, d)) -
      c • thetaSourceDifferentialBoundaryAugmentedDipoleCarrierNormal =
        thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate q m c := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  apply Prod.ext
  · change thetaMetricRoot q - c • (Complex.I • thetaMetricRoot pinnedOne) =
      thetaMetricRoot (q - (c * Complex.I) • pinnedOne)
    rw [map_sub, map_smul]
    module
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    apply Prod.ext
    · change m - c * 0 = m
      ring
    · change d - c * 1 =
        Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
          (thetaMetricRoot (q - (c * Complex.I) • pinnedOne))
      rw [hc]
      ring

/-- Orthogonal dipole projection of a metric-root lift is an explicit finite correction.  The
only input is the scalar boundary equation, so all infinite-dimensional regularity remains in
the corrected primitive. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_metricRoot
    (q : H) (m d c : ℂ)
    (hc : d =
      Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
        (thetaMetricRoot (q - (c * Complex.I) • pinnedOne)) + c) :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection
      (thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaMetricRoot q, (m, d))) =
      thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate q m c := by
  rw [thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_eq_sub_smul_normal]
  · exact thetaSourceDifferentialBoundaryAugmentedDipoleProjection_input_sub_normal_eq_candidate
      q m d c hc
  · rw [thetaSourceDifferentialBoundaryAugmentedDipoleProjection_input_sub_normal_eq_candidate
      q m d c hc]
    exact thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate_mem q m c

/-- The scalar denominator of the finite normal correction is strictly nonzero. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjection_den_ne_zero :
    (1 + inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne) : ℂ) ≠ 0 := by
  rw [inner_self_eq_norm_sq_to_K]
  simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity :
    0 < 1 + ‖thetaMetricRoot pinnedOne‖ ^ 2)))

/-- The unique scalar that corrects a metric-root lift into the exact dipole carrier. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar
    (q : H) (d : ℂ) : ℂ :=
  (d - Complex.I * inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot q)) /
    (1 + inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne))

/-- Multiplying the correction scalar by its positive denominator recovers exactly the boundary
defect of the uncorrected metric-root lift. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar_mul_den
    (q : H) (d : ℂ) :
    thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d *
      (1 + inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne)) =
        d - Complex.I * inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot q) := by
  unfold thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar
  exact div_mul_cancel₀ _ thetaSourceDifferentialBoundaryAugmentedDipoleProjection_den_ne_zero

/-- The explicit normal scalar satisfies the exact boundary correction equation. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar_spec
    (q : H) (d : ℂ) :
    d = Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
      (thetaMetricRoot (q -
        (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d * Complex.I) •
          pinnedOne)) +
        thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d := by
  rw [map_sub, map_smul, inner_sub_right, inner_smul_right]
  have hmul := thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar_mul_den q d
  calc
    d = Complex.I * inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot q) +
        thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d *
          (1 + inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne)) := by
      rw [hmul]
      ring
    _ = Complex.I *
        (inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot q) -
          (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d * Complex.I) *
            inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne)) +
          thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d := by
      ring_nf
      simp only [Complex.I_sq]
      ring

/-- Every metric-root lift has an unconditional exact dipole projection formula.  Projection
changes its primitive only by the explicit finite scalar multiple of `pinnedOne`. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_metricRoot_explicit
    (q : H) (m d : ℂ) :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection
      (thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaMetricRoot q, (m, d))) =
      thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate q m
        (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d) := by
  exact thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_metricRoot q m d
    (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d)
    (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar_spec q d)

/-- A corrected metric-root candidate is a literal source embedding exactly when its primitive
lift and monopole coordinate are supplied by one source vector.  Its dipole coordinate then
follows automatically from the source Riesz law. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate_eq_embedding_of_lift
    (z : ℂ) (q : H) (m c : ℂ) (k : thetaCentered)
    (hsource : thetaCenteredSourceInverse k = q - (c * Complex.I) • pinnedOne)
    (hmonopole : pinnedMean (thetaCenteredSourceInverse k) = m) :
    thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate q m c =
      thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  apply Prod.ext
  · change thetaMetricRoot (q - (c * Complex.I) • pinnedOne) =
      thetaMetricRoot (thetaCenteredSourceInverse k)
    rw [← hsource]
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    apply Prod.ext
    · change m = thetaPinnedMeanCLM (thetaCenteredSourceInverse k)
      rw [thetaPinnedMeanCLM_apply, hmonopole]
    · change Complex.I * inner ℂ (thetaMetricRoot pinnedOne)
          (thetaMetricRoot (q - (c * Complex.I) • pinnedOne)) =
        thetaCenteredDipoleTrace k
      rw [← hsource, thetaCenteredDipoleTrace_eq_thetaMetricRoot_energy]

/-- Exact projected-source regularity reduces to two literal source equations for the explicit
corrected primitive: source-inverse admission and its monopole value. -/
theorem thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_metricRoot_eq_embedding_of_lift
    (z : ℂ) (q : H) (m d : ℂ) (k : thetaCentered)
    (hsource : thetaCenteredSourceInverse k = q -
      (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d * Complex.I) •
        pinnedOne)
    (hmonopole : pinnedMean (thetaCenteredSourceInverse k) = m) :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection
      (thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaMetricRoot q, (m, d))) =
      thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := by
  rw [thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_metricRoot_explicit]
  exact thetaSourceDifferentialBoundaryAugmentedDipoleProjectionCandidate_eq_embedding_of_lift
    z q m (thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar q d) k hsource
    hmonopole

/-- Every repaired differential coordinate has zero pinned mean.  Thus a source lift of a
finite-normal correction has only one remaining scalar compatibility condition. -/
theorem pinnedMean_thetaSourceDifferentialRangeMap (z : ℂ) (k : thetaCentered) :
    pinnedMean (thetaSourceDifferentialRangeMap z k) = 0 := by
  rw [← thetaPinnedMeanCLM_apply, thetaSourceDifferentialRangeMap_apply,
    map_add, map_smul, map_sub, map_smul]
  simp only [thetaPinnedMeanCLM_apply, pinnedMean_pinnedOne]
  rw [(mem_thetaCentered_iff _).mp k.property]
  ring

/-- If the uncorrected primitive has zero pinned mean, the monopole equation of a literal
source lift is equivalent to one explicit finite scalar equation. -/
theorem thetaSourceDifferentialBoundaryAugmentedProjectionLift_monopole_iff
    (q : H) (m c : ℂ) (k : thetaCentered)
    (hmeanq : pinnedMean q = 0)
    (hsource : thetaCenteredSourceInverse k = q - (c * Complex.I) • pinnedOne) :
    pinnedMean (thetaCenteredSourceInverse k) = m ↔ c = Complex.I * m := by
  have hmean : pinnedMean (thetaCenteredSourceInverse k) = -(c * Complex.I) := by
    have h := congrArg thetaPinnedMeanCLM hsource
    rw [map_sub, map_smul, thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply,
      thetaPinnedMeanCLM_apply, hmeanq, pinnedMean_pinnedOne, zero_sub] at h
    simpa [smul_eq_mul] using h
  constructor
  · intro hmonopole
    rw [hmonopole] at hmean
    calc
      c = -c * (Complex.I * Complex.I) := by rw [Complex.I_mul_I]; ring
      _ = (-(c * Complex.I)) * Complex.I := by ring
      _ = Complex.I * (-(c * Complex.I)) := by ring
      _ = Complex.I * m := by rw [← hmean]
  · intro hscalar
    calc
      pinnedMean (thetaCenteredSourceInverse k) = -(c * Complex.I) := hmean
      _ = -((Complex.I * m) * Complex.I) := by rw [hscalar]
      _ = -(m * (Complex.I * Complex.I)) := by ring
      _ = m := by rw [Complex.I_mul_I]; ring

/-- The fundamental symmetry preserves the differential energy coordinate and exchanges the two
finite source ports of a Green readout. -/
theorem thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_readoutCLM_apply
    (z : ℂ) (l : thetaCentered) :
    thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
      (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z l) =
      thetaSourceDifferentialBoundaryAugmentedHilbertPack
        (thetaMetricRoot (thetaSourceDifferentialRangeMap z l),
          ((Complex.I / 2 * z) * thetaCenteredDipoleTrace l,
            (Complex.I / 2 * z) * pinnedMean (thetaCenteredSourceInverse l))) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H thetaMonopoleDipoleHilbert).injective
  change
    (thetaMetricRoot (thetaSourceDifferentialRangeMap z l),
      thetaMonopoleDipoleFundamentalSymmetry
        (thetaMonopoleDipoleHilbertPack
          ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPortSource l))) =
      (thetaMetricRoot (thetaSourceDifferentialRangeMap z l),
        thetaMonopoleDipoleHilbertPack
          ((Complex.I / 2 * z) * thetaCenteredDipoleTrace l,
            (Complex.I / 2 * z) * pinnedMean (thetaCenteredSourceInverse l)))
  apply Prod.ext
  · rfl
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).injective
    change
      (thetaMonopoleDipoleFundamentalSymmetry
        (thetaMonopoleDipoleHilbertPack
          ((Complex.I / 2 * z) • thetaSourceDifferentialBoundaryPortSource l))).ofLp =
        (thetaMonopoleDipoleHilbertPack
          ((Complex.I / 2 * z) * thetaCenteredDipoleTrace l,
            (Complex.I / 2 * z) * pinnedMean (thetaCenteredSourceInverse l))).ofLp
    rw [thetaMonopoleDipoleFundamentalSymmetry_ofLp,
      thetaMonopoleDipoleHilbertPack_ofLp,
      thetaMonopoleDipoleHilbertPack_ofLp]
    simp [thetaSourceDifferentialBoundaryPortSource, thetaPinnedMeanCLM_apply]

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole_coe
    (x : thetaSourceDifferentialBoundaryAugmentedDipoleCarrier) :
    ((thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole x :
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier) :
        thetaSourceDifferentialBoundaryAugmentedHilbert) =
      thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry (x :
        thetaSourceDifferentialBoundaryAugmentedHilbert) := rfl

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM_coe
    (z : ℂ) (k : thetaCentered) :
    ((thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k :
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier) :
        thetaSourceDifferentialBoundaryAugmentedHilbert) =
      thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := rfl

/-- The projected Green readout has exactly the swapped monopole carrier as codomain. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedReadoutMonopoleCLM (z : ℂ) :
  thetaCentered →L[ℂ] thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedMonopoleCarrierProjectCLM.comp
    (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z)

/-- Bounded dipole input map used by the maximal Green transport. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenTransportEmbedding
    (z : ℂ) : thetaCentered →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z

/-- Bounded monopole output map used by the maximal Green transport. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenTransportReadout
    (z : ℂ) : thetaCentered →L[ℂ]
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedReadoutMonopoleCLM z

/-- The dense dipole source embedding remains injective after codomain restriction. -/
theorem thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM_injective (z : ℂ) :
    Function.Injective (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z) := by
  intro k l hkl
  apply thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM_injective z
  exact congrArg Subtype.val hkl

/-- Packaged dense source data for the two-carrier Green transport. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum
    (z : ℂ) : ClosedGraphTransformBetweenDatum
      (H₀ := H)
      (H₁ := thetaSourceDifferentialBoundaryAugmentedDipoleCarrier)
      (H₂ := thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier)
      thetaCentered where
  B := thetaSourceDifferentialBoundaryAugmentedGreenTransportEmbedding z
  J := thetaSourceDifferentialBoundaryAugmentedGreenTransportReadout z
  hB := thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM_injective z
  hDense := thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM_dense z

/-- Literal Green transport from the dipole carrier to the symmetry-swapped monopole carrier.
Its domain is the dense source image; its adjoint is the maximal Hilbert adjoint. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenTransport (z : ℂ) :
    thetaSourceDifferentialBoundaryAugmentedDipoleCarrier →ₗ.[ℂ]
      thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  closedGraphTransformBetweenOfDatum
    (H₀ := H)
    (H₁ := thetaSourceDifferentialBoundaryAugmentedDipoleCarrier)
    (H₂ := thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier)
    thetaCentered
    (thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum z)

/-- Named maximal adjoint of the two-carrier Green transport. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenTransportAdjoint (z : ℂ) :
    thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier →ₗ.[ℂ]
      thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  closedGraphTransformBetweenAdjointOfDatum
    (H₀ := H)
    (H₁ := thetaSourceDifferentialBoundaryAugmentedDipoleCarrier)
    (H₂ := thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier)
    thetaCentered
    (thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum z)

@[simp] theorem thetaSourceDifferentialBoundaryAugmentedGreenTransportAdjoint_eq
    (z : ℂ) :
    thetaSourceDifferentialBoundaryAugmentedGreenTransportAdjoint z =
      closedGraphTransformBetweenAdjointOfDatum
        (H₀ := H)
        (H₁ := thetaSourceDifferentialBoundaryAugmentedDipoleCarrier)
        (H₂ := thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier)
        thetaCentered
        (thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum z) := rfl

/-- The reflected Green kernel gives the bounded-source pairing for the two carrier transport. -/
private theorem thetaSourceDifferentialBoundaryAugmentedGreenTransport_pairing
    (z : ℂ) (l k : thetaCentered) :
    inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedDipoleCarrierProjectCLM
          (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
            (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l)))
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) =
      inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM (starRingEnd ℂ z) l))
        (thetaSourceDifferentialBoundaryAugmentedReadoutMonopoleCLM z k) := by
  calc
    inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedDipoleCarrierProjectCLM
          (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
            (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l)))
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) =
      inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l))
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) := by
      change inner ℂ
          (thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection
            (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
              (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l)))
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) = _
      rw [Submodule.starProjection_apply]
      calc
        inner ℂ
            ↑(thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.orthogonalProjectionOnto
              (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
                (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l)))
            (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k) =
          inner ℂ
            (thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.orthogonalProjectionOnto
              (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
                (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l)))
            (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) := rfl
        _ = inner ℂ
            (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
              (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l))
            (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k) :=
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
            (K := thetaSourceDifferentialBoundaryAugmentedDipoleCarrier)
            (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) _
    _ = inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM (starRingEnd ℂ z) l))
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k) := by
      simpa only [thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM_coe,
        starRingEnd_self_apply] using
        (thetaSourceDifferentialBoundaryAugmentedHilbert_green_conj
          (starRingEnd ℂ z) l k).symm
    _ = inner ℂ
        (thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole
          (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM (starRingEnd ℂ z) l))
        (thetaSourceDifferentialBoundaryAugmentedReadoutMonopoleCLM z k) := by
      change inner ℂ
          (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
            (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM
              (starRingEnd ℂ z) l))
          (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k) =
        inner ℂ
          (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
            (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM
              (starRingEnd ℂ z) l))
          (thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.starProjection
            (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k))
      symm
      rw [Submodule.starProjection_apply]
      calc
        inner ℂ
            (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
              (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM
                (starRingEnd ℂ z) l))
            ↑(thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.orthogonalProjectionOnto
              (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k)) =
          inner ℂ
            (thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole
              (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM
                (starRingEnd ℂ z) l))
            (thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier.orthogonalProjectionOnto
              (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k)) := rfl
        _ = inner ℂ
            (thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole
              (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM
                (starRingEnd ℂ z) l) : thetaSourceDifferentialBoundaryAugmentedHilbert)
            (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k) :=
          Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
            (K := thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier)
            (thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole
              (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM
                (starRingEnd ℂ z) l)) _
        _ = inner ℂ
            (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
              (thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM
                (starRingEnd ℂ z) l))
            (thetaSourceDifferentialBoundaryAugmentedReadoutCLM z k) := rfl

/-- Reflected literal source vector in the monopole carrier for the Green adjoint graph. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceInput
    (z : ℂ) (l : thetaCentered) : thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedDipoleToMonopole
    (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM (starRingEnd ℂ z) l)

/-- Projected reflected Green readout in the dipole carrier for the Green adjoint graph. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput
    (z : ℂ) (l : thetaCentered) : thetaSourceDifferentialBoundaryAugmentedDipoleCarrier :=
  thetaSourceDifferentialBoundaryAugmentedDipoleCarrierProjectCLM
    (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
      (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l))

/-- Explicit finite correction scalar for the reflected Green readout. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar
    (z : ℂ) (l : thetaCentered) : ℂ :=
  thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar
    (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l)
    ((Complex.I / 2 * (starRingEnd ℂ z)) *
      pinnedMean (thetaCenteredSourceInverse l))

/-- Literal primitive that must be admitted by the source inverse for projected reflected
readout regularity. -/
noncomputable def thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive
    (z : ℂ) (l : thetaCentered) : H :=
  thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l -
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l * Complex.I) •
      pinnedOne

/-- Monopole coordinate of the reflected Green readout after the fundamental port exchange. -/
def thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole
    (z : ℂ) (l : thetaCentered) : ℂ :=
  (Complex.I / 2 * (starRingEnd ℂ z)) * thetaCenteredDipoleTrace l

/-- The projected reflected Green output is a literal source embedding whenever its explicit
corrected primitive is a literal source inverse with the exchanged monopole.  This is the exact
source-regularity obligation left by the two-carrier adjoint transport. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_eq_embedding_of_lift
    (z : ℂ) (l k : thetaCentered)
    (hsource : thetaCenteredSourceInverse k =
      thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive z l)
    (hmonopole : pinnedMean (thetaCenteredSourceInverse k) =
      thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole z l) :
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l).1 =
      thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := by
  change thetaSourceDifferentialBoundaryAugmentedDipoleCarrier.starProjection
      (thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry
        (thetaSourceDifferentialBoundaryAugmentedReadoutCLM (starRingEnd ℂ z) l)) = _
  rw [thetaSourceDifferentialBoundaryAugmentedFundamentalSymmetry_readoutCLM_apply]
  unfold thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive
    thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar at hsource
  unfold thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole at hmonopole
  exact thetaSourceDifferentialBoundaryAugmentedDipoleCarrier_starProjection_metricRoot_eq_embedding_of_lift
    z
    (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l)
    ((Complex.I / 2 * (starRingEnd ℂ z)) * thetaCenteredDipoleTrace l)
    ((Complex.I / 2 * (starRingEnd ℂ z)) * pinnedMean (thetaCenteredSourceInverse l))
    k hsource hmonopole

/-- For a reflected Green readout, literal projected-source regularity is reduced to one
source-inverse admission equation and one explicit finite scalar equation. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_eq_embedding_of_source_and_scalar
    (z : ℂ) (l k : thetaCentered)
    (hsource : thetaCenteredSourceInverse k =
      thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive z l)
    (hscalar : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole z l) :
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l).1 =
      thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := by
  apply thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_eq_embedding_of_lift
    z l k hsource
  refine (thetaSourceDifferentialBoundaryAugmentedProjectionLift_monopole_iff
    (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l)
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole z l)
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l) k
    (pinnedMean_thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l) ?_).mpr hscalar
  unfold thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive
    thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar at hsource
  exact hsource

/-- Scalar normal cancellation for one metric-root coordinate. -/
private theorem thetaSourceDifferentialBoundaryAugmented_scalar_cancellation_iff
    (a m p w : ℂ) (hp : 1 + p ≠ 0) :
    (Complex.I / 2 * w * a - Complex.I * m) / (1 + p) = Complex.I * w * a ↔
      m = -((1 / 2 : ℂ) + p) * w * a := by
  constructor
  · intro h
    have hmul := (div_eq_iff hp).mp h
    have hcancel : Complex.I * ((1 / 2 : ℂ) * w * a - m) =
        Complex.I * (w * a * (1 + p)) := by
      calc
        Complex.I * ((1 / 2 : ℂ) * w * a - m) =
            Complex.I / 2 * w * a - Complex.I * m := by ring
        _ = (Complex.I * w * a) * (1 + p) := hmul
        _ = Complex.I * (w * a * (1 + p)) := by ring
    have hminus : (1 / 2 : ℂ) * w * a - m = w * a * (1 + p) :=
      mul_left_cancel₀ Complex.I_ne_zero hcancel
    calc
      m = (1 / 2 : ℂ) * w * a - w * a * (1 + p) := by
        linear_combination -hminus
      _ = -((1 / 2 : ℂ) + p) * w * a := by ring
  · intro h
    apply (div_eq_iff hp).mpr
    calc
      Complex.I / 2 * w * a - Complex.I * m =
          Complex.I * ((1 / 2 : ℂ) * w * a - m) := by ring
      _ = Complex.I * (w * a * (1 + p)) := by rw [h]; ring
      _ = (Complex.I * w * a) * (1 + p) := by ring

/-- After constant-mode cancellation, the exchanged monopole law is exactly one first-moment
residual equation. -/
private theorem thetaSourceDifferentialBoundaryAugmented_scalar_monopole_iff_of_cancellation
    (a b c w : ℂ) (hcancel : c = Complex.I * w * a) :
    c = Complex.I * (Complex.I / 2 * w * b) ↔
      w * (b + 2 * Complex.I * a) = 0 := by
  have hright : Complex.I * (Complex.I / 2 * w * b) = -(1 / 2 : ℂ) * w * b := by
    calc
      Complex.I * (Complex.I / 2 * w * b) =
          (Complex.I * Complex.I) * ((1 / 2 : ℂ) * w * b) := by ring
      _ = -(1 / 2 : ℂ) * w * b := by
        rw [Complex.I_mul_I]
        ring
  constructor
  · intro hscalar
    have hcoef : Complex.I * w * a = -(1 / 2 : ℂ) * w * b := by
      calc
        Complex.I * w * a = c := hcancel.symm
        _ = Complex.I * (Complex.I / 2 * w * b) := hscalar
        _ = -(1 / 2 : ℂ) * w * b := hright
    linear_combination 2 * hcoef
  · intro hresidual
    have hcoef : Complex.I * w * a = -(1 / 2 : ℂ) * w * b := by
      linear_combination hresidual / 2
    calc
      c = Complex.I * w * a := hcancel
      _ = -(1 / 2 : ℂ) * w * b := hcoef
      _ = Complex.I * (Complex.I / 2 * w * b) := hright.symm

/-- On the literal `C_c^∞` derivative core, the only source-inverse obstruction in a
corrected differential coordinate is its coefficient of `pinnedOne`.  Once that coefficient
vanishes, the primitive is the quantile image of the actual smooth compact source
`sourceD g + w • g`. -/
theorem thetaSourceDifferentialRangeMap_sub_smul_pinnedOne_mem_range_of_core
    (w c : ℂ) (l : thetaCentered)
    (hl : l ∈ thetaDerivativeCoreOutput)
    (hc : c = Complex.I * w * pinnedMean (thetaCenteredSourceInverse l)) :
    thetaSourceDifferentialRangeMap w l - (c * Complex.I) • pinnedOne ∈
      thetaCenteredSourceInverse.range := by
  rcases hl with ⟨g, hg, hgs, hl⟩
  let f : SourceSpace thetaSource := (memLp_sourceD hg hgs).toLp (sourceD g)
  let u : SourceSpace thetaSource := (memLp_smooth hg hgs).toLp g
  have hf : f ∈ thetaSmoothSource := by
    refine ⟨sourceD g, (memLp_sourceD hg hgs).coeFn_toLp, ?_, ?_⟩
    · exact hgs.deriv.mul_left
    · change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => -Complex.I * deriv g x)
      exact contDiff_const.mul (contDiff_infty_iff_deriv.mp hg).2
  have hu : u ∈ thetaSmoothSource :=
    ⟨g, (memLp_smooth hg hgs).coeFn_toLp, hgs, hg⟩
  have hfu : f + w • u ∈ thetaSmoothSource :=
    thetaSmoothSourceSubmodule.add_mem hf
      (thetaSmoothSourceSubmodule.smul_mem w hu)
  have hB : thetaCenteredSourceInverse l = quantileUnitary thetaSource u := by
    change thetaCompactSourceInverse (l : H) = quantileUnitary thetaSource u
    rw [hl]
    exact thetaCompactSourceInverse_quantile_sourceD hg hgs
  have hc' : c = Complex.I * w * pinnedMean (quantileUnitary thetaSource u) := by
    rw [hc, hB]
  have hI :
      (Complex.I * w * pinnedMean (quantileUnitary thetaSource u)) * Complex.I =
        -(w * pinnedMean (quantileUnitary thetaSource u)) := by
    calc
      (Complex.I * w * pinnedMean (quantileUnitary thetaSource u)) * Complex.I =
          w * pinnedMean (quantileUnitary thetaSource u) * (Complex.I * Complex.I) := by
        ring
      _ = -(w * pinnedMean (quantileUnitary thetaSource u)) := by
        rw [Complex.I_mul_I]
        ring
  have hEq : thetaSourceDifferentialRangeMap w l - (c * Complex.I) • pinnedOne =
      quantileUnitary thetaSource (f + w • u) := by
    rw [thetaSourceDifferentialRangeMap_apply, hB, hl, hc', map_add, map_smul, hI]
    module
  rw [hEq]
  exact quantile_thetaSmoothSource_mem_range (f + w • u) hfu

/-- The reflected corrected primitive has an actual source lift on the literal core whenever
its finite normal scalar cancels the sole noncompact constant mode. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive_mem_range_of_core
    (z : ℂ) (l : thetaCentered)
    (hl : l ∈ thetaDerivativeCoreOutput)
    (hc : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l)) :
    thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive z l ∈
      thetaCenteredSourceInverse.range := by
  unfold thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive
  exact thetaSourceDifferentialRangeMap_sub_smul_pinnedOne_mem_range_of_core
    (starRingEnd ℂ z)
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l)
    l hl hc

/-- On the literal core, cancellation of the finite constant mode and the finite monopole law
together give the projected reflected Green output as a literal source embedding. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_exists_of_core
    (z : ℂ) (l : thetaCentered)
    (hl : l ∈ thetaDerivativeCoreOutput)
    (hcancel : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l))
    (hscalar : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole z l) :
    ∃ k : thetaCentered,
      (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l).1 =
        thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := by
  rcases thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectedPrimitive_mem_range_of_core
      z l hl hcancel with ⟨k, hk⟩
  refine ⟨k, thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_eq_embedding_of_source_and_scalar
    z l k hk hscalar⟩

/-- Constant-mode cancellation of the reflected finite correction is equivalent to one exact
metric-boundary residual. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar_eq_cancellation_iff
    (z : ℂ) (l : thetaCentered) :
    thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
        Complex.I * (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l) ↔
      inner ℂ (thetaMetricRoot pinnedOne)
          (thetaMetricRoot (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l)) =
        -((1 / 2 : ℂ) +
          inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne)) *
          (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l) := by
  unfold thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar
    thetaSourceDifferentialBoundaryAugmentedDipoleProjectionScalar
  exact thetaSourceDifferentialBoundaryAugmented_scalar_cancellation_iff _ _ _ _
    thetaSourceDifferentialBoundaryAugmentedDipoleProjection_den_ne_zero

/-- Given constant-mode cancellation, the exchanged monopole equality is equivalent to the
single source dipole--mean residual. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar_eq_monopole_iff_of_cancellation
    (z : ℂ) (l : thetaCentered)
    (hcancel : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l)) :
    thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
        Complex.I * thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole z l ↔
      (starRingEnd ℂ z) *
        (thetaCenteredDipoleTrace l + 2 * Complex.I *
          pinnedMean (thetaCenteredSourceInverse l)) = 0 := by
  unfold thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole
  exact thetaSourceDifferentialBoundaryAugmented_scalar_monopole_iff_of_cancellation _ _ _ _
    hcancel

/-- For a literal core input, the metric-boundary residual and the source dipole--mean residual
are sufficient for a projected reflected Green output to be an actual source embedding. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_exists_of_core_of_residuals
    (z : ℂ) (l : thetaCentered)
    (hl : l ∈ thetaDerivativeCoreOutput)
    (hmetric :
      inner ℂ (thetaMetricRoot pinnedOne)
          (thetaMetricRoot (thetaSourceDifferentialRangeMap (starRingEnd ℂ z) l)) =
        -((1 / 2 : ℂ) +
          inner ℂ (thetaMetricRoot pinnedOne) (thetaMetricRoot pinnedOne)) *
          (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l))
    (hmoment : (starRingEnd ℂ z) *
        (thetaCenteredDipoleTrace l + 2 * Complex.I *
          pinnedMean (thetaCenteredSourceInverse l)) = 0) :
    ∃ k : thetaCentered,
      (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l).1 =
        thetaSourceDifferentialBoundaryAugmentedEmbeddingCLM z k := by
  have hcancel : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * (starRingEnd ℂ z) * pinnedMean (thetaCenteredSourceInverse l) :=
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar_eq_cancellation_iff
      z l).mpr hmetric
  have hscalar : thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar z l =
      Complex.I * thetaSourceDifferentialBoundaryAugmentedGreenAdjointMonopole z l :=
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointCorrectionScalar_eq_monopole_iff_of_cancellation
      z l hcancel).mpr hmoment
  exact thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput_exists_of_core
    z l hl hcancel hscalar

private theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSource_pairing
    (z : ℂ) (l k : thetaCentered) :
    inner ℂ (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l)
        (thetaSourceDifferentialBoundaryAugmentedEmbeddingDipoleCLM z k) =
      inner ℂ (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceInput z l)
        (thetaSourceDifferentialBoundaryAugmentedReadoutMonopoleCLM z k) :=
  thetaSourceDifferentialBoundaryAugmentedGreenTransport_pairing z l k

private theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSource_transport_pairing
    (z : ℂ) (l k : thetaCentered) :
    inner ℂ (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l)
        (thetaSourceDifferentialBoundaryAugmentedGreenTransportEmbedding z k) =
      inner ℂ (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceInput z l)
        (thetaSourceDifferentialBoundaryAugmentedGreenTransportReadout z k) :=
  thetaSourceDifferentialBoundaryAugmentedGreenAdjointSource_pairing z l k

private theorem thetaSourceDifferentialBoundaryAugmentedGreenAdjointSource_datum_pairing
    (z : ℂ) (l k : thetaCentered) :
    inner ℂ (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l)
        ((thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum z).B k) =
      inner ℂ (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceInput z l)
        ((thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum z).J k) :=
  thetaSourceDifferentialBoundaryAugmentedGreenAdjointSource_transport_pairing z l k

set_option maxHeartbeats 400000 in
/-- The exact Green law puts the reflected source pair in the maximal-adjoint graph.
The first coordinate is the swapped literal source; the second is the dipole projection of the
reflected readout. -/
theorem thetaSourceDifferentialBoundaryAugmentedGreenTransport_adjoint_source_graph
    (z : ℂ) (l : thetaCentered) :
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceInput z l,
      thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l) ∈
        (thetaSourceDifferentialBoundaryAugmentedGreenTransportAdjoint z).graph := by
  rw [thetaSourceDifferentialBoundaryAugmentedGreenTransportAdjoint_eq]
  exact ClosedGraphTransformBetweenDatum.mem_adjoint_graph_of_pairing
    (H₀ := H)
    (H₁ := thetaSourceDifferentialBoundaryAugmentedDipoleCarrier)
    (H₂ := thetaSourceDifferentialBoundaryAugmentedMonopoleCarrier)
    thetaCentered
    (thetaSourceDifferentialBoundaryAugmentedGreenTransportDatum z)
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceOutput z l)
    (thetaSourceDifferentialBoundaryAugmentedGreenAdjointSourceInput z l)
    (fun k => thetaSourceDifferentialBoundaryAugmentedGreenAdjointSource_datum_pairing z l k)

/-! ## Literal conjugation and reflected source fibres -/

/-- Pointwise conjugation on the quantile `L²` carrier. -/
def thetaLpConj (f : H) : H :=
  ((Lp.memLp f).mono
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun _ => by simp)).toLp
      (fun t => (starRingEnd ℂ) ((f : ℝ → ℂ) t))

theorem thetaLpConj_coeFn_ae (f : H) :
    ⇑(thetaLpConj f) =ᵐ[unitIntervalMeasure]
      fun t => (starRingEnd ℂ) ((f : ℝ → ℂ) t) :=
  ((Lp.memLp f).mono
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun _ => by simp)).coeFn_toLp

theorem thetaLpConj_add (f g : H) :
    thetaLpConj (f + g) = thetaLpConj f + thetaLpConj g := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (f + g), thetaLpConj_coeFn_ae f,
    thetaLpConj_coeFn_ae g, Lp.coeFn_add f g, Lp.coeFn_add (thetaLpConj f) (thetaLpConj g)]
      with t hfg hf hg hadd hout
  rw [hfg, hout, hadd]
  simp only [Pi.add_apply]
  rw [hf, hg]
  simp

theorem thetaLpConj_smul (c : ℂ) (f : H) :
    thetaLpConj (c • f) = (starRingEnd ℂ c) • thetaLpConj f := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (c • f), thetaLpConj_coeFn_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul (starRingEnd ℂ c) (thetaLpConj f)]
      with t hcf hf hin hout
  rw [hcf, hout, hin]
  simp only [Pi.smul_apply]
  rw [hf]
  simp [smul_eq_mul]

theorem thetaLpConj_involutive (f : H) : thetaLpConj (thetaLpConj f) = f := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (thetaLpConj f), thetaLpConj_coeFn_ae f]
      with t houter hinner
  rw [houter, hinner]
  simp

theorem thetaLpConj_zero : thetaLpConj (0 : H) = 0 := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (0 : H), Lp.coeFn_zero ℂ (2 : ENNReal)
    unitIntervalMeasure] with t hconj hzero
  rw [hconj, hzero]
  simp

theorem thetaLpConj_injective : Function.Injective thetaLpConj := by
  intro f g hfg
  have h := congrArg thetaLpConj hfg
  rw [thetaLpConj_involutive, thetaLpConj_involutive] at h
  exact h

/-- Pointwise conjugation is antiunitary for the literal `L²` inner product.  This is the
positive ingredient needed to turn the real reflection into a doubled Hodge star. -/
theorem inner_thetaLpConj (f g : H) :
    inner ℂ (thetaLpConj f) (thetaLpConj g) =
      (starRingEnd ℂ) (inner ℂ f g) := by
  rw [MeasureTheory.L2.inner_def]
  change (∫ t : ℝ, inner ℂ ((thetaLpConj f : H) t) ((thetaLpConj g : H) t)
      ∂unitIntervalMeasure) =
    (starRingEnd ℂ) (∫ t : ℝ, inner ℂ ((f : H) t) ((g : H) t) ∂unitIntervalMeasure)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [thetaLpConj_coeFn_ae f, thetaLpConj_coeFn_ae g] with t hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_self_apply]

/-- The literal positive theta metric is real, hence commutes with pointwise conjugation. -/
theorem thetaMetricOperator_thetaLpConj (f : H) :
    thetaMetricOperator (thetaLpConj f) = thetaLpConj (thetaMetricOperator f) := by
  apply Lp.ext
  filter_upwards
      [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le (thetaLpConj f),
       thetaLpConj_coeFn_ae (thetaMetricOperator f),
       metricOperator_coeFn thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le f,
       thetaLpConj_coeFn_ae f] with t hleft hright hmetric hconj
  change
    ((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
      (thetaLpConj f) : H) t =
      (thetaLpConj
        ((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
          f) : H) t
  change
    (thetaLpConj
      ((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
        f) : H) t =
      (starRingEnd ℂ)
        (((metricOperator thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le)
          f : H) t) at hright
  rw [hleft, hright, hmetric, hconj, map_mul, starRingEnd_metricSymbol]

/-- Doubling the literal real reflection gives an anti-linear almost-complex source action.
Unlike pointwise conjugation itself, its square is `-1`. -/
def thetaDoubledHodge (u : H × H) : H × H :=
  (-thetaLpConj u.2, thetaLpConj u.1)

theorem thetaDoubledHodge_add (u v : H × H) :
    thetaDoubledHodge (u + v) = thetaDoubledHodge u + thetaDoubledHodge v := by
  ext <;> simp [thetaDoubledHodge, thetaLpConj_add, add_comm]

theorem thetaDoubledHodge_smul (c : ℂ) (u : H × H) :
    thetaDoubledHodge (c • u) = (starRingEnd ℂ c) • thetaDoubledHodge u := by
  ext <;> simp [thetaDoubledHodge, thetaLpConj_smul]

def thetaDoubledHodgeSLM :
    (H × H) →ₛₗ[starRingEnd ℂ] (H × H) where
  toFun := thetaDoubledHodge
  map_add' := thetaDoubledHodge_add
  map_smul' := thetaDoubledHodge_smul

theorem thetaDoubledHodge_sq (u : H × H) :
    thetaDoubledHodge (thetaDoubledHodge u) = -u := by
  have hneg (f : H) : thetaLpConj (-f) = -thetaLpConj f := by
    simpa using thetaLpConj_smul (-1 : ℂ) f
  ext <;> simp [thetaDoubledHodge, hneg, thetaLpConj_involutive]

/-- The bilinear cup candidate induced by source conjugation on the doubled carrier. -/
def thetaDoubledCup (u v : H × H) : ℂ :=
  inner ℂ (thetaLpConj u.1) v.2 - inner ℂ (thetaLpConj u.2) v.1

/-- Evaluating the doubled cup form against the doubled Hodge star is the sum of two literal
Hilbert energies. -/
theorem thetaDoubledCup_hodge (u : H × H) :
    thetaDoubledCup u (thetaDoubledHodge u) =
      inner ℂ (thetaLpConj u.1) (thetaLpConj u.1) +
        inner ℂ (thetaLpConj u.2) (thetaLpConj u.2) := by
  simp only [thetaDoubledCup, thetaDoubledHodge, inner_neg_right, sub_neg_eq_add]

/-- The source-plus-boundary carrier combines the doubled literal source with its exact
monopole--dipole Green completion. -/
def thetaSourceGreenHodge (r : (H × H) × (ℂ × ℂ)) : (H × H) × (ℂ × ℂ) :=
  (thetaDoubledHodge r.1, thetaMonopoleDipoleHodge r.2)

theorem thetaSourceGreenHodge_add (r s : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenHodge (r + s) = thetaSourceGreenHodge r + thetaSourceGreenHodge s := by
  ext <;> simp [thetaSourceGreenHodge, thetaDoubledHodge_add,
    thetaMonopoleDipoleHodge_add]

theorem thetaSourceGreenHodge_smul (c : ℂ) (r : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenHodge (c • r) =
      (starRingEnd ℂ c) • thetaSourceGreenHodge r := by
  ext <;> simp [thetaSourceGreenHodge, thetaDoubledHodge_smul,
    thetaMonopoleDipoleHodge_smul]

/-- The completed source Hodge star is conjugate-semilinear. -/
def thetaSourceGreenHodgeSLM :
    ((H × H) × (ℂ × ℂ)) →ₛₗ[starRingEnd ℂ] ((H × H) × (ℂ × ℂ)) where
  toFun := thetaSourceGreenHodge
  map_add' := thetaSourceGreenHodge_add
  map_smul' := thetaSourceGreenHodge_smul

/-- The source-plus-boundary Hodge star has square `-1`. -/
theorem thetaSourceGreenHodge_sq (r : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenHodge (thetaSourceGreenHodge r) = -r := by
  ext <;> simp [thetaSourceGreenHodge, thetaDoubledHodge_sq,
    thetaMonopoleDipoleHodge_sq]

/-- Bilinear cup form on the completed source carrier. -/
def thetaSourceGreenCup (r s : (H × H) × (ℂ × ℂ)) : ℂ :=
  thetaDoubledCup r.1 s.1 + thetaMonopoleDipoleCup r.2 s.2

/-- The completed source cup has the explicit positive Hodge diagonal. -/
theorem thetaSourceGreenCup_hodge (r : (H × H) × (ℂ × ℂ)) :
    thetaSourceGreenCup r (thetaSourceGreenHodge r) =
      inner ℂ (thetaLpConj r.1.1) (thetaLpConj r.1.1) +
        inner ℂ (thetaLpConj r.1.2) (thetaLpConj r.1.2) +
          (Complex.normSq r.2.1 : ℂ) + (Complex.normSq r.2.2 : ℂ) := by
  rw [thetaSourceGreenCup, thetaSourceGreenHodge,
    thetaDoubledCup_hodge, thetaMonopoleDipoleCup_hodge]
  ring

theorem pinnedMean_thetaLpConj (f : H) :
    pinnedMean (thetaLpConj f) = (starRingEnd ℂ) (pinnedMean f) := by
  symm
  rw [pinnedMean, ← integral_conj]
  apply integral_congr_ae
  exact (thetaLpConj_coeFn_ae f).symm

theorem pinnedPrefix_thetaLpConj (f : H) (t : ℝ) :
    pinnedPrefix (thetaLpConj f) t = (starRingEnd ℂ) (pinnedPrefix f t) := by
  symm
  rw [pinnedPrefix, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [thetaLpConj_coeFn_ae f] with u hu
  simp only [indicator_apply]
  split_ifs <;> simp [hu]

theorem pinnedVolterraFun_thetaLpConj (f : H) (t : ℝ) :
    pinnedVolterraFun (thetaLpConj f) t =
      (starRingEnd ℂ) (pinnedVolterraFun f t) := by
  change pinnedPrefix (thetaLpConj f) t - (t : ℂ) * pinnedMean (thetaLpConj f) =
    (starRingEnd ℂ) (pinnedPrefix f t - (t : ℂ) * pinnedMean f)
  rw [pinnedPrefix_thetaLpConj, pinnedMean_thetaLpConj]
  simp only [map_sub, map_mul, Complex.conj_ofReal]

/-- The literal theta source inverse anticommutes with pointwise conjugation.  The sign comes
from its intrinsic imaginary kernel factor, and is what realizes reflection across the critical
axis. -/
theorem thetaCompactSourceInverse_thetaLpConj (f : H) :
    thetaLpConj (thetaCompactSourceInverse f) =
      -thetaCompactSourceInverse (thetaLpConj f) := by
  have hBf : (thetaCompactSourceInverse f : H) =ᵐ[unitIntervalMeasure]
      fun t => pinnedKernelField thetaSource t f := by
    simpa [thetaCompactSourceInverse] using
      (pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f)
  have hBCf : (thetaCompactSourceInverse (thetaLpConj f) : H) =ᵐ[unitIntervalMeasure]
      fun t => pinnedKernelField thetaSource t (thetaLpConj f) := by
    simpa [thetaCompactSourceInverse] using
      (pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource (thetaLpConj f))
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae (thetaCompactSourceInverse f),
    Lp.coeFn_neg (thetaCompactSourceInverse (thetaLpConj f)), hBf, hBCf]
      with t hconj hneg hBf hBCf
  rw [hconj, hneg, hBf]
  simp only [Pi.neg_apply]
  rw [hBCf, pinnedKernelField_apply_eq_pinnedVolterraFun,
    pinnedKernelField_apply_eq_pinnedVolterraFun,
    pinnedVolterraFun_thetaLpConj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem thetaLpConj_neg (f : H) : thetaLpConj (-f) = -thetaLpConj f := by
  simpa using thetaLpConj_smul (-1 : ℂ) f

/-- The metric-conjugate bilinear pairing carried by the literal theta source. -/
def thetaMetricConjBilinear (f g : H) : ℂ :=
  inner ℂ (thetaMetricOperator (thetaLpConj f)) g

/-- The source flow fails to preserve the metric-conjugate pairing by exactly the rank-two
Green boundary form.  The sign is fixed by conjugate-linearity in the first Hilbert argument. -/
theorem thetaMetricConjBilinear_thetaKernel_defect (f g : H) :
    thetaMetricConjBilinear (thetaKernelOperator f) g +
        thetaMetricConjBilinear f (thetaKernelOperator g) =
      Complex.I * inner ℂ (pinnedBoundaryCLM (thetaLpConj f)) g := by
  have hgreen := congrArg (fun T : H →L[ℂ] H =>
      (inner ℂ (T (thetaLpConj f)) g : ℂ))
    thetaMetric_commutator_thetaKernelOperator
  have hsub :
      (thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator)
          (thetaLpConj f) =
        (thetaMetricOperator * thetaKernelOperator) (thetaLpConj f) -
          (ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator)
            (thetaLpConj f) := by
    change
      ((↑(thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator) : H →ₗ[ℂ] H)
        (thetaLpConj f)) = _
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rfl
  rw [hsub, mul_apply_eq_comp, mul_apply_eq_comp, inner_sub_left,
    smul_apply, inner_smul_left, ContinuousLinearMap.adjoint_inner_left] at hgreen
  have hconjI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  rw [hconjI] at hgreen
  have hsourceConj : thetaLpConj (thetaKernelOperator f) =
      -thetaKernelOperator (thetaLpConj f) := by
    simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse] using
      thetaCompactSourceInverse_thetaLpConj f
  unfold thetaMetricConjBilinear
  rw [hsourceConj, map_neg, inner_neg_left]
  linear_combination -hgreen

/-- In the exact port coordinates, the metric-conjugate Green defect is incoming intensity
minus outgoing intensity. -/
theorem thetaMetricConjBilinear_thetaKernel_twoPort (f g : H) :
    thetaMetricConjBilinear (thetaKernelOperator f) g +
        thetaMetricConjBilinear f (thetaKernelOperator g) =
      Complex.I * ((starRingEnd ℂ) (pinnedBoundaryInPort (thetaLpConj f)) *
          pinnedBoundaryInPort g -
        (starRingEnd ℂ) (pinnedBoundaryOutPort (thetaLpConj f)) *
          pinnedBoundaryOutPort g) := by
  rw [thetaMetricConjBilinear_thetaKernel_defect,
    inner_pinnedBoundaryCLM_eq_twoPort_pair]

theorem thetaLpConj_sub (f g : H) :
    thetaLpConj (f - g) = thetaLpConj f - thetaLpConj g := by
  rw [sub_eq_add_neg, thetaLpConj_add, thetaLpConj_neg, sub_eq_add_neg]

theorem thetaLpConj_pinnedOne : thetaLpConj pinnedOne = pinnedOne := by
  apply Lp.ext
  filter_upwards [thetaLpConj_coeFn_ae pinnedOne, pinnedOne_coeFn] with t hconj hone
  rw [hconj, hone]
  simp

/-- Conjugation restricts to the literal mean-zero source coordinate. -/
def thetaCenteredConj (k : thetaCentered) : thetaCentered :=
  ⟨thetaLpConj k, (mem_thetaCentered_iff _).mpr (by
    rw [pinnedMean_thetaLpConj, (mem_thetaCentered_iff _).mp k.property]
    simp)⟩

theorem thetaCenteredConj_coe (k : thetaCentered) :
    (thetaCenteredConj k : H) = thetaLpConj k := rfl

theorem thetaCenteredConj_involutive (k : thetaCentered) :
    thetaCenteredConj (thetaCenteredConj k) = k := by
  apply Subtype.ext
  exact thetaLpConj_involutive k

theorem thetaCenteredSourceInverse_thetaCenteredConj (k : thetaCentered) :
    thetaCenteredSourceInverse (thetaCenteredConj k) =
      -thetaLpConj (thetaCenteredSourceInverse k) := by
  have h := congrArg Neg.neg (thetaCompactSourceInverse_thetaLpConj (k : H))
  simpa [thetaCenteredSourceInverse, thetaCenteredConj] using h.symm

theorem pinnedMean_neg (f : H) : pinnedMean (-f) = -pinnedMean f := by
  simpa using pinnedMean_smul (-1 : ℂ) f

/-- The literal closed differential coordinate is equivariant for the critical-axis reflection
`z ↦ -conj z`. -/
theorem thetaSourceDifferentialRangeMap_thetaCenteredConj (z : ℂ) (k : thetaCentered) :
    thetaLpConj (thetaSourceDifferentialRangeMap z k) =
      thetaSourceDifferentialRangeMap (-(starRingEnd ℂ z)) (thetaCenteredConj k) := by
  rw [thetaSourceDifferentialRangeMap_apply, thetaLpConj_add, thetaLpConj_smul,
    thetaLpConj_sub, thetaLpConj_smul, thetaLpConj_pinnedOne,
    thetaSourceDifferentialRangeMap_apply, thetaCenteredConj_coe,
    thetaCenteredSourceInverse_thetaCenteredConj, pinnedMean_neg,
    pinnedMean_thetaLpConj]
  module

theorem pinnedFirstMoment_thetaLpConj (f : H) :
    pinnedFirstMoment (thetaLpConj f) = (starRingEnd ℂ) (pinnedFirstMoment f) := by
  symm
  rw [pinnedFirstMoment, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [thetaLpConj_coeFn_ae f] with t ht
  rw [map_mul, Complex.conj_ofReal, ht]

/-- The second scalar port is also real-coordinate conjugation covariant. -/
theorem thetaCenteredDipoleTrace_thetaCenteredConj (k : thetaCentered) :
    thetaCenteredDipoleTrace (thetaCenteredConj k) =
      (starRingEnd ℂ) (thetaCenteredDipoleTrace k) := by
  rw [thetaCenteredDipoleTrace_apply, thetaCenteredDipoleTrace_apply,
    thetaCenteredConj_coe]
  exact pinnedFirstMoment_thetaLpConj (k : H)

/-- The antilinear action on the full literal source and boundary record.  The two leading minus
signs are forced by the imaginary source kernel; the boundary signs are then fixed by the same
source action. -/
def thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))) :
    ((H × H) × (ℂ × ℂ)) :=
  ((-thetaLpConj r.1.1, thetaLpConj r.1.2),
    (-(starRingEnd ℂ r.2.1), starRingEnd ℂ r.2.2))

/-- The source/differential exchange on a complete boundary record. -/
def thetaSourceDifferentialBoundarySwap (r : ((H × H) × (ℂ × ℂ))) :
    ((H × H) × (ℂ × ℂ)) :=
  ((r.1.2, r.1.1), (r.2.2, r.2.1))

/-- The completed Hodge star is exactly literal record reflection after exchanging source and
differential legs.  Hence the unresolved Hodge-flow law is precisely a closed adjoint-swap
transport problem for the source relation. -/
theorem thetaSourceGreenHodge_eq_boundaryConj_swap (r : ((H × H) × (ℂ × ℂ))) :
    thetaSourceGreenHodge r =
      thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundarySwap r) := by
  rfl

/-- The explicit boundary action maps every literal source coordinate at `z` to the coordinate
at the critical-axis reflection `-conj z`. -/
theorem thetaSourceDifferentialBoundaryConj_coordinate (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundaryCoordinate z k) =
      thetaSourceDifferentialBoundaryCoordinate (-(starRingEnd ℂ z)) (thetaCenteredConj k) := by
  rw [thetaSourceDifferentialBoundaryCoordinate_apply,
    thetaSourceDifferentialBoundaryCoordinate_apply]
  simp only [thetaSourceDifferentialBoundaryConj]
  rw [thetaCenteredSourceInverse_thetaCenteredConj,
    thetaSourceDifferentialRangeMap_thetaCenteredConj,
    pinnedMean_neg, pinnedMean_thetaLpConj,
    thetaCenteredDipoleTrace_thetaCenteredConj]

theorem thetaSourceDifferentialBoundaryConj_add (r s : ((H × H) × (ℂ × ℂ))) :
    thetaSourceDifferentialBoundaryConj (r + s) =
      thetaSourceDifferentialBoundaryConj r + thetaSourceDifferentialBoundaryConj s := by
  ext <;> simp [thetaSourceDifferentialBoundaryConj, thetaLpConj_add, add_comm]

theorem thetaSourceDifferentialBoundaryConj_smul (c : ℂ) (r : ((H × H) × (ℂ × ℂ))) :
    thetaSourceDifferentialBoundaryConj (c • r) =
      (starRingEnd ℂ c) • thetaSourceDifferentialBoundaryConj r := by
  ext <;> simp [thetaSourceDifferentialBoundaryConj, thetaLpConj_smul]

theorem thetaSourceDifferentialBoundaryConj_involutive (r : ((H × H) × (ℂ × ℂ))) :
    thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundaryConj r) = r := by
  ext <;> simp [thetaSourceDifferentialBoundaryConj, thetaLpConj_neg,
    thetaLpConj_involutive]

/-- The complete record reflection as a conjugate-semilinear map. -/
def thetaSourceDifferentialBoundaryConjSLM :
    ((H × H) × (ℂ × ℂ)) →ₛₗ[starRingEnd ℂ] ((H × H) × (ℂ × ℂ)) where
  toFun := thetaSourceDifferentialBoundaryConj
  map_add' := thetaSourceDifferentialBoundaryConj_add
  map_smul' := thetaSourceDifferentialBoundaryConj_smul

theorem thetaSourceDifferentialBoundaryConj_mem
    (z : ℂ) (r : thetaSourceDifferentialBoundaryRelation z) :
    thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))) ∈
      thetaSourceDifferentialBoundaryRelation (-(starRingEnd ℂ z)) := by
  obtain ⟨k, hk⟩ :=
    (thetaSourceDifferentialBoundaryRelation_mem_iff z
      (r : ((H × H) × (ℂ × ℂ)))).mp r.property
  refine (thetaSourceDifferentialBoundaryRelation_mem_iff (-(starRingEnd ℂ z))
    (thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))))).mpr ?_
  refine ⟨thetaCenteredConj k, ?_⟩
  calc
    thetaSourceDifferentialBoundaryCoordinate (-(starRingEnd ℂ z)) (thetaCenteredConj k) =
        thetaSourceDifferentialBoundaryConj (thetaSourceDifferentialBoundaryCoordinate z k) :=
      (thetaSourceDifferentialBoundaryConj_coordinate z k).symm
    _ = thetaSourceDifferentialBoundaryConj (r : ((H × H) × (ℂ × ℂ))) := by rw [hk]

/-- Closed source-relation reflection induced by the literal theta kernel. -/
def thetaSourceDifferentialBoundaryRelationConj (z : ℂ) :
    thetaSourceDifferentialBoundaryRelation z →ₛₗ[starRingEnd ℂ]
      thetaSourceDifferentialBoundaryRelation (-(starRingEnd ℂ z)) where
  toFun r := ⟨thetaSourceDifferentialBoundaryConj r,
    thetaSourceDifferentialBoundaryConj_mem z r⟩
  map_add' r s := by
    apply Subtype.ext
    exact thetaSourceDifferentialBoundaryConj_add r s
  map_smul' c r := by
    apply Subtype.ext
    exact thetaSourceDifferentialBoundaryConj_smul c r

theorem thetaSourceDifferentialBoundaryRelationConj_coordinate
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryRelationConj z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
        thetaSourceDifferentialBoundaryCoordinateElement (-(starRingEnd ℂ z))
          (thetaCenteredConj k) := by
  apply Subtype.ext
  exact thetaSourceDifferentialBoundaryConj_coordinate z k

/-- Reflection carries every nonzero vertical fibre of the literal closed relation to a nonzero
vertical fibre at the reflected parameter. -/
theorem thetaSourceDifferentialBoundaryRelation_nonzero_vertical_reflect
    (z : ℂ) :
    (∃ r : ((H × H) × (ℂ × ℂ)), r ∈ thetaSourceDifferentialBoundaryRelation z ∧
      r.1.2 = 0 ∧ r.1.1 ≠ 0) →
      ∃ s : ((H × H) × (ℂ × ℂ)),
        s ∈ thetaSourceDifferentialBoundaryRelation (-(starRingEnd ℂ z)) ∧
          s.1.2 = 0 ∧ s.1.1 ≠ 0 := by
  rintro ⟨r, hr, hrange, hsource⟩
  refine ⟨thetaSourceDifferentialBoundaryConj r,
    thetaSourceDifferentialBoundaryConj_mem z ⟨r, hr⟩, ?_, ?_⟩
  · change thetaLpConj r.1.2 = 0
    rw [hrange, thetaLpConj_zero]
  · change -thetaLpConj r.1.1 ≠ 0
    intro hzero
    apply hsource
    apply thetaLpConj_injective
    have hc : thetaLpConj r.1.1 = 0 := neg_eq_zero.mp hzero
    rw [hc, thetaLpConj_zero]

/-- Source-faithful conjugation proves the expected reality reflection of the completed Xi zero
set directly through its literal closed relation. -/
theorem XiC_eq_zero_reflect_of_XiC_eq_zero {z : ℂ} (hz : XiC z = 0) :
    XiC (-(starRingEnd ℂ z)) = 0 := by
  apply (XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical
    (-(starRingEnd ℂ z))).mpr
  apply thetaSourceDifferentialBoundaryRelation_nonzero_vertical_reflect z
  exact (XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical z).mp hz

/-- The reflected boundary action reverses the hyperbolic signature.  Hence a completion that
extends this literal action cannot treat the action as an ordinary Pontryagin isometry. -/
theorem thetaMonopoleDipoleHyperbolicForm_boundaryConj
    (u v : ℂ × ℂ) :
    thetaMonopoleDipoleHyperbolicForm
      (-(starRingEnd ℂ u.1), starRingEnd ℂ u.2)
      (-(starRingEnd ℂ v.1), starRingEnd ℂ v.2) =
      -(starRingEnd ℂ) (thetaMonopoleDipoleHyperbolicForm u v) := by
  simp only [thetaMonopoleDipoleHyperbolicForm, map_neg, map_add, map_mul,
    starRingEnd_self_apply]
  ring

end

end RHTower.HedenmalmThetaSource
