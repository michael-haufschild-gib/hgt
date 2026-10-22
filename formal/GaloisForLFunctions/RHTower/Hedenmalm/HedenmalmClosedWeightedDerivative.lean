import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactDivisorEigenmode
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmFredholmRangeDivisor
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmWeightedAdjointCore
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Closed weighted Hedenmalm derivative

This file constructs the closure of `-i d/dx` on compactly supported smooth vectors in
`H_k = L²(ℝ,k⁻¹ dx)`.  We work in the canonically unitarily equivalent quantile space
`L²(0,1)`.  The compact source inverse, restricted to the mean-zero hyperplane, is injective and
has dense range; its graph inverse is therefore the required closed derivative.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource

private abbrev H := Lp ℂ 2 unitIntervalMeasure

private abbrev HS := SourceSpace thetaSource

private abbrev sourceMeasure : Measure ℝ :=
  volume.withDensity (realDensity (sourceWeight thetaSource))

local instance hedenmalmClosedWeightedDerivativeLocalInst1 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

private theorem continuous_sourceWeight : Continuous (sourceWeight thetaSource) := by
  apply thetaSource.continuous_k.inv₀
  intro x
  exact (thetaSource.pos_k x).ne'

local instance hedenmalmClosedWeightedDerivativeLocalInst2 : IsFiniteMeasureOnCompacts sourceMeasure where
  lt_top_of_isCompact := by
    intro K hK
    rw [sourceMeasure, withDensity_apply' (realDensity (sourceWeight thetaSource)) K]
    obtain ⟨C, hC⟩ :=
      hK.exists_bound_of_continuousOn continuous_sourceWeight.continuousOn
    calc
      (∫⁻ x in K, realDensity (sourceWeight thetaSource) x ∂volume)
          ≤ ∫⁻ _x in K, ENNReal.ofReal C ∂volume := by
            apply setLIntegral_mono measurable_const
            intro x hx
            exact ENNReal.ofReal_le_ofReal (by
              simpa [Real.norm_eq_abs, abs_of_pos (sourceWeight_pos thetaSource x)]
                using hC x hx)
      _ = ENNReal.ofReal C * volume K := setLIntegral_const K _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- Mean-zero hyperplane in the quantile realization of `H_k`. -/
def thetaCentered : Submodule ℂ H := (ℂ ∙ pinnedOne)ᗮ

theorem mem_thetaCentered_iff (f : H) :
    f ∈ thetaCentered ↔ pinnedMean f = 0 := by
  rw [thetaCentered, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinner : inner ℂ pinnedOne f = pinnedMean f := by
    rw [inner_lp_eq, pinnedMean]
    apply integral_congr_ae
    filter_upwards [pinnedOne_coeFn] with t ht
    rw [ht]
    simp
  rw [hinner]

/-- The compact source inverse restricted to the mean-zero hyperplane. -/
def thetaCenteredSourceInverse : thetaCentered →L[ℂ] H :=
  thetaCompactSourceInverse.comp thetaCentered.subtypeL

theorem pinnedVolterra_eq_zero_of_kernelOperator_eq_zero
    {f : H} (hf : thetaCompactSourceInverse f = 0) :
    pinnedVolterra f = 0 := by
  apply Lp.ext
  have hzero : ((0 : H) : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun _ => 0 :=
    Lp.coeFn_zero ℂ (2 : ENNReal) unitIntervalMeasure
  have hBzero : ((thetaCompactSourceInverse f : H) : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure] fun _ => 0 := by
    rw [hf]
    exact hzero
  filter_upwards
      [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f,
        hBzero, pinnedVolterra_coeFn f,
        ae_unitIntervalMeasure_mem_Ioo, hzero]
    with t hB hBzero hC ht h0
  change ((thetaCompactSourceInverse f : H) : ℝ → ℂ) t = _ at hB
  change (pinnedVolterra f : ℝ → ℂ) t = (0 : H) t
  rw [hC, h0]
  have hq : ((quantileSpeed thetaSource t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (quantileSpeed_pos thetaSource t).ne'
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  rw [hBzero] at hB
  rw [pinnedKernelField_apply_eq_pinnedVolterraFun] at hB
  exact (mul_eq_zero.mp hB.symm).resolve_left (mul_ne_zero hI hq)

/-- The pinned primitive has no kernel on the mean-zero hyperplane. -/
theorem eq_zero_of_pinnedMean_eq_zero_of_pinnedVolterra_eq_zero
    (f : H) (hmean : pinnedMean f = 0) (hC : pinnedVolterra f = 0) : f = 0 := by
  have hCfun : pinnedVolterraFun f =ᵐ[unitIntervalMeasure] fun _ : ℝ => (0 : ℂ) := by
    have hcoe : (fun t => (pinnedVolterra f) t) =ᵐ[unitIntervalMeasure]
        fun _ : ℝ => (0 : ℂ) := by
      rw [hC]
      simp
    exact (pinnedVolterra_coeFn f).symm.trans hcoe
  have hprefix : pinnedPrefix f =ᵐ[unitIntervalMeasure] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hCfun] with t ht
    rw [pinnedVolterraFun, hmean, mul_zero, sub_zero] at ht
    exact ht
  let F : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, f u
  have hIntOn : IntegrableOn (fun t => f t) (Icc (0 : ℝ) 1) volume := by
    change Integrable (fun t => f t) (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using integrable_coe f
  have hIntOnU : IntegrableOn (fun t => f t) (uIcc (0 : ℝ) 1) volume := by
    simpa only [uIcc_of_le zero_le_one] using hIntOn
  have hFcontinuous : ContinuousOn F (Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval hIntOnU
    simpa only [uIcc_of_le zero_le_one, F] using h
  have hFae : F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ : ℝ => (0 : ℂ) := by
    rw [← unitIntervalMeasure]
    filter_upwards [hprefix, ae_restrict_mem measurableSet_Icc] with t htzero ht
    rw [pinnedPrefix_eq_intervalIntegral f ht] at htzero
    exact htzero
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hFzero : Set.EqOn F (fun _ : ℝ => (0 : ℂ)) (Icc (0 : ℝ) 1) :=
    (volume : Measure ℝ).eqOn_of_ae_eq hFae hFcontinuous continuousOn_const hclosure
  have hldt := hIntOnU.intervalIntegrable.ae_hasDerivAt_integral
  have hldtRestrict :
      ∀ᵐ x ∂unitIntervalMeasure,
        x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x := by
    change ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      x ∈ uIcc (0 : ℝ) 1 → ∀ c ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y => ∫ t in c..y, f t) (f x) x
    exact ae_restrict_of_ae hldt
  have hfzero : (fun t => f t) =ᵐ[unitIntervalMeasure] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hldtRestrict, unitIntervalMeasure.ae_ne 0,
      unitIntervalMeasure.ae_ne 1, ae_restrict_mem measurableSet_Icc]
        with x hxderiv hx0 hx1 hx
    have hxoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
    have hFderiv : HasDerivAt F (f x) x := by
      exact hxderiv (by simpa only [uIcc_of_le zero_le_one] using hx) 0 (by simp)
    have hlocal : Filter.EventuallyEq (nhds x) F (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2] with y hy
      exact hFzero (Ioo_subset_Icc_self hy)
    have hzeroDeriv : HasDerivAt F 0 x :=
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hlocal
    exact hFderiv.unique hzeroDeriv
  apply Lp.ext
  filter_upwards [hfzero, Lp.coeFn_zero ℂ (2 : ENNReal) unitIntervalMeasure] with t ht h0
  exact ht.trans h0.symm

theorem thetaCenteredSourceInverse_injective :
    Function.Injective thetaCenteredSourceInverse := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply eq_zero_of_pinnedMean_eq_zero_of_pinnedVolterra_eq_zero ((f - g : thetaCentered) : H)
  · exact (mem_thetaCentered_iff _).mp (f - g).property
  · apply pinnedVolterra_eq_zero_of_kernelOperator_eq_zero
    change thetaCenteredSourceInverse (f - g) = 0
    rw [map_sub, hfg, sub_self]

/-! ### Compactly supported smooth source core -/

theorem integral_sourceD_eq_zero {g : ℝ → ℂ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hgs : HasCompactSupport g) :
    ∫ x, sourceD g x = 0 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hderivIntegrable : Integrable (deriv g) :=
    hg1.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hgs.deriv
  have hsplit := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi hderivIntegrable 0
  rw [hgs.integral_Iic_deriv_eq hg1 0, hgs.integral_Ioi_deriv_eq hg1 0] at hsplit
  have hderiv : ∫ x, deriv g x = 0 := by simpa using hsplit.symm
  change ∫ x, -Complex.I * deriv g x = 0
  rw [MeasureTheory.integral_const_mul, hderiv, mul_zero]

theorem sourceInverse_sourceD {g : ℝ → ℂ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hgs : HasCompactSupport g) (x : ℝ) :
    sourceInverse thetaSource (sourceD g) x = g x := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  rw [sourceInverse, integral_sourceD_eq_zero hg hgs]
  simp only [zero_div, zero_mul, sub_zero]
  change Complex.I * ∫ y in Iic x, -Complex.I * deriv g y = g x
  rw [MeasureTheory.integral_const_mul,
    hgs.integral_Iic_deriv_eq hg1 x]
  calc
    Complex.I * (-Complex.I * g x) = -(Complex.I * Complex.I) * g x := by ring
    _ = g x := by rw [Complex.I_mul_I]; ring

theorem integral_Iic_eq_const_add_interval {h : ℝ → ℂ} (hh : Integrable h) (x : ℝ) :
    (∫ y in Iic x, h y) = (∫ y in Iic (0 : ℝ), h y) + ∫ y in (0 : ℝ)..x, h y := by
  rcases le_total (0 : ℝ) x with hx | hx
  · rw [intervalIntegral.integral_of_le hx, ← MeasureTheory.setIntegral_union
      (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hh.integrableOn hh.integrableOn,
      Iic_union_Ioc_eq_Iic hx]
  · rw [intervalIntegral.integral_of_ge hx]
    have hsplit : (∫ y in Iic (0 : ℝ), h y) =
        (∫ y in Iic x, h y) + ∫ y in Ioc x (0 : ℝ), h y := by
      rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        hh.integrableOn hh.integrableOn, Iic_union_Ioc_eq_Iic hx]
    rw [hsplit]
    ring

/-- Pinned primitive of a centered smooth compactly supported source. -/
def smoothCenteredPrimitive (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.I * ∫ y in Iic x, h y

theorem hasDerivAt_smoothCenteredPrimitive {h : ℝ → ℂ}
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhs : HasCompactSupport h) (x : ℝ) :
    HasDerivAt (smoothCenteredPrimitive h) (Complex.I * h x) x := by
  have hInt : Integrable h := hh.continuous.integrable_of_hasCompactSupport hhs
  have hbase : HasDerivAt (fun y => ∫ z in (0 : ℝ)..y, h z) (h x) x :=
    (hh.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hsum := hbase.const_add (∫ z in Iic (0 : ℝ), h z)
  have hIic : HasDerivAt (fun y => ∫ z in Iic y, h z) (h x) x := by
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with y
    exact integral_Iic_eq_const_add_interval hInt y
  exact hIic.const_mul Complex.I

theorem smoothCenteredPrimitive_smooth {h : ℝ → ℂ}
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhs : HasCompactSupport h) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothCenteredPrimitive h) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_smoothCenteredPrimitive hh hhs x).differentiableAt, ?_⟩
  have hderiv : deriv (smoothCenteredPrimitive h) = fun x => Complex.I * h x := by
    funext x
    exact (hasDerivAt_smoothCenteredPrimitive hh hhs x).deriv
  rw [hderiv]
  exact contDiff_const.mul hh

theorem smoothCenteredPrimitive_compact {h : ℝ → ℂ}
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhs : HasCompactSupport h)
    (hmean : ∫ x, h x = 0) : HasCompactSupport (smoothCenteredPrimitive h) := by
  obtain ⟨R, hRpos, hR⟩ := hhs.isCompact.isBounded.subset_closedBall_lt (0 : ℝ) 0
  have hzero_of_lt_neg {x : ℝ} (hx : x < -R) : h x = 0 := by
    by_contra hne
    have hxsupp : x ∈ Function.support h := hne
    have hxball := hR ((subset_tsupport (f := h)) hxsupp)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxball
    have : R < |x| := by
      rw [abs_of_neg (hx.trans (neg_lt_zero.mpr hRpos))]
      linarith
    linarith
  have hzero_of_gt {x : ℝ} (hx : R < x) : h x = 0 := by
    by_contra hne
    have hxsupp : x ∈ Function.support h := hne
    have hxball := hR ((subset_tsupport (f := h)) hxsupp)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero,
      abs_of_pos (hRpos.trans hx)] at hxball
    linarith
  have hInt : Integrable h := hh.continuous.integrable_of_hasCompactSupport hhs
  apply (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hxball
  have hxabs : R < |x| := by
    have hxball' : ¬ |x| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero, Real.norm_eq_abs] using hxball
    exact lt_of_not_ge hxball'
  have hxzero : smoothCenteredPrimitive h x = 0 := by
    rcases le_total x 0 with hx0 | hx0
    · have hxneg : x < -R := by
        rw [abs_of_nonpos hx0] at hxabs
        linarith
      rw [smoothCenteredPrimitive,
        setIntegral_eq_zero_of_forall_eq_zero (fun y hy =>
          hzero_of_lt_neg (hy.trans_lt hxneg)), mul_zero]
    · have hxpos : R < x := by
        rw [abs_of_nonneg hx0] at hxabs
        exact hxabs
      have htail : ∫ y in Ioi x, h y = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero (fun y hy =>
          hzero_of_gt (hxpos.trans hy))
      have hsplit := HedenmalmFredholmRange.setIntegral_Iic_add_Ioi hInt x
      rw [htail, add_zero, hmean] at hsplit
      rw [smoothCenteredPrimitive, hsplit, mul_zero]
  exact hx hxzero

theorem sourceD_smoothCenteredPrimitive {h : ℝ → ℂ}
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhs : HasCompactSupport h) (x : ℝ) :
    sourceD (smoothCenteredPrimitive h) x = h x := by
  change -Complex.I * deriv (smoothCenteredPrimitive h) x = h x
  rw [(hasDerivAt_smoothCenteredPrimitive hh hhs x).deriv]
  calc
    -Complex.I * (Complex.I * h x) = -(Complex.I * Complex.I) * h x := by ring
    _ = h x := by rw [Complex.I_mul_I]; ring

/-- Exact image in `H_k` of compactly supported smooth functions. -/
def thetaSmoothSource : Set HS :=
  {u | ∃ g : ℝ → ℂ, (fun x => u x) =ᵐ[sourceMeasure] g ∧
    HasCompactSupport g ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) g}

/-- Compactly supported smooth source vectors form a genuine linear subspace of `H_k`. -/
def thetaSmoothSourceSubmodule : Submodule ℂ HS where
  carrier := thetaSmoothSource
  zero_mem' := by
    refine ⟨0, ?_, HasCompactSupport.zero, contDiff_const⟩
    exact Lp.coeFn_zero ℂ 2 sourceMeasure
  add_mem' := by
    rintro u v ⟨g, hug, hgs, hg⟩ ⟨h, hvh, hhs, hh⟩
    refine ⟨g + h, ?_, hgs.add hhs, hg.add hh⟩
    filter_upwards [Lp.coeFn_add u v, hug, hvh] with x huv hugx hvhx
    rw [huv]
    change u x + v x = g x + h x
    rw [hugx, hvhx]
  smul_mem' := by
    rintro c u ⟨g, hug, hgs, hg⟩
    refine ⟨fun x => c * g x, ?_, hgs.mul_left, contDiff_const.mul hg⟩
    filter_upwards [Lp.coeFn_smul c u, hug] with x hc hugx
    rw [hc]
    change c * u x = c * g x
    rw [hugx]

theorem dense_thetaSmoothSource : Dense thetaSmoothSource := by
  simpa only [thetaSmoothSource, HS, sourceMeasure] using
    (Lp.dense_hasCompactSupport_contDiff (μ := sourceMeasure) (F := ℂ)
      (by norm_num : (2 : ENNReal) ≠ ⊤))

theorem memLp_sourceD {g : ℝ → ℂ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hgs : HasCompactSupport g) : MemLp (sourceD g) 2 sourceMeasure := by
  apply Continuous.memLp_of_hasCompactSupport
  · change Continuous (fun x => -Complex.I * deriv g x)
    exact (hg.of_le (by simp)).continuous_deriv le_rfl |>.const_mul _
  · change HasCompactSupport (fun x => -Complex.I * deriv g x)
    exact hgs.deriv.mul_left

theorem memLp_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hgs : HasCompactSupport g) : MemLp g 2 sourceMeasure :=
  hg.continuous.memLp_of_hasCompactSupport hgs

/-- Fixed normalized `C_c^∞` correction profile. -/
def thetaCoreBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def thetaCoreProfile (x : ℝ) : ℂ := (thetaCoreBump.normed volume x : ℂ)

theorem thetaCoreProfile_smooth :
    ContDiff ℝ (↑(⊤ : ℕ∞)) thetaCoreProfile := by
  exact Complex.ofRealCLM.contDiff.comp thetaCoreBump.contDiff_normed

theorem thetaCoreProfile_compact : HasCompactSupport thetaCoreProfile :=
  thetaCoreBump.hasCompactSupport_normed.comp_left rfl

theorem integral_thetaCoreProfile : ∫ x, thetaCoreProfile x = 1 := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (thetaCoreBump.integral_normed (μ := volume))
  exact (integral_ofReal (𝕜 := ℂ)).trans h

def thetaCoreProfileVector : HS :=
  (memLp_smooth thetaCoreProfile_smooth thetaCoreProfile_compact).toLp thetaCoreProfile

theorem thetaCoreProfileVector_ae :
    (fun x => thetaCoreProfileVector x) =ᵐ[sourceMeasure] thetaCoreProfile :=
  (memLp_smooth thetaCoreProfile_smooth thetaCoreProfile_compact).coeFn_toLp

theorem quantile_sourceD_mem_centered {g : ℝ → ℂ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hgs : HasCompactSupport g) :
    quantileUnitary thetaSource ((memLp_sourceD hg hgs).toLp (sourceD g)) ∈ thetaCentered := by
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  have hfAEμ : (fun x => f x) =ᵐ[sourceMeasure] sourceD g :=
    (memLp_sourceD hg hgs).coeFn_toLp
  have hfAE : (fun x => f x) =ᵐ[volume] sourceD g :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using hfAEμ)
  rw [mem_thetaCentered_iff, pinnedMean_quantileUnitary]
  rw [integral_quantileTransform thetaSource
    (integrable_sourceSpace thetaSource f).aestronglyMeasurable]
  rw [integral_congr_ae hfAE, integral_sourceD_eq_zero hg hgs, zero_div]

theorem thetaCompactSourceInverse_quantile_sourceD {g : ℝ → ℂ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hgs : HasCompactSupport g) :
    thetaCompactSourceInverse
        (quantileUnitary thetaSource ((memLp_sourceD hg hgs).toLp (sourceD g))) =
      quantileUnitary thetaSource ((memLp_smooth hg hgs).toLp g) := by
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  have hgMem : MemLp g 2 sourceMeasure := memLp_smooth hg hgs
  let u : HS := hgMem.toLp g
  have hfAEμ : (fun x => f x) =ᵐ[sourceMeasure] sourceD g :=
    (memLp_sourceD hg hgs).coeFn_toLp
  have huAEμ : (fun x => u x) =ᵐ[sourceMeasure] g := hgMem.coeFn_toLp
  have hfAE : (fun x => f x) =ᵐ[volume] sourceD g :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using hfAEμ)
  have huAE : (fun x => u x) =ᵐ[volume] g :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using huAEμ)
  have huQ : (fun t => u (thetaSource.quantileFun t)) =ᵐ[unitIntervalMeasure]
      fun t => g (thetaSource.quantileFun t) :=
    ((thetaSource.law_ae_eq).mpr huAE).comp_tendsto
      (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards
      [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource
        (quantileUnitary thetaSource f),
       quantileUnitary_ae thetaSource f, quantileUnitary_ae thetaSource u,
       huQ, ae_unitIntervalMeasure_mem_Ioo]
    with t hB hUf hUu hgu ht
  change ((thetaCompactSourceInverse (quantileUnitary thetaSource f) : H) : ℝ → ℂ) t = _ at hB
  calc
    ((thetaCompactSourceInverse (quantileUnitary thetaSource f) : H) : ℝ → ℂ) t =
        pinnedKernelField thetaSource t (quantileUnitary thetaSource f) := hB
    _ = quantileTransform thetaSource (sourceInverse thetaSource (fun x => f x)) t := by
      rw [pinnedKernelField_apply_eq_pinnedVolterraFun]
      exact (quantileTransform_sourceInverse_eq_pinned thetaSource f ht).symm
    _ = quantileTransform thetaSource (sourceInverse thetaSource (sourceD g)) t := by
      unfold quantileTransform
      rw [sourceInverse_congr_ae thetaSource hfAE]
    _ = quantileTransform thetaSource g t := by
      unfold quantileTransform
      rw [sourceInverse_sourceD hg hgs]
    _ = quantileTransform thetaSource (fun x => u x) t := by
      rw [quantileTransform, quantileTransform, hgu]
    _ = (quantileUnitary thetaSource u : ℝ → ℂ) t := hUu.symm

theorem quantile_thetaSmoothSource_mem_range
    (u : HS) (hu : u ∈ thetaSmoothSource) :
    quantileUnitary thetaSource u ∈ thetaCenteredSourceInverse.range := by
  rcases hu with ⟨g, hug, hgs, hg⟩
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  have hfCentered : quantileUnitary thetaSource f ∈ thetaCentered :=
    quantile_sourceD_mem_centered hg hgs
  refine ⟨⟨quantileUnitary thetaSource f, hfCentered⟩, ?_⟩
  change thetaCompactSourceInverse (quantileUnitary thetaSource f) =
    quantileUnitary thetaSource u
  rw [thetaCompactSourceInverse_quantile_sourceD hg hgs]
  have hueq : (memLp_smooth hg hgs).toLp g = u := by
    apply Lp.ext
    filter_upwards [hug, (memLp_smooth hg hgs).coeFn_toLp] with x hux hgx
    exact hgx.trans hux.symm
  exact congrArg (quantileUnitary thetaSource) hueq

theorem thetaCenteredSourceInverse_dense_range :
    Dense (thetaCenteredSourceInverse.range : Set H) := by
  have hsub : DenseRange (fun u : {u : HS // u ∈ thetaSmoothSource} => (u : HS)) :=
    denseRange_subtype_val.mpr dense_thetaSmoothSource
  have hU : DenseRange (quantileUnitary thetaSource : HS → H) :=
    (quantileUnitary thetaSource).surjective.denseRange
  have hcomp := hU.comp hsub (quantileUnitary thetaSource).continuous
  apply hcomp.mono
  intro y hy
  rcases hy with ⟨u, rfl⟩
  exact quantile_thetaSmoothSource_mem_range u u.property

/-! ### Closed weighted derivative and Fredholm range -/

theorem thetaCentered_isClosed : IsClosed (thetaCentered : Set H) := by
  simpa only [thetaCentered] using
    (Submodule.isClosed_orthogonal (ℂ ∙ pinnedOne : Submodule ℂ H))

local instance hedenmalmClosedWeightedDerivativeLocalInst3 : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

/-- Closure of `-i d/dx`, realized as graph inverse of the compact centered source inverse. -/
def thetaWeightedDerivative : H →ₗ.[ℂ] H :=
  closedHyperplaneInverse thetaCentered thetaCenteredSourceInverse

theorem thetaWeightedDerivative_isClosed : thetaWeightedDerivative.IsClosed :=
  closedHyperplaneInverse_isClosed thetaCentered thetaCentered_isClosed
    thetaCenteredSourceInverse thetaCenteredSourceInverse_injective

theorem thetaWeightedDerivative_dense_domain :
    Dense (thetaWeightedDerivative.domain : Set H) :=
  closedHyperplaneInverse_dense_domain thetaCentered thetaCenteredSourceInverse
    thetaCenteredSourceInverse_dense_range

theorem thetaWeightedDerivative_kernel_eq_bot : thetaWeightedDerivative.kernel = ⊥ :=
  closedHyperplaneInverse_kernel_eq_bot thetaCentered thetaCenteredSourceInverse
    thetaCenteredSourceInverse_injective

theorem thetaWeightedDerivative_range :
    thetaWeightedDerivative.rangeSubmodule = thetaCentered :=
  closedHyperplaneInverse_range thetaCentered thetaCenteredSourceInverse
    thetaCenteredSourceInverse_injective

/-- Bounded mean functional cutting out the codimension-one range. -/
def thetaPinnedMeanCLM : H →L[ℂ] ℂ := innerSL ℂ pinnedOne

theorem thetaPinnedMeanCLM_apply (f : H) : thetaPinnedMeanCLM f = pinnedMean f := by
  change inner ℂ pinnedOne f = pinnedMean f
  rw [inner_lp_eq, pinnedMean]
  apply integral_congr_ae
  filter_upwards [pinnedOne_coeFn] with t ht
  rw [ht]
  simp

theorem thetaPinnedMeanCLM_surjective : Function.Surjective thetaPinnedMeanCLM := by
  intro c
  refine ⟨c • pinnedOne, ?_⟩
  rw [map_smul, thetaPinnedMeanCLM_apply, pinnedMean_pinnedOne]
  simp

theorem thetaCentered_eq_ker_pinnedMean :
    thetaCentered = LinearMap.ker thetaPinnedMeanCLM.toLinearMap := by
  ext f
  rw [mem_thetaCentered_iff, LinearMap.mem_ker]
  change pinnedMean f = 0 ↔ thetaPinnedMeanCLM f = 0
  rw [thetaPinnedMeanCLM_apply]

/-- Normalized smooth vector whose interval-coordinate mean is one. -/
def thetaCoreMeanOne : H :=
  (Real.sqrt thetaSource.mass : ℂ) •
    quantileUnitary thetaSource thetaCoreProfileVector

theorem thetaCoreMeanOne_mean : pinnedMean thetaCoreMeanOne = 1 := by
  rw [← thetaPinnedMeanCLM_apply, thetaCoreMeanOne, map_smul,
    thetaPinnedMeanCLM_apply, pinnedMean_quantileUnitary]
  rw [integral_quantileTransform thetaSource
    (integrable_sourceSpace thetaSource thetaCoreProfileVector).aestronglyMeasurable]
  have hAEμ := thetaCoreProfileVector_ae
  have hAE : (fun x => thetaCoreProfileVector x) =ᵐ[volume] thetaCoreProfile :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using hAEμ)
  rw [integral_congr_ae hAE, integral_thetaCoreProfile]
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  rw [smul_eq_mul, one_div, mul_inv_cancel₀ hsqrt]

/-- Continuous projection onto the centered hyperplane, preserving `C_c^∞`. -/
def thetaCenterProjection : H →L[ℂ] H :=
  1 - thetaPinnedMeanCLM.smulRight thetaCoreMeanOne

theorem thetaCenterProjection_apply (f : H) :
    thetaCenterProjection f = f - pinnedMean f • thetaCoreMeanOne := by
  simp [thetaCenterProjection, thetaPinnedMeanCLM_apply]

theorem thetaCenterProjection_mem (f : H) : thetaCenterProjection f ∈ thetaCentered := by
  rw [mem_thetaCentered_iff, thetaCenterProjection_apply]
  calc
    pinnedMean (f - pinnedMean f • thetaCoreMeanOne) =
        thetaPinnedMeanCLM (f - pinnedMean f • thetaCoreMeanOne) :=
      (thetaPinnedMeanCLM_apply _).symm
    _ = 0 := by
      rw [map_sub, map_smul, thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply,
        thetaCoreMeanOne_mean]
      simp

def thetaCenterProjectionToCentered : H →L[ℂ] thetaCentered :=
  thetaCenterProjection.codRestrict thetaCentered thetaCenterProjection_mem

theorem thetaCenterProjectionToCentered_surjective :
    Function.Surjective thetaCenterProjectionToCentered := by
  intro f
  refine ⟨(f : H), Subtype.ext ?_⟩
  change thetaCenterProjection (f : H) = (f : H)
  rw [thetaCenterProjection_apply]
  rw [(mem_thetaCentered_iff f).mp f.property, zero_smul, sub_zero]

theorem thetaWeightedDerivative_isFredholm : thetaWeightedDerivative.IsFredholm :=
  closedHyperplaneInverse_isFredholm thetaCentered thetaCentered_isClosed
    thetaCenteredSourceInverse thetaCenteredSourceInverse_injective thetaPinnedMeanCLM
    thetaPinnedMeanCLM_surjective thetaCentered_eq_ker_pinnedMean

theorem thetaWeightedDerivative_index : thetaWeightedDerivative.index = -1 :=
  closedHyperplaneInverse_index_eq_neg_one thetaCentered thetaCenteredSourceInverse
    thetaCenteredSourceInverse_injective thetaPinnedMeanCLM
    thetaPinnedMeanCLM_surjective thetaCentered_eq_ker_pinnedMean

theorem thetaWeightedDerivative_adjoint_kernel :
    thetaWeightedDerivative.adjoint.kernel = ℂ ∙ pinnedOne := by
  rw [show thetaWeightedDerivative.adjoint.kernel = thetaCenteredᗮ from
    closedHyperplaneInverse_adjoint_kernel thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective thetaCenteredSourceInverse_dense_range]
  rw [thetaCentered, Submodule.orthogonal_orthogonal]

/-! ### Literal compactly supported smooth core -/

/-- Quantile images of actual compactly supported smooth functions. -/
def thetaDerivativeCoreSubmodule : Submodule ℂ H :=
  thetaSmoothSourceSubmodule.map (quantileUnitary thetaSource).toLinearMap

theorem thetaDerivativeCoreSubmodule_le_domain :
    thetaDerivativeCoreSubmodule ≤ thetaWeightedDerivative.domain := by
  rintro y ⟨u, hu, rfl⟩
  rcases hu with ⟨g, hug, hgs, hg⟩
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  have hfCentered : quantileUnitary thetaSource f ∈ thetaCentered :=
    quantile_sourceD_mem_centered hg hgs
  rw [thetaWeightedDerivative, closedHyperplaneInverse_domain]
  refine ⟨⟨quantileUnitary thetaSource f, hfCentered⟩, ?_⟩
  change thetaCompactSourceInverse (quantileUnitary thetaSource f) =
    quantileUnitary thetaSource u
  rw [thetaCompactSourceInverse_quantile_sourceD hg hgs]
  have hueq : (memLp_smooth hg hgs).toLp g = u := by
    apply Lp.ext
    filter_upwards [hug, (memLp_smooth hg hgs).coeFn_toLp] with x hux hgx
    exact hgx.trans hux.symm
  exact congrArg (quantileUnitary thetaSource) hueq

theorem thetaCoreProfileVector_mem_smooth :
    thetaCoreProfileVector ∈ thetaSmoothSourceSubmodule :=
  ⟨thetaCoreProfile, thetaCoreProfileVector_ae,
    thetaCoreProfile_compact, thetaCoreProfile_smooth⟩

/-- Centered correction of an actual smooth compactly supported source. -/
def thetaSmoothCenteredMap (u : thetaSmoothSourceSubmodule) : thetaCentered :=
  thetaCenterProjectionToCentered (quantileUnitary thetaSource (u : HS))

theorem thetaSmoothCenteredMap_denseRange : DenseRange thetaSmoothCenteredMap := by
  have hsub : DenseRange (fun u : thetaSmoothSourceSubmodule => (u : HS)) := by
    rw [denseRange_subtype_val]
    change Dense thetaSmoothSource
    exact dense_thetaSmoothSource
  have hU : DenseRange (quantileUnitary thetaSource : HS → H) :=
    (quantileUnitary thetaSource).surjective.denseRange
  have hUsub := hU.comp hsub (quantileUnitary thetaSource).continuous
  have hP : DenseRange thetaCenterProjectionToCentered :=
    thetaCenterProjectionToCentered_surjective.denseRange
  have hcomp := hP.comp hUsub thetaCenterProjectionToCentered.continuous
  convert hcomp using 1
  funext u
  rfl

theorem thetaSmoothCenteredMap_eq_quantile (u : thetaSmoothSourceSubmodule) :
    ∃ v : thetaSmoothSourceSubmodule,
      (thetaSmoothCenteredMap u : H) = quantileUnitary thetaSource (v : HS) := by
  let c : ℂ := pinnedMean (quantileUnitary thetaSource (u : HS))
  let v₀ : HS :=
    (u : HS) - (c * (Real.sqrt thetaSource.mass : ℂ)) • thetaCoreProfileVector
  have hv₀ : v₀ ∈ thetaSmoothSourceSubmodule := by
    exact thetaSmoothSourceSubmodule.sub_mem u.property
      (thetaSmoothSourceSubmodule.smul_mem _ thetaCoreProfileVector_mem_smooth)
  refine ⟨⟨v₀, hv₀⟩, ?_⟩
  change thetaCenterProjection (quantileUnitary thetaSource (u : HS)) =
    quantileUnitary thetaSource v₀
  rw [thetaCenterProjection_apply]
  simp only [v₀, c, map_sub, map_smul, thetaCoreMeanOne]
  module

theorem thetaSmoothCenteredMap_eq_derivative (u : thetaSmoothSourceSubmodule) :
    ∃ (g : ℝ → ℂ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hgs : HasCompactSupport g),
      (thetaSmoothCenteredMap u : H) =
        quantileUnitary thetaSource ((memLp_sourceD hg hgs).toLp (sourceD g)) := by
  rcases thetaSmoothCenteredMap_eq_quantile u with ⟨v, hv⟩
  rcases v.property with ⟨h, hvh, hhs, hh⟩
  have hvCentered : quantileUnitary thetaSource (v : HS) ∈ thetaCentered := by
    rw [← hv]
    exact (thetaSmoothCenteredMap u).property
  have hmeanv : pinnedMean (quantileUnitary thetaSource (v : HS)) = 0 :=
    (mem_thetaCentered_iff _).mp hvCentered
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  have hvIntegral : ∫ x, (v : HS) x = 0 := by
    have hformula := pinnedMean_quantileUnitary thetaSource (v : HS)
    rw [integral_quantileTransform thetaSource
      (integrable_sourceSpace thetaSource (v : HS)).aestronglyMeasurable] at hformula
    have hdiv : (∫ x, (v : HS) x) / (Real.sqrt thetaSource.mass : ℂ) = 0 := by
      rw [← hformula]
      exact hmeanv
    exact (div_eq_zero_iff.mp hdiv).resolve_right hsqrt
  have hvhVolume : (fun x => (v : HS) x) =ᵐ[volume] h :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (by simpa [sourceMeasure] using hvh)
  have hmean : ∫ x, h x = 0 := by
    rw [← integral_congr_ae hvhVolume]
    exact hvIntegral
  let g := smoothCenteredPrimitive h
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := smoothCenteredPrimitive_smooth hh hhs
  have hgs : HasCompactSupport g := smoothCenteredPrimitive_compact hh hhs hmean
  refine ⟨g, hg, hgs, ?_⟩
  let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
  have hfg : f = (v : HS) := by
    apply Lp.ext
    filter_upwards [(memLp_sourceD hg hgs).coeFn_toLp, hvh] with x hfx hvx
    rw [hfx, hvx]
    exact sourceD_smoothCenteredPrimitive hh hhs x
  exact hv.trans (congrArg (quantileUnitary thetaSource) hfg).symm

/-- Derivative outputs of literal `C_c^∞` functions, as vectors of the centered hyperplane. -/
def thetaDerivativeCoreOutput : Set thetaCentered :=
  {k | ∃ (g : ℝ → ℂ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
      (hgs : HasCompactSupport g),
    (k : H) = quantileUnitary thetaSource ((memLp_sourceD hg hgs).toLp (sourceD g))}

theorem dense_thetaDerivativeCoreOutput : Dense thetaDerivativeCoreOutput := by
  apply thetaSmoothCenteredMap_denseRange.mono
  rintro k ⟨u, rfl⟩
  rcases thetaSmoothCenteredMap_eq_derivative u with ⟨g, hg, hgs, heq⟩
  exact ⟨g, hg, hgs, heq⟩

/-- Restriction of the closed derivative to its literal `C_c^∞` domain. -/
def thetaDerivativeCore : H →ₗ.[ℂ] H :=
  thetaWeightedDerivative.domRestrict thetaDerivativeCoreSubmodule

theorem thetaDerivativeCore_graph_closure :
    closure (thetaDerivativeCore.graph : Set (H × H)) = thetaWeightedDerivative.graph := by
  let F : thetaCentered →L[ℂ] H × H :=
    thetaCenteredSourceInverse.prod thetaCentered.subtypeL
  have hMaps : MapsTo F thetaDerivativeCoreOutput thetaDerivativeCore.graph := by
    intro k hk
    rcases hk with ⟨g, hg, hgs, hk⟩
    let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
    let u : HS := (memLp_smooth hg hgs).toLp g
    have hfCentered : quantileUnitary thetaSource f ∈ thetaCentered :=
      quantile_sourceD_mem_centered hg hgs
    have hkSub : k = ⟨quantileUnitary thetaSource f, hfCentered⟩ := Subtype.ext hk
    have hB : thetaCenteredSourceInverse k = quantileUnitary thetaSource u := by
      rw [hkSub]
      exact thetaCompactSourceInverse_quantile_sourceD hg hgs
    have huSmooth : u ∈ thetaSmoothSourceSubmodule :=
      ⟨g, (memLp_smooth hg hgs).coeFn_toLp, hgs, hg⟩
    have hcoreSub : thetaCenteredSourceInverse k ∈ thetaDerivativeCoreSubmodule := by
      refine ⟨u, huSmooth, ?_⟩
      exact hB.symm
    have hAdom : thetaCenteredSourceInverse k ∈ thetaWeightedDerivative.domain := by
      rw [thetaWeightedDerivative, closedHyperplaneInverse_domain]
      exact ⟨k, rfl⟩
    change F k ∈ thetaDerivativeCore.graph
    rw [LinearPMap.mem_graph_iff]
    let xcore : thetaDerivativeCore.domain :=
      ⟨thetaCenteredSourceInverse k, ⟨hcoreSub, hAdom⟩⟩
    refine ⟨xcore, rfl, ?_⟩
    have hAapply : thetaWeightedDerivative
        ⟨thetaCenteredSourceInverse k, hAdom⟩ = (k : H) := by
      simpa only [thetaWeightedDerivative] using
        (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
          thetaCenteredSourceInverse_injective k).2
    exact (LinearPMap.domRestrict_apply (y :=
      (⟨thetaCenteredSourceInverse k, hAdom⟩ : thetaWeightedDerivative.domain)) rfl).trans
        hAapply
  apply le_antisymm
  · apply closure_minimal
      (LinearPMap.le_graph_of_le
        (LinearPMap.domRestrict_le : thetaDerivativeCore ≤ thetaWeightedDerivative))
    exact thetaWeightedDerivative_isClosed
  · intro p hp
    change p ∈ thetaWeightedDerivative.graph at hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hx, hout⟩
    have hxRange : (x : H) ∈ thetaCenteredSourceInverse.range := by
      rw [← closedHyperplaneInverse_domain thetaCentered thetaCenteredSourceInverse]
      exact x.property
    rcases hxRange with ⟨k, hk⟩
    have hAapply : thetaWeightedDerivative x = (k : H) := by
      have h := (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
        thetaCenteredSourceInverse_injective k).2
      have heq : x = ⟨thetaCenteredSourceInverse k,
          (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
            thetaCenteredSourceInverse_injective k).1⟩ := Subtype.ext hk.symm
      simpa only [thetaWeightedDerivative, heq] using h
    have hpEq : F k = p := by
      apply Prod.ext
      · exact hk.trans hx
      · exact hAapply.symm.trans hout
    rw [← hpEq]
    have hkClosure : k ∈ closure thetaDerivativeCoreOutput := by
      rw [dense_thetaDerivativeCoreOutput.closure_eq]
      exact Set.mem_univ k
    exact map_mem_closure F.continuous hkClosure hMaps

theorem thetaDerivativeCore_isClosable : thetaDerivativeCore.IsClosable :=
  thetaWeightedDerivative_isClosed.isClosable.leIsClosable
    (LinearPMap.domRestrict_le : thetaDerivativeCore ≤ thetaWeightedDerivative)

theorem thetaDerivativeCore_closure_eq :
    thetaDerivativeCore.closure = thetaWeightedDerivative := by
  apply LinearPMap.eq_of_eq_graph
  rw [← thetaDerivativeCore_isClosable.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  simpa only [Submodule.topologicalClosure_coe] using thetaDerivativeCore_graph_closure

/-- Literal `C_c^∞(ℝ)` is a graph core; its closure is the constructed maximal derivative. -/
theorem thetaWeightedDerivative_hasCore :
    thetaWeightedDerivative.HasCore thetaDerivativeCoreSubmodule := by
  refine ⟨thetaDerivativeCoreSubmodule_le_domain, ?_⟩
  exact thetaDerivativeCore_closure_eq

theorem thetaDerivativeCore_dense_domain :
    Dense (thetaDerivativeCore.domain : Set H) := by
  have hsub : DenseRange (fun u : thetaSmoothSourceSubmodule => (u : HS)) := by
    rw [denseRange_subtype_val]
    change Dense thetaSmoothSource
    exact dense_thetaSmoothSource
  have hU : DenseRange (quantileUnitary thetaSource : HS → H) :=
    (quantileUnitary thetaSource).surjective.denseRange
  have hcomp := hU.comp hsub (quantileUnitary thetaSource).continuous
  have hcoreSub : Dense (thetaDerivativeCoreSubmodule : Set H) := by
    apply hcomp.mono
    rintro _ ⟨u, rfl⟩
    exact ⟨u, u.property, rfl⟩
  have hdomain : thetaDerivativeCore.domain = thetaDerivativeCoreSubmodule := by
    change thetaDerivativeCoreSubmodule ⊓ thetaWeightedDerivative.domain =
      thetaDerivativeCoreSubmodule
    exact inf_eq_left.mpr thetaDerivativeCoreSubmodule_le_domain
  rw [hdomain]
  exact hcoreSub

/-- Maximal weak first-order operator paired with the closed derivative. -/
def thetaMaximalWeightedAdjoint : H →ₗ.[ℂ] H := thetaWeightedDerivative.adjoint

/-- A vector lies in the maximal adjoint domain exactly when its weak derivative is represented by
an ambient Hilbert vector on every literal `C_c^∞` test vector. -/
theorem mem_thetaMaximalWeightedAdjoint_domain_iff (y : H) :
    y ∈ thetaMaximalWeightedAdjoint.domain ↔
      ∃ w : H, ∀ x : thetaDerivativeCore.domain,
        inner ℂ w (x : H) = inner ℂ y (thetaDerivativeCore x) := by
  exact LinearPMap.mem_adjoint_domain_iff_of_graph_core
    thetaWeightedDerivative thetaDerivativeCore thetaWeightedDerivative_dense_domain
    (LinearPMap.domRestrict_le : thetaDerivativeCore ≤ thetaWeightedDerivative)
    thetaDerivativeCore_graph_closure y

/-- Representing weak derivative is unique and is exactly the maximal-adjoint value. -/
theorem thetaMaximalWeightedAdjoint_apply_eq
    (y : thetaMaximalWeightedAdjoint.domain) (w : H)
    (hw : ∀ x : thetaDerivativeCore.domain,
      inner ℂ w (x : H) = inner ℂ (y : H) (thetaDerivativeCore x)) :
    thetaMaximalWeightedAdjoint y = w := by
  apply thetaDerivativeCore_dense_domain.eq_of_inner_left ℂ
  intro _ hx
  let x : thetaDerivativeCore.domain := ⟨_, hx⟩
  let xA : thetaWeightedDerivative.domain :=
    ⟨(x : H), thetaDerivativeCoreSubmodule_le_domain x.property.1⟩
  have hcoreApply : thetaDerivativeCore x = thetaWeightedDerivative xA :=
    (LinearPMap.domRestrict_le : thetaDerivativeCore ≤ thetaWeightedDerivative).2 rfl
  calc
    inner ℂ (thetaMaximalWeightedAdjoint y) (x : H) =
        inner ℂ (y : H) (thetaWeightedDerivative xA) :=
      LinearPMap.adjoint_isFormalAdjoint thetaWeightedDerivative_dense_domain y xA
    _ = inner ℂ (y : H) (thetaDerivativeCore x) :=
      congrArg (inner ℂ (y : H)) hcoreApply.symm
    _ = inner ℂ w (x : H) := (hw x).symm

/-! ### Exact adjoint square and compact Witten resolvent -/

/-- Bounded inverse of the Witten Hamiltonian `A†A`. -/
def thetaWittenResolvent : H →L[ℂ] H :=
  thetaCenteredSourceInverse.comp thetaCenteredSourceInverse.adjoint

theorem thetaCenteredSourceInverse_adjoint_injective :
    Function.Injective thetaCenteredSourceInverse.adjoint := by
  intro x y hxy
  apply thetaCenteredSourceInverse_dense_range.eq_of_inner_left ℂ
  intro _ hk
  rcases hk with ⟨k, rfl⟩
  calc
    inner ℂ x (thetaCenteredSourceInverse k : H) =
        inner ℂ (thetaCenteredSourceInverse.adjoint x) k :=
      (thetaCenteredSourceInverse.adjoint_inner_left k x).symm
    _ = inner ℂ (thetaCenteredSourceInverse.adjoint y) k :=
      congrArg (fun z => inner ℂ z k) hxy
    _ = inner ℂ y (thetaCenteredSourceInverse k : H) :=
      thetaCenteredSourceInverse.adjoint_inner_left k y

theorem thetaWittenResolvent_injective : Function.Injective thetaWittenResolvent := by
  simpa only [thetaWittenResolvent, ContinuousLinearMap.coe_comp] using
    (thetaCenteredSourceInverse.self_comp_adjoint_injective_iff.mpr
      thetaCenteredSourceInverse_adjoint_injective)

theorem thetaWittenResolvent_isSelfAdjoint : IsSelfAdjoint thetaWittenResolvent := by
  change thetaWittenResolvent.adjoint = thetaWittenResolvent
  rw [thetaWittenResolvent]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem thetaWittenResolvent_dense_range :
    Dense (thetaWittenResolvent.range : Set H) := by
  have horth : thetaWittenResolvent.rangeᗮ = ⊥ := by
    rw [thetaWittenResolvent.orthogonal_range,
      show thetaWittenResolvent.adjoint = thetaWittenResolvent from
        thetaWittenResolvent_isSelfAdjoint]
    exact LinearMap.ker_eq_bot.mpr thetaWittenResolvent_injective
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  simpa using horth

theorem thetaWittenResolvent_compact : IsCompactOperator thetaWittenResolvent := by
  exact (isCompactOperator_thetaCompactSourceInverse.comp_clm
    thetaCentered.subtypeL).comp_clm thetaCenteredSourceInverse.adjoint

/-- Positive self-adjoint Witten Hamiltonian. The following equality identifies it with the
literal natural-domain composition `A†A`. -/
def thetaWittenHamiltonian : H →ₗ.[ℂ] H :=
  closedDenseInverse thetaWittenResolvent

theorem thetaWittenHamiltonian_isClosed : thetaWittenHamiltonian.IsClosed :=
  closedDenseInverse_isClosed thetaWittenResolvent thetaWittenResolvent_injective

theorem thetaWittenHamiltonian_dense_domain :
    Dense (thetaWittenHamiltonian.domain : Set H) :=
  closedDenseInverse_dense_domain thetaWittenResolvent thetaWittenResolvent_dense_range

theorem thetaWittenHamiltonian_isSelfAdjoint : IsSelfAdjoint thetaWittenHamiltonian :=
  closedDenseInverse_isSelfAdjoint thetaWittenResolvent thetaWittenResolvent_injective
    thetaWittenResolvent_dense_range thetaWittenResolvent_isSelfAdjoint

theorem thetaWittenHamiltonian_eq_adjointSquare :
    thetaWittenHamiltonian = LinearPMap.adjointSquare thetaWeightedDerivative := by
  exact (closedHyperplaneInverse_adjointSquare_eq_closedDenseInverse
    thetaCentered thetaCenteredSourceInverse thetaCenteredSourceInverse_injective
      thetaCenteredSourceInverse_dense_range).symm

theorem thetaWittenHamiltonian_kernel_eq_bot : thetaWittenHamiltonian.kernel = ⊥ :=
  closedDenseInverse_kernel_eq_bot thetaWittenResolvent thetaWittenResolvent_injective

theorem thetaWittenHamiltonian_hasCompactResolventAt_zero :
    LinearPMap.HasCompactResolventAt thetaWittenHamiltonian 0 :=
  closedDenseInverse_hasCompactResolventAt_zero thetaWittenResolvent
    thetaWittenResolvent_injective thetaWittenResolvent_compact

theorem thetaWittenHamiltonian_nonnegative (x : thetaWittenHamiltonian.domain) :
    0 ≤ (inner ℂ (thetaWittenHamiltonian x) (x : H)).re := by
  have hxRange : (x : H) ∈ thetaWittenResolvent.range := by
    rw [← closedDenseInverse_domain thetaWittenResolvent]
    exact x.property
  rcases hxRange with ⟨y, hy⟩
  have hApply := (closedDenseInverse_apply_C thetaWittenResolvent
    thetaWittenResolvent_injective y).2
  have heq : x = ⟨thetaWittenResolvent y,
      (closedDenseInverse_apply_C thetaWittenResolvent
        thetaWittenResolvent_injective y).1⟩ := Subtype.ext hy.symm
  have hTx : thetaWittenHamiltonian x = y := by
    exact (congrArg thetaWittenHamiltonian heq).trans hApply
  calc
    0 ≤ (inner ℂ (thetaCenteredSourceInverse.adjoint y)
        (thetaCenteredSourceInverse.adjoint y)).re :=
      (inner_self_nonneg (𝕜 := ℂ) (x := thetaCenteredSourceInverse.adjoint y))
    _ = (inner ℂ y (thetaCenteredSourceInverse
        (thetaCenteredSourceInverse.adjoint y) : H)).re := by
      rw [thetaCenteredSourceInverse.adjoint_inner_left]
    _ = (inner ℂ (thetaWittenHamiltonian x) (x : H)).re := by
      congr 2
      exact hTx.symm

end HedenmalmClosedWeightedDerivative

end

end RHTower
