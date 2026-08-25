import GaloisForLFunctions.HTGeometry.DiskBoundaryQuotientLeakage
import GaloisForLFunctions.HTGeometry.HorizontalLayerBlaschkeGeometry
import GaloisForLFunctions.RHTower.SuzukiShiftedXiBoundaryGramRank
import GaloisForLFunctions.RHTower.SuzukiShiftedXiCommonDivisorCancellation
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteDiskFactor
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteBlaschkeIsometry
import GaloisForLFunctions.RHTower.SuzukiShiftedXiLeakageNormBounds
import GaloisForLFunctions.RHTower.SuzukiShiftedXiAnalyticKernelRealization
import GaloisForLFunctions.RHTower.XiShiftEulerRegionIndex

/-!
# Exact boundary factorization of Suzuki's shifted-Xi quotient

The complete infinite numerator and pole Blaschke denominator already identify the interior
generalized-Schur kernel.  Here the remaining global phase is fixed at `i`, the cross identity is
upgraded by analytic continuation to a cross-multiplied identity on the entire upper half-plane,
and radial boundary convergence identifies the actual patched real-axis quotient almost
everywhere.  Consequently its literal anti-causal compression has exactly the cancellation-aware
divisor rank profile.
-/

open Complex MeasureTheory Filter Set Topology
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

local instance : MeasurableSpace Circle :=
  GaloisForLFunctions.HTGeometry.instMeasurableSpaceCircle_galoisForLFunctions

private theorem suzukiCanonicalE_I_ne_zero (omega : ℝ) :
    suzukiCanonicalE omega I ≠ 0 := by
  rw [suzukiCanonicalE]
  convert xi_ne_zero_of_real (3 / 2 + omega) using 1
  rw [Complex.I_mul_I]
  push_cast
  ring

private theorem suzukiCanonicalE_neg_I_ne_zero (omega : ℝ) :
    suzukiCanonicalE omega (-I) ≠ 0 := by
  rw [suzukiCanonicalE]
  convert xi_ne_zero_of_real (omega - 1 / 2) using 1
  rw [neg_mul, Complex.I_mul_I]
  push_cast
  ring

private theorem suzukiCanonicalTheta_I_ne_zero (omega : ℝ) :
    suzukiCanonicalTheta omega I ≠ 0 := by
  rw [suzukiCanonicalTheta_eq_E_neg_div_E]
  exact div_ne_zero (suzukiCanonicalE_neg_I_ne_zero omega)
    (suzukiCanonicalE_I_ne_zero omega)

private theorem xiShiftPoleBlaschkeMultiplier_I_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega) :
    (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley I) ≠ 0 := by
  apply xiShiftPoleBlaschkeMultiplier_cayley_ne_zero homega (by simp)
  intro hext
  apply suzukiCanonicalE_I_ne_zero omega
  rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hext]
  ring

/-- Quotient of the complete disk numerator and pole denominator at an upper-half-plane point. -/
def xiShiftInfiniteBoundaryQuotient
    {omega : ℝ} (homega : 0 ≤ omega) (z : ℂ) : ℂ :=
  (xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z) /
    (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z)

/-- The unique global phase matching the complete disk quotient to Suzuki's normalization. -/
def xiShiftBoundaryFactorizationPhase
    {omega : ℝ} (homega : 0 ≤ omega) : ℂ :=
  (starRingEnd ℂ) (xiShiftInfiniteBoundaryQuotient homega I) /
    (starRingEnd ℂ) (suzukiCanonicalTheta omega I)

theorem norm_xiShiftBoundaryFactorizationPhase
    {omega : ℝ} (homega : 0 ≤ omega) :
    ‖xiShiftBoundaryFactorizationPhase homega‖ = 1 := by
  have hcross :=
    suzukiCanonicalTheta_cross_eq_infiniteGeneralizedSchurQuotient_cross
      homega (z := I) (w := I) (by simp) (by simp)
      (suzukiCanonicalE_I_ne_zero omega) (suzukiCanonicalE_I_ne_zero omega)
  change suzukiCanonicalTheta omega I *
      (starRingEnd ℂ) (suzukiCanonicalTheta omega I) =
    xiShiftInfiniteBoundaryQuotient homega I *
      (starRingEnd ℂ) (xiShiftInfiniteBoundaryQuotient homega I) at hcross
  have hnorm := congrArg norm hcross
  simp only [norm_mul, norm_conj] at hnorm
  have hnormEq : ‖suzukiCanonicalTheta omega I‖ =
      ‖xiShiftInfiniteBoundaryQuotient homega I‖ := by
    nlinarith [norm_nonneg (suzukiCanonicalTheta omega I),
      norm_nonneg (xiShiftInfiniteBoundaryQuotient homega I)]
  rw [xiShiftBoundaryFactorizationPhase, norm_div, norm_conj, norm_conj,
    ← hnormEq, div_self]
  exact norm_ne_zero_iff.mpr (suzukiCanonicalTheta_I_ne_zero omega)

/-- Interior quotient identity with its global phase fixed once and for all. -/
theorem suzukiCanonicalTheta_eq_phase_mul_infiniteBoundaryQuotient
    {omega : ℝ} (homega : 0 ≤ omega)
    {z : ℂ} (hz : 0 < z.im) (hEz : suzukiCanonicalE omega z ≠ 0) :
    suzukiCanonicalTheta omega z =
      xiShiftBoundaryFactorizationPhase homega *
        xiShiftInfiniteBoundaryQuotient homega z := by
  have hcross :=
    suzukiCanonicalTheta_cross_eq_infiniteGeneralizedSchurQuotient_cross
      homega hz (w := I) (by simp) hEz (suzukiCanonicalE_I_ne_zero omega)
  change suzukiCanonicalTheta omega z *
      (starRingEnd ℂ) (suzukiCanonicalTheta omega I) =
    xiShiftInfiniteBoundaryQuotient homega z *
      (starRingEnd ℂ) (xiShiftInfiniteBoundaryQuotient homega I) at hcross
  have htheta : (starRingEnd ℂ) (suzukiCanonicalTheta omega I) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (suzukiCanonicalTheta_I_ne_zero omega)
  rw [xiShiftBoundaryFactorizationPhase]
  calc
    suzukiCanonicalTheta omega z =
        (suzukiCanonicalTheta omega z *
          (starRingEnd ℂ) (suzukiCanonicalTheta omega I)) /
            (starRingEnd ℂ) (suzukiCanonicalTheta omega I) := by
      field_simp
    _ = (xiShiftInfiniteBoundaryQuotient homega z *
          (starRingEnd ℂ) (xiShiftInfiniteBoundaryQuotient homega I)) /
            (starRingEnd ℂ) (suzukiCanonicalTheta omega I) := by rw [hcross]
    _ = ((starRingEnd ℂ) (xiShiftInfiniteBoundaryQuotient homega I) /
          (starRingEnd ℂ) (suzukiCanonicalTheta omega I)) *
            xiShiftInfiniteBoundaryQuotient homega z := by ring

private theorem analyticOnNhd_diskMultiplier_comp_upperToDiskCayley
    (F : DiskMultiplier) :
    AnalyticOnNhd ℂ (fun z => F.fn (upperToDiskCayley z)) upperHalfPlaneSet := by
  have hF : AnalyticOnNhd ℂ F.fn (Metric.ball (0 : ℂ) 1) :=
    F.diff.analyticOnNhd Metric.isOpen_ball
  have hcomp := hF.comp analyticOnNhd_upperToDiskCayley_upperHalfPlane
    (fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]
      exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)
  simpa only [Function.comp_def] using hcomp

/-- Cross-multiplied complete factorization, valid even at upper-half-plane poles. -/
theorem suzukiCanonicalE_neg_mul_infinitePole_eq_phase_mul_numerator_mul_E
    {omega : ℝ} (homega : 0 ≤ omega) :
    Set.EqOn
      (fun z => suzukiCanonicalE omega (-z) *
        (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z))
      (fun z => xiShiftBoundaryFactorizationPhase homega *
        (xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z) *
          suzukiCanonicalE omega z)
      upperHalfPlaneSet := by
  let f : ℂ → ℂ := fun z => suzukiCanonicalE omega (-z) *
    (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z)
  let g : ℂ → ℂ := fun z => xiShiftBoundaryFactorizationPhase homega *
    (xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z) *
      suzukiCanonicalE omega z
  have hf : AnalyticOnNhd ℂ f upperHalfPlaneSet := by
    apply AnalyticOnNhd.mul
    · intro z hz
      simpa only [Function.comp_def] using
        ((differentiable_suzukiCanonicalE omega).analyticAt (-z)).comp
          (show AnalyticAt ℂ (fun u : ℂ => -u) z by fun_prop)
    · exact analyticOnNhd_diskMultiplier_comp_upperToDiskCayley
        (xiShiftPoleBlaschkeMultiplier homega)
  have hg : AnalyticOnNhd ℂ g upperHalfPlaneSet := by
    exact (analyticOnNhd_const.mul
      (analyticOnNhd_diskMultiplier_comp_upperToDiskCayley
        (xiShiftInfiniteSchurNumerator homega))).mul
      (fun z _ => (differentiable_suzukiCanonicalE omega).analyticAt z)
  have hEulerSubset : xiShiftEulerUpperSet omega ⊆ upperHalfPlaneSet := by
    intro z hz
    change 0 < z.im
    change 1 / 2 + omega < z.im at hz
    linarith
  have heqEuler : Set.EqOn f g (xiShiftEulerUpperSet omega) := by
    intro z hz
    have hE' : suzukiCanonicalE omega z ≠ 0 := by
      rw [suzukiCanonicalE]
      apply xi_ne_zero_of_one_lt_re
      change 1 / 2 + omega < z.im at hz
      simp only [Complex.sub_re, Complex.add_re, Complex.div_re,
        Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im]
      norm_num
      linarith
    have hext : xiShiftExtremeE omega z ≠ 0 := by
      intro hzero
      apply hE'
      rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
      ring
    have hB := xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
      homega (hEulerSubset hz) hext
    have htheta :=
      suzukiCanonicalTheta_eq_phase_mul_infiniteBoundaryQuotient
        homega (hEulerSubset hz) hE'
    dsimp [f, g]
    rw [suzukiCanonicalTheta_eq_E_neg_div_E] at htheta
    change suzukiCanonicalE omega (-z) / suzukiCanonicalE omega z =
      xiShiftBoundaryFactorizationPhase homega *
        ((xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z) /
          (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z)) at htheta
    field_simp [hE', hB] at htheta
    calc
      suzukiCanonicalE omega (-z) *
          (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z) =
        suzukiCanonicalE omega z * xiShiftBoundaryFactorizationPhase homega *
          (xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z) := htheta
      _ = xiShiftBoundaryFactorizationPhase homega *
          (xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z) *
            suzukiCanonicalE omega z := by ring
  obtain ⟨z₀, hz₀⟩ := xiShiftEulerUpperSet_nonempty omega
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg
    isPreconnected_upperHalfPlaneSet (hEulerSubset hz₀) ?_
  filter_upwards [(isOpen_xiShiftEulerUpperSet omega).mem_nhds hz₀] with z hz
  exact heqEuler hz

private theorem exists_common_diskMultiplierRadialBoundary_subseq_ae_real
    (A B : DiskMultiplier) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto
          (fun i => diskMultiplierRadialBoundaryFun (ns i) A (circleCayley x))
          atTop (𝓝 (diskMultiplierBoundaryFun A (circleCayley x))) ∧
        Tendsto
          (fun i => diskMultiplierRadialBoundaryFun (ns i) B (circleCayley x))
          atTop (𝓝 (diskMultiplierBoundaryFun B (circleCayley x))) := by
  obtain ⟨nsA, hnsA, haeA⟩ := exists_diskMultiplierRadialBoundary_subseq_ae A
  obtain ⟨nsB, hnsB, haeB⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono B hnsA
  let ns : ℕ → ℕ := fun i => nsA (nsB i)
  have hns : StrictMono ns := hnsA.comp hnsB
  have haeA' : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) A z)
        atTop (𝓝 (diskMultiplierBoundaryFun A z)) := by
    filter_upwards [haeA] with z hz
    exact hz.comp hnsB.tendsto_atTop
  have haePair : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) A z)
          atTop (𝓝 (diskMultiplierBoundaryFun A z)) ∧
        Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) B z)
          atTop (𝓝 (diskMultiplierBoundaryFun B z)) := by
    filter_upwards [haeA', haeB] with z hA hB
    exact ⟨hA, hB⟩
  have hqmp : Measure.QuasiMeasurePreserving circleCayley
      ((volume : Measure ℝ).withDensity (realDensity standardCauchyWeight))
      circleLebesgue :=
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving
  have haeWeighted := hqmp.ae haePair
  let P : ℝ → Prop := fun x =>
    Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) A (circleCayley x))
        atTop (𝓝 (diskMultiplierBoundaryFun A (circleCayley x))) ∧
      Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) B (circleCayley x))
        atTop (𝓝 (diskMultiplierBoundaryFun B (circleCayley x)))
  have haeWeightedEq : P =ᵐ[
      (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)]
      fun _ => True := by
    filter_upwards [haeWeighted] with x hx
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have haeVolumeEq : P =ᵐ[(volume : Measure ℝ)] fun _ => True :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mp haeWeightedEq
  refine ⟨ns, hns, ?_⟩
  filter_upwards [haeVolumeEq] with x hx
  change P x
  rw [hx]
  trivial

private theorem suzukiCanonicalTheta_boundary_eq_phase_mul_boundaryQuotient
    {omega : ℝ} (homega : 0 ≤ omega)
    {ns : ℕ → ℕ} (hns : StrictMono ns) {x : ℝ}
    (hA : Tendsto
      (fun i => diskMultiplierRadialBoundaryFun (ns i)
        (xiShiftInfiniteSchurNumerator homega) (circleCayley x))
      atTop (𝓝 (diskMultiplierBoundaryFun
        (xiShiftInfiniteSchurNumerator homega) (circleCayley x))))
    (hB : Tendsto
      (fun i => diskMultiplierRadialBoundaryFun (ns i)
        (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x))
      atTop (𝓝 (diskMultiplierBoundaryFun
        (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x))))
    (hE : suzukiCanonicalE omega (x : ℂ) ≠ 0)
    (hBne : diskMultiplierBoundaryFun
      (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x) ≠ 0) :
    suzukiCanonicalTheta omega (x : ℂ) =
      xiShiftBoundaryFactorizationPhase homega *
        diskMultiplierBoundaryFun
          (xiShiftInfiniteSchurNumerator homega) (circleCayley x) /
        diskMultiplierBoundaryFun
          (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x) := by
  let u : ℕ → ℂ := fun i =>
    ((hardyDiskAbelRadius (ns i) : ℝ) : ℂ) * realCayley x
  let z : ℕ → ℂ := fun i =>
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (u i)
  have huNorm (i : ℕ) : ‖u i‖ < 1 := by
    change ‖((hardyDiskAbelRadius (ns i) : ℝ) : ℂ) * realCayley x‖ < 1
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg (ns i)), norm_realCayley, mul_one]
    exact hardyDiskAbelRadius_lt_one (ns i)
  have huNe (i : ℕ) : u i ≠ 1 := by
    intro hi
    have hnorm := congrArg norm hi
    rw [norm_one] at hnorm
    exact (ne_of_lt (huNorm i)) hnorm
  have hu : Tendsto u atTop (𝓝 (realCayley x)) := by
    have hr : Tendsto (fun i => hardyDiskAbelRadius (ns i)) atTop (𝓝 (1 : ℝ)) :=
      (tendsto_hardyDiskAbelRadius.mono_right inf_le_left).comp hns.tendsto_atTop
    have hrc : Tendsto (fun i => ((hardyDiskAbelRadius (ns i) : ℝ) : ℂ))
        atTop (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa [u] using hrc.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => realCayley x)
        atTop (𝓝 (realCayley x)))
  have hrealCayleyNe : realCayley x ≠ 1 := by
    intro h
    rw [realCayley, div_eq_one_iff_eq (real_add_I_ne_zero x)] at h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hz : Tendsto z atTop (𝓝 (x : ℂ)) := by
    change Tendsto
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv ∘ u)
      atTop (𝓝 (x : ℂ))
    have ht := (differentiableAt_suzukiUpperCayleyInv
      hrealCayleyNe).continuousAt.tendsto.comp hu
    have hendpoint :
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (realCayley x) =
          (x : ℂ) :=
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley
        (real_add_I_ne_zero x)
    rw [hendpoint] at ht
    exact ht
  have hA' : Tendsto
      (fun i => (xiShiftInfiniteSchurNumerator homega).fn (u i))
      atTop (𝓝 (diskMultiplierBoundaryFun
        (xiShiftInfiniteSchurNumerator homega) (circleCayley x))) := by
    simpa [diskMultiplierRadialBoundaryFun, circleCayley_coe, u] using hA
  have hB' : Tendsto
      (fun i => (xiShiftPoleBlaschkeMultiplier homega).fn (u i))
      atTop (𝓝 (diskMultiplierBoundaryFun
        (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x))) := by
    simpa [diskMultiplierRadialBoundaryFun, circleCayley_coe, u] using hB
  have hEplus : Tendsto (fun i => suzukiCanonicalE omega (z i))
      atTop (𝓝 (suzukiCanonicalE omega (x : ℂ))) :=
    (differentiable_suzukiCanonicalE omega).continuous.continuousAt.tendsto.comp hz
  have hEneg : Tendsto (fun i => suzukiCanonicalE omega (-(z i)))
      atTop (𝓝 (suzukiCanonicalE omega (-(x : ℂ)))) :=
    (differentiable_suzukiCanonicalE omega).continuous.continuousAt.tendsto.comp hz.neg
  have hcross (i : ℕ) :
      suzukiCanonicalE omega (-(z i)) *
          (xiShiftPoleBlaschkeMultiplier homega).fn (u i) =
        xiShiftBoundaryFactorizationPhase homega *
          (xiShiftInfiniteSchurNumerator homega).fn (u i) *
            suzukiCanonicalE omega (z i) := by
    have hi : z i ∈ upperHalfPlaneSet := by
      change 0 < (z i).im
      exact GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one
        (huNorm i)
    have heq :=
      suzukiCanonicalE_neg_mul_infinitePole_eq_phase_mul_numerator_mul_E
        homega hi
    have hcayley : upperToDiskCayley (z i) = u i := by
      change upperToDiskCayley
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (u i)) = u i
      exact upperToDiskCayley_suzukiUpperCayleyInv (huNe i)
    change suzukiCanonicalE omega (-(z i)) *
        (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley (z i)) =
      xiShiftBoundaryFactorizationPhase homega *
        (xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley (z i)) *
          suzukiCanonicalE omega (z i) at heq
    rw [hcayley] at heq
    exact heq
  have hlimit :
      suzukiCanonicalE omega (-(x : ℂ)) *
          diskMultiplierBoundaryFun
            (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x) =
        xiShiftBoundaryFactorizationPhase homega *
          diskMultiplierBoundaryFun
            (xiShiftInfiniteSchurNumerator homega) (circleCayley x) *
            suzukiCanonicalE omega (x : ℂ) := by
    apply tendsto_nhds_unique (hEneg.mul hB')
    exact ((tendsto_const_nhds.mul hA').mul hEplus).congr'
      (Eventually.of_forall fun i => (hcross i).symm)
  rw [suzukiCanonicalTheta_eq_E_neg_div_E]
  field_simp [hE, hBne]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hlimit

/-- The actual patched shifted-Xi boundary is exactly the complete infinite disk quotient almost
everywhere; common numerator/denominator factors remain present on both sides and are not erased. -/
theorem suzukiShiftedXiBoundary_ae_eq_phase_mul_infiniteBoundaryQuotient
    {omega : ℝ} (homega : 0 ≤ omega) :
    suzukiShiftedXiBoundary omega =ᵐ[(volume : Measure ℝ)] fun x =>
      xiShiftBoundaryFactorizationPhase homega *
        diskMultiplierBoundaryFun
          (xiShiftInfiniteSchurNumerator homega) (circleCayley x) /
        diskMultiplierBoundaryFun
          (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x) := by
  obtain ⟨ns, hns, haeRadial⟩ :=
    exists_common_diskMultiplierRadialBoundary_subseq_ae_real
      (xiShiftInfiniteSchurNumerator homega)
      (xiShiftPoleBlaschkeMultiplier homega)
  have haeE : ∀ᵐ x : ℝ, suzukiCanonicalE omega (x : ℂ) ≠ 0 :=
    ae_iff.mpr (by
      simpa only [not_ne_iff] using volume_suzukiCanonicalE_real_zeroSet omega)
  have haeBnormCircle :
      (fun z => ‖diskMultiplierBoundaryFun
        (xiShiftPoleBlaschkeMultiplier homega) z‖) =ᵐ[circleLebesgue]
        fun _ => (1 : ℝ) :=
    ae_norm_diskMultiplierBoundaryFun_eq_one
      (xiShiftPoleBlaschkeMultiplier homega) rfl
      (xiShiftPoleBlaschkeMultiplier_isometry homega)
  have haeBnormWeighted := haeBnormCircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have haeBnorm :
      (fun x => ‖diskMultiplierBoundaryFun
        (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x)‖) =ᵐ[
          (volume : Measure ℝ)] fun _ => (1 : ℝ) :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mp haeBnormWeighted
  filter_upwards [suzukiShiftedXiBoundary_ae_eq_canonicalTheta omega,
    haeRadial, haeE, haeBnorm] with x htheta hradial hE hBnorm
  rw [htheta]
  apply suzukiCanonicalTheta_boundary_eq_phase_mul_boundaryQuotient
    homega hns hradial.1 hradial.2 hE
  intro hzero
  rw [hzero, norm_zero] at hBnorm
  norm_num at hBnorm

/-- Measurable-symbol form of the exact boundary factorization, matching the literal quotient
multiplier used by `diskBoundaryInnerQuotientLeakage`. -/
theorem suzukiShiftedXiBoundary_ae_eq_phase_mul_innerQuotientSymbol
    {omega : ℝ} (homega : 0 ≤ omega) :
    suzukiShiftedXiBoundary omega =ᵐ[(volume : Measure ℝ)] fun x =>
      xiShiftBoundaryFactorizationPhase homega *
        (diskInnerBoundarySymbol
          (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x))⁻¹ *
        diskMultiplierBoundarySymbol
          (xiShiftInfiniteSchurNumerator homega) (circleCayley x) := by
  have haeAcircle := diskMultiplierBoundarySymbol_ae
    (xiShiftInfiniteSchurNumerator homega)
  have haeBcircle := diskInnerBoundarySymbol_ae
    (xiShiftPoleBlaschkeMultiplier homega) rfl
    (xiShiftPoleBlaschkeMultiplier_isometry homega)
  have haeAweighted := haeAcircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have haeBweighted := haeBcircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have haeA := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp haeAweighted
  have haeB := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp haeBweighted
  filter_upwards [
    suzukiShiftedXiBoundary_ae_eq_phase_mul_infiniteBoundaryQuotient homega,
    haeA, haeB] with x hfactor hA hB
  change diskMultiplierBoundarySymbol
      (xiShiftInfiniteSchurNumerator homega) (circleCayley x) =
    diskMultiplierBoundaryFun
      (xiShiftInfiniteSchurNumerator homega) (circleCayley x) at hA
  change diskInnerBoundarySymbol
      (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x) =
    diskMultiplierBoundaryFun
      (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x) at hB
  rw [hfactor, hA, hB]
  simp only [div_eq_mul_inv]
  ring

/-- The complete shifted-Xi Schur numerator is itself inner: its exact boundary symbol is
unimodular almost everywhere.  This is forced by the literal unimodular Xi quotient, the
unimodular denominator, and the unit global phase, then transported back across the Cayley
measure equivalence. -/
theorem ae_norm_xiShiftInfiniteSchurNumerator_boundarySymbol_eq_one
    {omega : ℝ} (homega : 0 ≤ omega) :
    ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundarySymbol
        (xiShiftInfiniteSchurNumerator homega) z‖ = 1 := by
  let P : ℝ → Prop := fun x =>
    ‖diskMultiplierBoundarySymbol
      (xiShiftInfiniteSchurNumerator homega) (circleCayley x)‖ = 1
  have hvolume : ∀ᵐ x ∂(volume : Measure ℝ), P x := by
    filter_upwards [
      suzukiShiftedXiBoundary_ae_eq_phase_mul_innerQuotientSymbol homega]
      with x hfactor
    have hnorm := congrArg norm hfactor
    simp only [norm_suzukiShiftedXiBoundary,
      norm_mul, norm_mul, norm_inv,
      norm_xiShiftBoundaryFactorizationPhase homega,
      norm_diskInnerBoundarySymbol, inv_one, one_mul] at hnorm
    simpa using hnorm.symm
  have hvolumeEq : P =ᵐ[(volume : Measure ℝ)] fun _ => True := by
    filter_upwards [hvolume] with x hx
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have hweightedEq : P =ᵐ[
      (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)]
      fun _ => True :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mpr hvolumeEq
  have hweighted : ∀ᵐ x ∂
      (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight), P x := by
    filter_upwards [hweightedEq] with x hx
    rw [hx]
    trivial
  rw [← circleCayley_weighted_measurePreserving.map_eq]
  apply (MeasureTheory.ae_map_iff
    continuous_circleCayley.measurable.aemeasurable
    (measurableSet_eq_fun
      (measurable_diskMultiplierBoundarySymbol
        (xiShiftInfiniteSchurNumerator homega)).norm measurable_const)).2
  exact hweighted

/-- Hardy multiplication by the complete shifted-Xi numerator preserves norm. -/
theorem xiShiftInfiniteSchurNumerator_isometry
    {omega : ℝ} (homega : 0 ≤ omega) :
    HardyMultiplierIsometry (xiShiftInfiniteSchurNumerator homega) := by
  apply hardyMultiplierIsometry_of_ae_norm_boundary_eq_one
  filter_upwards [diskMultiplierBoundarySymbol_ae
      (xiShiftInfiniteSchurNumerator homega),
    ae_norm_xiShiftInfiniteSchurNumerator_boundarySymbol_eq_one homega]
    with z hsymbol hnorm
  rwa [← hsymbol]

/-- Literal whole-line shifted-Xi multiplication is the complete cancellation-aware quotient
multiplier, up to the unique harmless unimodular phase. -/
theorem suzukiShiftedXiBoundaryMul_eq_phase_smul_innerQuotientMul
    {omega : ℝ} (homega : 0 ≤ omega) :
    (suzukiShiftedXiBoundaryMulUnitary omega).toLinearIsometry.toContinuousLinearMap =
      xiShiftBoundaryFactorizationPhase homega •
        diskBoundaryInnerQuotientMul
          (xiShiftInfiniteSchurNumerator homega)
          (xiShiftPoleBlaschkeMultiplier homega) rfl
          (xiShiftPoleBlaschkeMultiplier_isometry homega) := by
  let Q : RealLineL2 →L[ℂ] RealLineL2 :=
    diskBoundaryInnerQuotientMul
      (xiShiftInfiniteSchurNumerator homega)
      (xiShiftPoleBlaschkeMultiplier homega) rfl
      (xiShiftPoleBlaschkeMultiplier_isometry homega)
  change (suzukiShiftedXiBoundaryMulUnitary omega).toLinearIsometry.toContinuousLinearMap =
    xiShiftBoundaryFactorizationPhase homega • Q
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hactual := suzukiShiftedXiBoundaryMulUnitary_ae omega f
  have hquotient : Q f =ᵐ[(volume : Measure ℝ)] fun x =>
      (diskInnerBoundarySymbol
        (xiShiftPoleBlaschkeMultiplier homega) (circleCayley x))⁻¹ *
      diskMultiplierBoundarySymbol
        (xiShiftInfiniteSchurNumerator homega) (circleCayley x) * f x := by
    simpa only [Q] using diskBoundaryInnerQuotientMul_ae
      (xiShiftInfiniteSchurNumerator homega)
      (xiShiftPoleBlaschkeMultiplier homega) rfl
      (xiShiftPoleBlaschkeMultiplier_isometry homega) f
  have hsmul := Lp.coeFn_smul (xiShiftBoundaryFactorizationPhase homega) (Q f)
  filter_upwards [hactual,
    suzukiShiftedXiBoundary_ae_eq_phase_mul_innerQuotientSymbol homega,
    hquotient, hsmul] with x hactual hfactor hquotient hsmul
  change (((suzukiShiftedXiBoundaryMulUnitary omega f : RealLineL2) : ℝ → ℂ) x) =
    ((((xiShiftBoundaryFactorizationPhase homega • Q) f : RealLineL2) : ℝ → ℂ) x)
  rw [hactual, hfactor]
  change _ = (((xiShiftBoundaryFactorizationPhase homega • Q f : RealLineL2) :
    ℝ → ℂ) x)
  rw [hsmul]
  change _ = xiShiftBoundaryFactorizationPhase homega *
    (((Q f : RealLineL2) : ℝ → ℂ) x)
  rw [hquotient]
  ring

/-- Exact actual anti-causal leakage factorization through the complete disk quotient. -/
theorem suzukiShiftedXiHardyLeakage_eq_phase_smul_innerQuotientLeakage
    {omega : ℝ} (homega : 0 ≤ omega) :
    suzukiShiftedXiHardyLeakage omega =
      xiShiftBoundaryFactorizationPhase homega •
        diskBoundaryInnerQuotientLeakage
          (xiShiftInfiniteSchurNumerator homega)
          (xiShiftPoleBlaschkeMultiplier homega) rfl
          (xiShiftPoleBlaschkeMultiplier_isometry homega) := by
  rw [suzukiShiftedXiHardyLeakage,
    suzukiShiftedXiBoundaryMul_eq_phase_smul_innerQuotientMul homega,
    hardyLeakage_smul]
  rfl

/-- The actual shifted-Xi anti-causal compression and the complete disk model-space core have
identical operator norm. -/
theorem norm_suzukiShiftedXiHardyLeakage_eq_infiniteLeakageCore
    {omega : ℝ} (homega : 0 ≤ omega) :
    ‖suzukiShiftedXiHardyLeakage omega‖ =
      ‖xiShiftInfiniteLeakageCore homega‖ := by
  rw [suzukiShiftedXiHardyLeakage_eq_phase_smul_innerQuotientLeakage homega,
    norm_smul_continuousLinearMap_of_norm_eq_one _ _
      (norm_xiShiftBoundaryFactorizationPhase homega),
    norm_diskBoundaryInnerQuotientLeakage_eq_modelSpaceLeakageCore]
  rfl

/-- Exact local crossing modulus inside the literal shifted-Xi numerator divisor.  The selected
numerator zero and its paired pole are a horizontal Blaschke pair with half-separation `omega` and
height `(I * xiSpectralPoint q).re`. -/
theorem norm_normalizedBlaschkeFactor_xiShift_pair
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    ‖normalizedBlaschkeFactor
        (xiShiftNumeratorDiskCoordinate omega q)
        (xiShiftPoleDiskCoordinate omega q)‖ =
      omega / (I * xiSpectralPoint q.1).re := by
  let a : ℝ := (I * xiSpectralPoint q.1).re
  let gamma : ℝ := (xiSpectralPoint q.1).re
  have ha : 0 < a := lt_of_le_of_lt homega q.2
  have hnum : xiShiftNumeratorCoordinate omega q =
      ((-gamma : ℝ) : ℂ) + ((a + omega : ℝ) : ℂ) * I := by
    rw [xiShiftNumeratorCoordinate]
    apply Complex.ext <;> simp [a, gamma, mul_re]
  have hpole : xiShiftPoleCoordinate omega q =
      ((-gamma : ℝ) : ℂ) + ((a - omega : ℝ) : ℂ) * I := by
    rw [xiShiftPoleCoordinate]
    apply Complex.ext <;> simp [a, gamma, mul_re]
  change ‖normalizedBlaschkeFactor
      (upperToDiskCayley (xiShiftNumeratorCoordinate omega q))
      (upperToDiskCayley (xiShiftPoleCoordinate omega q))‖ = _
  rw [normalizedBlaschkeFactor_upperToDiskCayley
      (xiShiftNumeratorCoordinate_im_pos homega q)
      (xiShiftPoleCoordinate_im_pos omega q),
    norm_mul, norm_normalizedCayleyBlaschkeUnit_eq_one
      (xiShiftNumeratorCoordinate_im_pos homega q), one_mul,
    hnum, hpole]
  have hlocal := norm_upperHalfPlaneBlaschkeFactor_horizontalPair
    (a := a) (omega := omega) (gamma := gamma) ha homega
  simpa [a] using hlocal

/-- Actual shifted-Xi numerator after removing `m` copies of one selected crossing Blaschke
factor.  This quotient is the invariant residual-divisor value used by the tame-layer condition. -/
def xiShiftCrossingResidualValue
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) (m : ℕ) : ℂ :=
  (xiShiftInfiniteSchurNumerator homega).fn
      (xiShiftPoleDiskCoordinate omega q) /
    normalizedBlaschkeFactor
      (xiShiftNumeratorDiskCoordinate omega q)
      (xiShiftPoleDiskCoordinate omega q) ^ m

/-- Exact multiplicity-`m` factorization of the actual numerator value at a crossing pole. -/
theorem norm_xiShiftInfiniteSchurNumerator_pole_eq_crossing_mul_residual
    {omega : ℝ} (homega : 0 < omega)
    (q : XiShiftRightZeroCopy omega) (m : ℕ) :
    ‖(xiShiftInfiniteSchurNumerator homega.le).fn
        (xiShiftPoleDiskCoordinate omega q)‖ =
      (omega / (I * xiSpectralPoint q.1).re) ^ m *
        ‖xiShiftCrossingResidualValue homega.le q m‖ := by
  let u : ℂ := normalizedBlaschkeFactor
    (xiShiftNumeratorDiskCoordinate omega q)
    (xiShiftPoleDiskCoordinate omega q)
  have huNorm : ‖u‖ = omega / (I * xiSpectralPoint q.1).re :=
    norm_normalizedBlaschkeFactor_xiShift_pair homega.le q
  have ha : 0 < (I * xiSpectralPoint q.1).re :=
    lt_trans homega q.2
  have hu : u ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [huNorm]
    exact ne_of_gt (div_pos homega ha)
  have hfactor :
      (xiShiftInfiniteSchurNumerator homega.le).fn
          (xiShiftPoleDiskCoordinate omega q) =
        u ^ m * xiShiftCrossingResidualValue homega.le q m := by
    rw [xiShiftCrossingResidualValue]
    exact (mul_div_cancel₀ _ (pow_ne_zero m hu)).symm
  rw [hfactor, norm_mul, norm_pow, huNorm]

/-- The isolated/tame layer condition implies the exact theorem-B numerator-value limit. -/
theorem tendsto_norm_xiShiftInfiniteSchurNumerator_pole_one_of_tameCrossing
    {ι : Type*} {l : Filter ι} (omega : ι → ℝ)
    (homega : ∀ i, 0 < omega i)
    (q : ∀ i, XiShiftRightZeroCopy (omega i)) (m : ℕ)
    (hratio : Tendsto (fun i =>
      omega i / (I * xiSpectralPoint (q i).1).re) l (𝓝 1))
    (hresidual : Tendsto (fun i =>
      ‖xiShiftCrossingResidualValue (homega i).le (q i) m‖) l (𝓝 1)) :
    Tendsto (fun i =>
      ‖(xiShiftInfiniteSchurNumerator (homega i).le).fn
        (xiShiftPoleDiskCoordinate (omega i) (q i))‖) l (𝓝 1) := by
  convert (hratio.pow m).mul hresidual using 1
  · funext i
    exact norm_xiShiftInfiniteSchurNumerator_pole_eq_crossing_mul_residual
      (homega i) (q i) m
  · simp

/-- Exact horizontal-ray lower bound for the full-divisor projected leakage. -/
theorem lambda_pow_mul_residual_le_norm_xiShiftInfiniteLeakageCore
    {omega lambda : ℝ} (homega : 0 < omega)
    (q : XiShiftRightZeroCopy omega) (m : ℕ)
    (hray : omega = lambda * (I * xiSpectralPoint q.1).re) :
    lambda ^ m * ‖xiShiftCrossingResidualValue homega.le q m‖ ≤
      ‖xiShiftInfiniteLeakageCore homega.le‖ := by
  have hnum := norm_xiShiftInfiniteSchurNumerator_pole_le_leakage homega.le q
  rw [norm_xiShiftInfiniteSchurNumerator_pole_eq_crossing_mul_residual
    homega q m] at hnum
  have ha : 0 < (I * xiSpectralPoint q.1).re := lt_trans homega q.2
  have hratio : omega / (I * xiSpectralPoint q.1).re = lambda := by
    calc
      omega / (I * xiSpectralPoint q.1).re =
          (lambda * (I * xiSpectralPoint q.1).re) /
            (I * xiSpectralPoint q.1).re :=
        congrArg (fun x : ℝ => x / (I * xiSpectralPoint q.1).re) hray
      _ = lambda := by field_simp
  rwa [hratio] at hnum

/-- Exact theorem-B norm squeeze for the stated real-line leakage operator. -/
theorem tendsto_norm_suzukiShiftedXiHardyLeakage_one_of_poleValue
    {ι : Type*} {l : Filter ι} (omega : ι → ℝ)
    (homega : ∀ i, 0 ≤ omega i)
    (q : ∀ i, XiShiftRightZeroCopy (omega i))
    (hnum : Tendsto (fun i =>
      ‖(xiShiftInfiniteSchurNumerator (homega i)).fn
        (xiShiftPoleDiskCoordinate (omega i) (q i))‖) l (𝓝 1)) :
    Tendsto (fun i => ‖suzukiShiftedXiHardyLeakage (omega i)‖) l (𝓝 1) := by
  have hcore :=
    tendsto_norm_xiShiftInfiniteLeakageCore_one_of_poleValue omega homega q hnum
  convert hcore using 1
  funext i
  exact norm_suzukiShiftedXiHardyLeakage_eq_infiniteLeakageCore (homega i)

/-- Full norm singularity for the stated anti-causal operator at an isolated multiplicity-`m`
layer with tame residual divisor. -/
theorem tendsto_norm_suzukiShiftedXiHardyLeakage_one_of_tameCrossing
    {ι : Type*} {l : Filter ι} (omega : ι → ℝ)
    (homega : ∀ i, 0 < omega i)
    (q : ∀ i, XiShiftRightZeroCopy (omega i)) (m : ℕ)
    (hratio : Tendsto (fun i =>
      omega i / (I * xiSpectralPoint (q i).1).re) l (𝓝 1))
    (hresidual : Tendsto (fun i =>
      ‖xiShiftCrossingResidualValue (homega i).le (q i) m‖) l (𝓝 1)) :
    Tendsto (fun i => ‖suzukiShiftedXiHardyLeakage (omega i)‖) l (𝓝 1) := by
  apply tendsto_norm_suzukiShiftedXiHardyLeakage_one_of_poleValue
    omega (fun i => (homega i).le) q
  exact tendsto_norm_xiShiftInfiniteSchurNumerator_pole_one_of_tameCrossing
    omega homega q m hratio hresidual

/-- Quantitative theorem-B ray law for the actual shifted-Xi anti-causal leakage. -/
theorem lambda_pow_mul_residual_le_norm_suzukiShiftedXiHardyLeakage
    {omega lambda : ℝ} (homega : 0 < omega)
    (q : XiShiftRightZeroCopy omega) (m : ℕ)
    (hray : omega = lambda * (I * xiSpectralPoint q.1).re) :
    lambda ^ m * ‖xiShiftCrossingResidualValue homega.le q m‖ ≤
      ‖suzukiShiftedXiHardyLeakage omega‖ := by
  rw [norm_suzukiShiftedXiHardyLeakage_eq_infiniteLeakageCore homega.le]
  exact lambda_pow_mul_residual_le_norm_xiShiftInfiniteLeakageCore
    homega q m hray

private theorem xiShiftInfiniteLeakageCore_eq_zero_of_isEmpty
    {omega : ℝ} (homega : 0 ≤ omega)
    [IsEmpty (XiShiftRightZeroCopy omega)] :
    xiShiftInfiniteLeakageCore homega = 0 := by
  let B := xiShiftPoleBlaschkeMultiplier homega
  have hBfn : B.fn = fun _ => 1 :=
    xiShiftPoleBlaschkeMultiplier_fn_eq_one_of_isEmpty homega
  have hK : hardyMultiplierModelSpace B = ⊥ := by
    rw [hardyMultiplierModelSpace]
    have hrange : LinearMap.range ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk) = ⊤ := by
      apply top_unique
      intro f _
      refine ⟨f, ?_⟩
      calc
        hardyMul B f = hardyMul DiskMultiplier.one f := by
          apply hardyMul_congr
          intro z hz
          rw [hBfn]
          rfl
        _ = f := hardyMul_one f
    rw [hrange]
    ext x
    simp
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  have hmem := (xiShiftInfiniteLeakageCore homega f).property
  let y : HardyDisk := (xiShiftInfiniteLeakageCore homega f : HardyDisk)
  have hy : y ∈ hardyMultiplierModelSpace B := hmem
  have hy₀ : y ∈ (⊥ : Submodule ℂ HardyDisk) := by
    rw [← hK]
    exact hy
  change y = 0
  exact hy₀

/-- Pole-free side of theorem B: if no shifted-Xi pole copy remains, the stated anti-causal
leakage operator vanishes identically. -/
theorem suzukiShiftedXiHardyLeakage_eq_zero_of_isEmpty
    {omega : ℝ} (homega : 0 ≤ omega)
    [IsEmpty (XiShiftRightZeroCopy omega)] :
    suzukiShiftedXiHardyLeakage omega = 0 := by
  rw [suzukiShiftedXiHardyLeakage_eq_phase_smul_innerQuotientLeakage homega,
    diskBoundaryInnerQuotientLeakage_eq_modelEmbedding_comp]
  change xiShiftBoundaryFactorizationPhase homega •
    (diskBoundaryModelEmbedding
      (xiShiftPoleBlaschkeMultiplier homega) rfl
      (xiShiftPoleBlaschkeMultiplier_isometry homega)).comp
      ((xiShiftInfiniteLeakageCore homega).comp hardyLineDiskCayleyCLM) = 0
  rw [xiShiftInfiniteLeakageCore_eq_zero_of_isEmpty homega]
  apply ContinuousLinearMap.ext
  intro f
  change xiShiftBoundaryFactorizationPhase homega •
    diskBoundaryModelEmbedding
      (xiShiftPoleBlaschkeMultiplier homega) rfl
      (xiShiftPoleBlaschkeMultiplier_isometry homega) 0 = 0
  rw [map_zero, smul_zero]

/-- **Exact cancellation-aware shifted-Xi leakage rank law.**  At every nonnegative shift and
every finite rank level, the literal anti-causal boundary compression has rank at least `r`
exactly when the full pole model space modulo the complete numerator-adjoint cancellation kernel
has `r` independent directions.  This includes finite rank, infinite rank, and exceptional common
factors without a genericity assumption. -/
theorem suzukiShiftedXiHardyLeakage_rankAtLeast_iff_uncancelledDivisorQuotient
    {omega : ℝ} (homega : 0 ≤ omega) (r : ℕ) :
    UpperHardyOperatorRankAtLeast
        (suzukiShiftedXiHardyLeakage omega) r ↔
      HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega) r := by
  have hphase : xiShiftBoundaryFactorizationPhase homega ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_xiShiftBoundaryFactorizationPhase homega]
    norm_num
  rw [suzukiShiftedXiHardyLeakage_eq_phase_smul_innerQuotientLeakage homega]
  change ContinuousLinearMapRankAtLeast
      (xiShiftBoundaryFactorizationPhase homega •
        diskBoundaryInnerQuotientLeakage
          (xiShiftInfiniteSchurNumerator homega)
          (xiShiftPoleBlaschkeMultiplier homega) rfl
          (xiShiftPoleBlaschkeMultiplier_isometry homega)) r ↔ _
  rw [continuousLinearMapRankAtLeast_smul_iff _ _ hphase r]
  exact diskBoundaryInnerQuotientLeakage_rankAtLeast_iff_uncancelledQuotient
    (xiShiftInfiniteSchurNumerator homega)
    (xiShiftPoleBlaschkeMultiplier homega) rfl
    (xiShiftPoleBlaschkeMultiplier_isometry homega) r

/-- Equivalent exact negative-index profile of the literal shifted-Xi boundary Gram kernel. -/
theorem suzukiShiftedXiBoundaryNegativeGramKernel_negativeDimension_iff_uncancelledDivisorQuotient
    {omega : ℝ} (homega : 0 ≤ omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          suzukiShiftedXiBoundaryNegativeGramKernel omega z.1 w.1) r ↔
      HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega) r := by
  rw [suzukiShiftedXiBoundaryNegativeGramKernel_negativeDimension_iff_rankAtLeast,
    suzukiShiftedXiHardyLeakage_rankAtLeast_iff_uncancelledDivisorQuotient homega]

end
end RHTower
