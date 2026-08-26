import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity
import GaloisForLFunctions.HTGeometry.DiskMultiplierBoundary
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.CircleRieszFischerFourier
import GaloisForLFunctions.HTGeometry.BoundedRealHerglotz

/-!
# Local gluing of opposite Hardy traces across a circle arc

This module realizes the normalized Cauchy transform of arbitrary circle `L²` data, proves its
inside/outside formulas on analytic and anti-analytic Hardy traces, and gives an exact edge-gluing
theorem. If an interior Hardy trace agrees almost everywhere on an arc with the conjugate trace of
a zero-constant-term Hardy function, one holomorphic germ crosses the arc and realizes both the
interior function and its reciprocal-conjugate exterior reflection.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def hardyCauchyKernelMultiplier (a : ℂ) (ha : ‖a‖ < 1) : DiskMultiplier where
  fn := fun z => (1 - (starRingEnd ℂ) a * z)⁻¹
  diff := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.inv
    · fun_prop
    · intro hzero
      have hnorm : ‖(starRingEnd ℂ) a * z‖ < 1 := by
        rw [norm_mul, RCLike.norm_conj]
        have hz' : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
        nlinarith [norm_nonneg a, norm_nonneg z]
      rw [(sub_eq_zero.mp hzero).symm] at hnorm
      norm_num at hnorm
  bd := (1 - ‖a‖)⁻¹
  bd_nonneg := inv_nonneg.mpr (sub_nonneg.mpr ha.le)
  bd_le := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
    have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := by
      intro hzero
      have hnorm : ‖(starRingEnd ℂ) a * z‖ < 1 := by
        rw [norm_mul, RCLike.norm_conj]
        nlinarith [norm_nonneg a, norm_nonneg z]
      rw [(sub_eq_zero.mp hzero).symm] at hnorm
      norm_num at hnorm
    rw [norm_inv]
    apply (inv_le_inv₀ (norm_pos_iff.mpr hden) (sub_pos.mpr ha)).2
    calc
      1 - ‖a‖ ≤ 1 - ‖a‖ * ‖z‖ := by
        have hzle : ‖z‖ ≤ 1 := hz'.le
        nlinarith [norm_nonneg a]
      _ = ‖(1 : ℂ)‖ - ‖(starRingEnd ℂ) a * z‖ := by
        rw [norm_one, norm_mul, RCLike.norm_conj]
      _ ≤ ‖1 - (starRingEnd ℂ) a * z‖ := norm_sub_norm_le _ _

theorem hardyOf_hardyCauchyKernelMultiplier (a : ℂ) (ha : ‖a‖ < 1) :
    hardyOf (hardyCauchyKernelMultiplier a ha) = hardyKernel ha := by
  apply hardyDisk_ext
  intro z hz
  rw [hardyFun_hardyOf (hardyCauchyKernelMultiplier a ha) hz,
    hardyFun_hardyKernel hz ha]
  rfl

theorem diskMultiplierBoundaryFun_hardyCauchyKernelMultiplier_ae
    (a : ℂ) (ha : ‖a‖ < 1) :
    diskMultiplierBoundaryFun (hardyCauchyKernelMultiplier a ha) =ᵐ[circleLebesgue]
      fun ζ : Circle => (1 - (starRingEnd ℂ) a * (ζ : ℂ))⁻¹ := by
  let φ := hardyCauchyKernelMultiplier a ha
  obtain ⟨ns, hns, hboundary⟩ := exists_diskMultiplierRadialBoundary_subseq_ae φ
  filter_upwards [hboundary] with ζ hζ
  have hr : Tendsto (fun i => (hardyDiskAbelRadius (ns i) : ℂ)) atTop (nhds 1) := by
    exact ((Complex.continuous_ofReal.tendsto 1).comp
      (tendsto_hardyDiskAbelRadius.mono_right inf_le_left)).comp hns.tendsto_atTop
  have harg : Tendsto
      (fun i => (hardyDiskAbelRadius (ns i) : ℂ) * (ζ : ℂ)) atTop (nhds (ζ : ℂ)) := by
    simpa using hr.mul tendsto_const_nhds
  have hden : 1 - (starRingEnd ℂ) a * (ζ : ℂ) ≠ 0 := by
    intro hzero
    have heq := sub_eq_zero.mp hzero
    have hnorm := congrArg norm heq
    rw [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one, norm_one] at hnorm
    linarith
  have hlim : Tendsto
      (fun i => diskMultiplierRadialBoundaryFun (ns i) φ ζ) atTop
      (nhds ((1 - (starRingEnd ℂ) a * (ζ : ℂ))⁻¹)) := by
    change Tendsto
      (fun i => (1 - (starRingEnd ℂ) a *
        ((hardyDiskAbelRadius (ns i) : ℂ) * (ζ : ℂ)))⁻¹) atTop _
    exact (((tendsto_const_nhds.sub (tendsto_const_nhds.mul harg)).inv₀ hden))
  exact tendsto_nhds_unique hζ hlim

theorem hardyDiskBoundary_hardyKernel_coe_ae (a : ℂ) (ha : ‖a‖ < 1) :
    ⇑(hardyDiskBoundary (hardyKernel ha)) =ᵐ[circleLebesgue]
      fun ζ : Circle => (1 - (starRingEnd ℂ) a * (ζ : ℂ))⁻¹ := by
  rw [← hardyOf_hardyCauchyKernelMultiplier a ha]
  exact diskMultiplierBoundaryFun_hardyCauchyKernelMultiplier_ae a ha

/-- Normalized circle Cauchy transform of an `L²` boundary vector. -/
def circleHardyCauchyTransform
    (f : Lp ℂ 2 circleLebesgue) (z : ℂ) : ℂ :=
  ∫ ζ : Circle, f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) ∂circleLebesgue

theorem circleHardyCauchyTransform_eq_inner
    (f : Lp ℂ 2 circleLebesgue) {z : ℂ} (hz : ‖z‖ < 1) :
    circleHardyCauchyTransform f z =
      inner ℂ (hardyDiskBoundary (hardyKernel hz)) f := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hardyDiskBoundary_hardyKernel_coe_ae z hz] with ζ hζ
  rw [hζ, RCLike.inner_apply]
  have hden : (ζ : ℂ) - z ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    have := congrArg norm heq
    rw [Circle.norm_coe] at this
    linarith
  change f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) =
    f ζ * (starRingEnd ℂ) ((1 - (starRingEnd ℂ) z * (ζ : ℂ))⁻¹)
  congr 1
  rw [map_inv₀, map_sub, map_mul, map_one, starRingEnd_self_apply]
  have hunit : (starRingEnd ℂ) (ζ : ℂ) = ((ζ : ℂ))⁻¹ := by
    exact (Complex.inv_eq_conj (Circle.norm_coe ζ)).symm
  rw [hunit]
  field_simp

theorem circleHardyCauchyTransform_hardyDiskBoundary
    (f : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    circleHardyCauchyTransform (hardyDiskBoundary f) z = hardyFun f z := by
  rw [circleHardyCauchyTransform_eq_inner _ hz,
    hardyDiskBoundary.inner_map_map,
    inner_hardyKernel hz]

theorem inner_hardyDiskBoundary_circleLpConj_hardyDiskBoundary
    (f g : HardyDisk) :
    inner ℂ (hardyDiskBoundary f) (circleLpConj (hardyDiskBoundary g)) =
      (starRingEnd ℂ) (f 0) * (starRingEnd ℂ) (g 0) := by
  let U := circleLpAddCircleLinearIsometryEquiv
  let V :
      Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) ≃ₗᵢ[ℂ]
        lp (fun _ : ℤ => ℂ) 2 := fourierBasis.repr
  calc
    inner ℂ (hardyDiskBoundary f) (circleLpConj (hardyDiskBoundary g)) =
        inner ℂ (U (hardyDiskBoundary f))
          (U (circleLpConj (hardyDiskBoundary g))) :=
      (U.inner_map_map _ _).symm
    _ = inner ℂ (V (U (hardyDiskBoundary f)))
          (V (U (circleLpConj (hardyDiskBoundary g)))) :=
      (V.inner_map_map _ _).symm
    _ = inner ℂ
          (nonnegativeIntExtensionLinearIsometry f)
          (V (U (circleLpConj (hardyDiskBoundary g)))) := by
      congr 1
      simp [V, U, hardyDiskBoundary]
    _ = ∑' k : ℤ,
          (starRingEnd ℂ) (nonnegativeIntExtension f k) *
            (starRingEnd ℂ) (nonnegativeIntExtension g (-k)) := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro k
      rw [RCLike.inner_apply]
      have hy : V (U (circleLpConj (hardyDiskBoundary g))) k =
          (starRingEnd ℂ) (nonnegativeIntExtension g (-k)) := by
        rw [HilbertBasis.repr_apply_apply]
        rw [show fourierBasis k = U (circleZMonomialLp circleLebesgue k) by
          simpa [U, circleLpAddCircleLinearIsometryEquiv] using
            (circleLpToAddCircleLinearIsometry_circleZMonomial k).symm]
        rw [U.inner_map_map, circleZMonomialLp_inner_circleLpConj,
          hardyDiskBoundary_apply,
          circleZMonomialLp_inner_circleRieszFischerOfNat]
      rw [hy]
      rw [nonnegativeIntExtensionLinearIsometry_apply]
      ring
    _ = (starRingEnd ℂ) (f 0) * (starRingEnd ℂ) (g 0) := by
      rw [tsum_eq_single 0]
      · change (starRingEnd ℂ) (f 0) * (starRingEnd ℂ) (g 0) = _
        rfl
      · intro k hk
        cases k with
        | ofNat n =>
            cases n with
            | zero => exact (hk rfl).elim
            | succ n =>
                rw [show -(Int.ofNat (n + 1)) = Int.negSucc n by
                  simp [Int.negSucc_eq]]
                simp [nonnegativeIntExtension]
        | negSucc n => simp [nonnegativeIntExtension]

theorem circleHardyCauchyTransform_circleLpConj_hardyDiskBoundary
    (f : HardyDisk) (hf0 : f 0 = 0) {z : ℂ} (hz : ‖z‖ < 1) :
    circleHardyCauchyTransform (circleLpConj (hardyDiskBoundary f)) z = 0 := by
  rw [circleHardyCauchyTransform_eq_inner _ hz,
    inner_hardyDiskBoundary_circleLpConj_hardyDiskBoundary]
  simp [hf0]

theorem circleLpConj_circleLpConj (f : Lp ℂ 2 circleLebesgue) :
    circleLpConj (circleLpConj f) = f := by
  apply Lp.ext
  filter_upwards [circleLpConj_coeFn_ae (circleLpConj f),
    circleLpConj_coeFn_ae f] with ζ houter hinner
  rw [houter, hinner]
  simp

theorem integral_hardyDiskBoundary (f : HardyDisk) :
    (∫ ζ : Circle, (hardyDiskBoundary f) ζ ∂circleLebesgue) = f 0 := by
  have h := circleZMonomialLp_inner_circleRieszFischerOfNat
    (f : ℕ → ℂ) (lp.memℓp f) (0 : ℤ)
  rw [circleZMonomialLp_inner] at h
  simpa [hardyDiskBoundary_apply, nonnegativeIntExtension] using h

theorem integrable_circleLp_mul_continuous
    (f : Lp ℂ 2 circleLebesgue) (K : Circle → ℂ) (hK : Continuous K) :
    Integrable (fun ζ : Circle => f ζ * K ζ) circleLebesgue := by
  let Kc : C(Circle, ℂ) := ⟨K, hK⟩
  exact ((Lp.memLp f).integrable one_le_two).mul_bdd hK.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => by
      simpa [Kc] using ContinuousMap.norm_coe_le_norm Kc ζ)

theorem circleHardyCauchyTransform_exterior_relation
    (f : Lp ℂ 2 circleLebesgue) {z : ℂ} (hz : 1 < ‖z‖) :
    circleHardyCauchyTransform f z =
      (∫ ζ : Circle, f ζ ∂circleLebesgue) -
        (starRingEnd ℂ)
          (circleHardyCauchyTransform (circleLpConj f)
            ((starRingEnd ℂ z)⁻¹)) := by
  have hw : ‖(starRingEnd ℂ z)⁻¹‖ < 1 := by
    rw [norm_inv, RCLike.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  have hkernel : Continuous fun ζ : Circle =>
      (ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹) := by
    apply Continuous.div continuous_subtype_val
      (continuous_subtype_val.sub continuous_const)
    intro ζ
    apply sub_ne_zero.mpr
    intro heq
    have hnorm := congrArg norm heq
    rw [Circle.norm_coe] at hnorm
    linarith
  have hB : Integrable (fun ζ : Circle =>
      (circleLpConj f) ζ *
        ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹))) circleLebesgue :=
    integrable_circleLp_mul_continuous _ _ hkernel
  rw [circleHardyCauchyTransform, circleHardyCauchyTransform]
  calc
    (∫ ζ : Circle, f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) ∂circleLebesgue) =
        ∫ ζ : Circle, f ζ - (starRingEnd ℂ)
          ((circleLpConj f) ζ *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹)))
          ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards [circleLpConj_coeFn_ae f] with ζ hζ
      rw [hζ]
      have hζ0 : (ζ : ℂ) ≠ 0 := by simp
      have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0, norm_zero] at hz
        linarith
      have hden1 : (ζ : ℂ) - z ≠ 0 := by
        intro hzero
        have heq := sub_eq_zero.mp hzero
        have hnorm := congrArg norm heq
        rw [Circle.norm_coe] at hnorm
        linarith
      have hden2 : (ζ : ℂ) - (starRingEnd ℂ z)⁻¹ ≠ 0 := by
        intro hzero
        have heq := sub_eq_zero.mp hzero
        have hnorm := congrArg norm heq
        rw [Circle.norm_coe, norm_inv, RCLike.norm_conj] at hnorm
        have := inv_lt_one_of_one_lt₀ hz
        linarith
      have hden1' : -(ζ : ℂ) + z ≠ 0 := by
        intro hzero
        apply hden1
        linear_combination -hzero
      simp only [map_mul, map_div₀, map_sub, map_inv₀,
        starRingEnd_self_apply]
      have hcircle : (starRingEnd ℂ) (ζ : ℂ) = ((ζ : ℂ))⁻¹ :=
        (Complex.inv_eq_conj (Circle.norm_coe ζ)).symm
      rw [hcircle]
      field_simp [hz0, hζ0, hden1, hden1', hden2]
      have hinv := mul_inv_cancel₀ hden1'
      linear_combination -(f ζ * z) * hinv
    _ = (∫ ζ : Circle, f ζ ∂circleLebesgue) -
        ∫ ζ : Circle, (starRingEnd ℂ)
          ((circleLpConj f) ζ *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹)))
          ∂circleLebesgue := by
      have hfint : Integrable (fun ζ : Circle => f ζ) circleLebesgue :=
        (Lp.memLp f).integrable one_le_two
      have hBconj : Integrable (fun ζ : Circle => (starRingEnd ℂ)
          ((circleLpConj f) ζ *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹)))) circleLebesgue :=
        hB.norm.mono'
          (Complex.continuous_conj.comp_aestronglyMeasurable
            hB.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun ζ => by rw [RCLike.norm_conj])
      rw [integral_sub hfint hBconj]
    _ = (∫ ζ : Circle, f ζ ∂circleLebesgue) -
        (starRingEnd ℂ)
          (∫ ζ : Circle, (circleLpConj f) ζ *
            ((ζ : ℂ) / ((ζ : ℂ) - (starRingEnd ℂ z)⁻¹))
            ∂circleLebesgue) := by
      rw [integral_conj]

theorem circleHardyCauchyTransform_circleLpConj_hardyDiskBoundary_general
    (f : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    circleHardyCauchyTransform (circleLpConj (hardyDiskBoundary f)) z =
      (starRingEnd ℂ) (f 0) := by
  rw [circleHardyCauchyTransform_eq_inner _ hz,
    inner_hardyDiskBoundary_circleLpConj_hardyDiskBoundary]
  simp [hardyKernel, hardyKernelCoeff]

theorem integral_circleLpConj_hardyDiskBoundary (f : HardyDisk) :
    (∫ ζ : Circle, (circleLpConj (hardyDiskBoundary f)) ζ
      ∂circleLebesgue) = (starRingEnd ℂ) (f 0) := by
  calc
    (∫ ζ : Circle, (circleLpConj (hardyDiskBoundary f)) ζ
        ∂circleLebesgue) =
        ∫ ζ : Circle, (starRingEnd ℂ) ((hardyDiskBoundary f) ζ)
          ∂circleLebesgue := by
      apply integral_congr_ae
      exact circleLpConj_coeFn_ae _
    _ = (starRingEnd ℂ)
        (∫ ζ : Circle, (hardyDiskBoundary f) ζ ∂circleLebesgue) :=
      integral_conj
    _ = (starRingEnd ℂ) (f 0) := by rw [integral_hardyDiskBoundary]

theorem circleHardyCauchyTransform_hardyDiskBoundary_exterior
    (f : HardyDisk) {z : ℂ} (hz : 1 < ‖z‖) :
    circleHardyCauchyTransform (hardyDiskBoundary f) z = 0 := by
  have hw : ‖(starRingEnd ℂ z)⁻¹‖ < 1 := by
    rw [norm_inv, RCLike.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  rw [circleHardyCauchyTransform_exterior_relation _ hz,
    integral_hardyDiskBoundary,
    circleHardyCauchyTransform_circleLpConj_hardyDiskBoundary_general _ hw]
  simp

/-- Reciprocal-conjugate analytic reflection of a Hardy function to the exterior disk. -/
def hardyExteriorReflection (f : HardyDisk) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (hardyFun f ((starRingEnd ℂ z)⁻¹))

theorem circleHardyCauchyTransform_circleLpConj_hardyDiskBoundary_exterior
    (f : HardyDisk) (hf0 : f 0 = 0) {z : ℂ} (hz : 1 < ‖z‖) :
    circleHardyCauchyTransform (circleLpConj (hardyDiskBoundary f)) z =
      -hardyExteriorReflection f z := by
  have hw : ‖(starRingEnd ℂ z)⁻¹‖ < 1 := by
    rw [norm_inv, RCLike.norm_conj]
    exact inv_lt_one_of_one_lt₀ hz
  rw [circleHardyCauchyTransform_exterior_relation _ hz,
    integral_circleLpConj_hardyDiskBoundary,
    circleLpConj_circleLpConj,
    circleHardyCauchyTransform_hardyDiskBoundary _ hw]
  simp [hardyExteriorReflection, hf0]

/-- If an `L²` circle vector vanishes on a Euclidean arc, its Cauchy transform extends
holomorphically through every point of that arc. -/
theorem differentiableAt_circleHardyCauchyTransform_of_ae_zero_near
    (f : Lp ℂ 2 circleLebesgue) (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < r → f ζ = 0) :
    DifferentiableAt ℂ (circleHardyCauchyTransform f) z₀ := by
  let F : ℂ → Circle → ℂ := fun z ζ =>
    if dist (ζ : ℂ) z₀ < r then 0
    else f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
  let bound : Circle → ℝ := fun ζ => (2 / r) * ‖f ζ‖
  have hmeas : ∀ z ∈ ball z₀ (r / 2),
      AEStronglyMeasurable (F z) circleLebesgue := by
    intro z hz
    have hset : MeasurableSet {ζ : Circle | dist (ζ : ℂ) z₀ < r} := by
      change @MeasurableSet Circle (borel Circle)
        {ζ : Circle | dist (ζ : ℂ) z₀ < r}
      letI : MeasurableSpace Circle := borel Circle
      rw [show {ζ : Circle | dist (ζ : ℂ) z₀ < r} =
          (fun ζ : Circle => (ζ : ℂ)) ⁻¹' ball z₀ r by
        ext ζ
        simp [mem_ball]]
      exact @IsOpen.measurableSet Circle _ _ (borel Circle) ⟨le_rfl⟩
        (isOpen_ball.preimage continuous_subtype_val)
    have hkernelMeas : Measurable
        (fun ζ : Circle => (ζ : ℂ) / ((ζ : ℂ) - z)) := by
      fun_prop
    have hprod : AEStronglyMeasurable
        (fun ζ : Circle => f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)))
        circleLebesgue :=
      (Lp.aestronglyMeasurable f).mul
        hkernelMeas.aestronglyMeasurable
    convert hprod.indicator hset.compl using 1
    funext ζ
    by_cases hnear : dist (ζ : ℂ) z₀ < r <;>
      simp [F, Set.indicator, hnear]
  have hdiff : ∀ ζ : Circle,
      DifferentiableOn ℂ (fun z : ℂ => F z ζ) (ball z₀ (r / 2)) := by
    intro ζ
    by_cases hnear : dist (ζ : ℂ) z₀ < r
    · simp only [F, if_pos hnear]
      fun_prop
    · simp only [F, if_neg hnear]
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hconstF : DifferentiableAt ℂ (fun _ : ℂ => f ζ) z :=
        differentiableAt_const (c := f ζ)
      have hconstZeta : DifferentiableAt ℂ (fun _ : ℂ => (ζ : ℂ)) z :=
        differentiableAt_const (c := (ζ : ℂ))
      have hden : (ζ : ℂ) - z ≠ 0 := by
        intro hzero
        have heq : (ζ : ℂ) = z := sub_eq_zero.mp hzero
        have hzdist : dist (ζ : ℂ) z₀ < r / 2 := by
          simpa [heq] using hz
        exact hnear (by linarith)
      exact hconstF.mul
        (hconstZeta.div (hconstZeta.sub differentiableAt_id) hden)
  have hbound : ∀ ζ : Circle, ∀ z ∈ ball z₀ (r / 2),
      ‖F z ζ‖ ≤ bound ζ := by
    intro ζ z hz
    by_cases hnear : dist (ζ : ℂ) z₀ < r
    · simp only [F, if_pos hnear, norm_zero]
      change 0 ≤ (2 / r) * ‖f ζ‖
      exact mul_nonneg (div_nonneg (by norm_num) hr.le) (norm_nonneg _)
    · simp only [F, if_neg hnear, bound]
      have hfar : r ≤ dist (ζ : ℂ) z₀ := le_of_not_gt hnear
      have htriangle : dist (ζ : ℂ) z₀ ≤
          dist (ζ : ℂ) z + dist z z₀ := dist_triangle _ _ _
      have hzdist : dist z z₀ < r / 2 := by
        simpa [mem_ball] using hz
      have hsep : r / 2 < ‖(ζ : ℂ) - z‖ := by
        rw [← dist_eq]
        linarith
      have hkernel : ‖(ζ : ℂ) / ((ζ : ℂ) - z)‖ ≤ 2 / r := by
        rw [norm_div, Circle.norm_coe, one_div]
        have hhalf : 0 < r / 2 := by positivity
        have hnormpos : 0 < ‖(ζ : ℂ) - z‖ := lt_trans hhalf hsep
        calc
          ‖(ζ : ℂ) - z‖⁻¹ ≤ (r / 2)⁻¹ :=
            (inv_le_inv₀ hnormpos hhalf).2 hsep.le
          _ = 2 / r := by field_simp
      rw [norm_mul]
      calc
        ‖f ζ‖ * ‖(ζ : ℂ) / ((ζ : ℂ) - z)‖ ≤
            ‖f ζ‖ * (2 / r) :=
          mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
        _ = (2 / r) * ‖f ζ‖ := by ring
  have hboundInt : Integrable bound circleLebesgue := by
    exact ((Lp.memLp f).integrable one_le_two).norm.const_mul (2 / r)
  have hdiffInt : DifferentiableAt ℂ
      (fun z : ℂ => ∫ ζ : Circle, F z ζ ∂circleLebesgue) z₀ :=
    differentiableAt_integral_of_cauchy_dominated
      (by positivity : 0 < r / 2) hmeas hdiff hbound hboundInt
  have heq : circleHardyCauchyTransform f =
      fun z : ℂ => ∫ ζ : Circle, F z ζ ∂circleLebesgue := by
    funext z
    rw [circleHardyCauchyTransform]
    apply integral_congr_ae
    filter_upwards [hzero] with ζ hζ
    by_cases hnear : dist (ζ : ℂ) z₀ < r
    · simp [F, hnear, hζ hnear]
    · simp [F, hnear]
  rw [heq]
  exact hdiffInt

theorem circleHardyCauchyTransform_sub_of_norm_ne_one
    (f g : Lp ℂ 2 circleLebesgue) {z : ℂ} (hz : ‖z‖ ≠ 1) :
    circleHardyCauchyTransform (f - g) z =
      circleHardyCauchyTransform f z - circleHardyCauchyTransform g z := by
  have hkernel : Continuous fun ζ : Circle =>
      (ζ : ℂ) / ((ζ : ℂ) - z) := by
    apply Continuous.div continuous_subtype_val
      (continuous_subtype_val.sub continuous_const)
    intro ζ hden
    apply hz
    have heq : (ζ : ℂ) = z := sub_eq_zero.mp hden
    rw [← heq, Circle.norm_coe]
  have hfint := integrable_circleLp_mul_continuous f _ hkernel
  have hgint := integrable_circleLp_mul_continuous g _ hkernel
  rw [circleHardyCauchyTransform, circleHardyCauchyTransform,
    circleHardyCauchyTransform]
  calc
    (∫ ζ : Circle, (f - g) ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
        ∂circleLebesgue) =
        ∫ ζ : Circle,
          (f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z)) -
            g ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))) ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub f g] with ζ hζ
      rw [hζ]
      simp only [Pi.sub_apply]
      ring
    _ = (∫ ζ : Circle, f ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
          ∂circleLebesgue) -
        ∫ ζ : Circle, g ζ * ((ζ : ℂ) / ((ζ : ℂ) - z))
          ∂circleLebesgue := integral_sub hfint hgint

/-- Exact local gluing of an analytic Hardy function to a reciprocal-conjugate exterior Hardy
function when their `L²` traces agree on a circle arc. -/
theorem exists_differentiableAt_hardy_arc_glue
    (u v : HardyDisk) (hv0 : v 0 = 0) (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hseam : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < r →
        (hardyDiskBoundary u) ζ =
          (starRingEnd ℂ) ((hardyDiskBoundary v) ζ)) :
    ∃ G : ℂ → ℂ,
      DifferentiableAt ℂ G z₀ ∧
      (∀ z : ℂ, ‖z‖ < 1 → G z = hardyFun u z) ∧
      (∀ z : ℂ, 1 < ‖z‖ → G z = hardyExteriorReflection v z) := by
  let d : Lp ℂ 2 circleLebesgue :=
    hardyDiskBoundary u - circleLpConj (hardyDiskBoundary v)
  have hzeroD : ∀ᵐ ζ : Circle ∂circleLebesgue,
      dist (ζ : ℂ) z₀ < r → d ζ = 0 := by
    filter_upwards [Lp.coeFn_sub (hardyDiskBoundary u)
        (circleLpConj (hardyDiskBoundary v)),
      circleLpConj_coeFn_ae (hardyDiskBoundary v), hseam]
      with ζ hsub hconj hmatch
    intro hnear
    change (hardyDiskBoundary u - circleLpConj (hardyDiskBoundary v)) ζ = 0
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hconj, hmatch hnear]
    simp
  refine ⟨circleHardyCauchyTransform d,
    differentiableAt_circleHardyCauchyTransform_of_ae_zero_near
      d z₀ hr hzeroD, ?_, ?_⟩
  · intro z hz
    have hzne : ‖z‖ ≠ 1 := ne_of_lt hz
    change circleHardyCauchyTransform
      (hardyDiskBoundary u - circleLpConj (hardyDiskBoundary v)) z = _
    rw [circleHardyCauchyTransform_sub_of_norm_ne_one _ _ hzne,
      circleHardyCauchyTransform_hardyDiskBoundary _ hz,
      circleHardyCauchyTransform_circleLpConj_hardyDiskBoundary _ hv0 hz,
      sub_zero]
  · intro z hz
    have hzne : ‖z‖ ≠ 1 := ne_of_gt hz
    change circleHardyCauchyTransform
      (hardyDiskBoundary u - circleLpConj (hardyDiskBoundary v)) z = _
    rw [circleHardyCauchyTransform_sub_of_norm_ne_one _ _ hzne,
      circleHardyCauchyTransform_hardyDiskBoundary_exterior _ hz,
      circleHardyCauchyTransform_circleLpConj_hardyDiskBoundary_exterior _ hv0 hz]
    simp

end

end GaloisForLFunctions.HTGeometry
