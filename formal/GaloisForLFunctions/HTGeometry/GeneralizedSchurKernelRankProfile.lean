import GaloisForLFunctions.HTGeometry.ProjectedAdjointRankProfile
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel
import GaloisForLFunctions.HTGeometry.HardyMultiplierZeroModelDimension
import GaloisForLFunctions.HTGeometry.KernelNegativeSquareCongruence

/-!
# Arbitrary-inner generalized-Schur kernel rank profile

For a contractive Hardy numerator and any isometric Hardy denominator, the literal generalized-
Schur kernel carries an `r`-dimensional negative square exactly when the numerator adjoint restricted
to the denominator model space has algebraic rank at least `r`.  This simultaneously covers finite
common-factor rank loss and infinite leakage rank.
-/

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Multiplication by `B` preserves the Hardy norm. -/
def HardyMultiplierIsometry (B : DiskMultiplier) : Prop :=
  ∀ x : HardyDisk, ‖hardyMul B x‖ = ‖x‖

/-- Bounded Hermitian operator realizing a generalized-Schur kernel with arbitrary denominator. -/
def generalizedSchurOperator (F B : DiskMultiplier) : HardyDisk →L[ℂ] HardyDisk :=
  (hardyMul B).comp (hardyMul B).adjoint -
    (hardyMul F).comp (hardyMul F).adjoint

theorem generalizedSchurOperator_hermitian
    (F B : DiskMultiplier) (x y : HardyDisk) :
    inner ℂ x (generalizedSchurOperator F B y) =
      inner ℂ (generalizedSchurOperator F B x) y := by
  have hself : ∀ (A : HardyDisk →L[ℂ] HardyDisk) (u v : HardyDisk),
      inner ℂ u (A (A.adjoint v)) = inner ℂ (A (A.adjoint u)) v := by
    intro A u v
    calc
      inner ℂ u (A (A.adjoint v)) = inner ℂ (A.adjoint u) (A.adjoint v) :=
        (ContinuousLinearMap.adjoint_inner_left A (A.adjoint v) u).symm
      _ = inner ℂ (A (A.adjoint u)) v :=
        ContinuousLinearMap.adjoint_inner_right A (A.adjoint u) v
  simp only [generalizedSchurOperator, sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, inner_sub_left]
  rw [hself (hardyMul B), hself (hardyMul F)]

/-- Literal reflected generalized-Schur defect kernel for arbitrary disk multipliers. -/
def generalizedSchurKernel (F B : DiskMultiplier) (z w : ℂ) : ℂ :=
  (reflectedDiskMultiplierValue B z *
      (starRingEnd ℂ) (reflectedDiskMultiplierValue B w) -
    reflectedDiskMultiplierValue F z *
      (starRingEnd ℂ) (reflectedDiskMultiplierValue F w)) /
    (1 - z * (starRingEnd ℂ) w)

/-- Hardy realization of the arbitrary-denominator generalized-Schur kernel. -/
def generalizedSchurRealization (F B : DiskMultiplier) :
    RHTower.AnalyticHermitianKernelRealization HardyDisk where
  domain := Metric.ball 0 1
  kernelSection := fun z => analyticHardyKernelSection ((starRingEnd ℂ) z)
  domain_preconnected := convex_ball 0 1 |>.isPreconnected
  coefficient_analytic := analyticOnNhd_inner_analyticHardyKernelSection
  global_total := conjugateAnalyticHardyKernelSection_global_total
  form := generalizedSchurOperator F B
  form_hermitian := generalizedSchurOperator_hermitian F B

theorem generalizedSchurRealization_kernel_eq
    (F B : DiskMultiplier) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    (generalizedSchurRealization F B).kernel z w =
      generalizedSchurKernel F B z w := by
  have hzc : ‖(starRingEnd ℂ) z‖ < 1 := by simpa using hz
  have hwc : ‖(starRingEnd ℂ) w‖ < 1 := by simpa using hw
  rw [RHTower.AnalyticHermitianKernelRealization.kernel,
    generalizedSchurRealization]
  simp only [generalizedSchurOperator, sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, analyticHardyKernelSection_eq hzc,
    analyticHardyKernelSection_eq hwc]
  change inner ℂ (hardyKernel hwc)
      (hardyMul B ((hardyMul B).adjoint (hardyKernel hzc))) -
    inner ℂ (hardyKernel hwc)
      (hardyMul F ((hardyMul F).adjoint (hardyKernel hzc))) = _
  rw [adjoint_hardyMul_hardyKernel B hzc,
    adjoint_hardyMul_hardyKernel F hzc, map_smul, map_smul,
    inner_smul_right, inner_smul_right,
    inner_hardyKernel hwc, hardyFun_hardyMul B (hardyKernel hzc) hwc,
    inner_hardyKernel hwc, hardyFun_hardyMul F (hardyKernel hzc) hwc,
    hardyFun_hardyKernel hwc hzc]
  rw [generalizedSchurKernel]
  simp only [reflectedDiskMultiplierValue]
  simp
  rw [div_eq_mul_inv]
  ring

theorem adjoint_hardyMul_comp_of_isometry
    (B : DiskMultiplier) (hB : HardyMultiplierIsometry B) (x : HardyDisk) :
    (hardyMul B).adjoint (hardyMul B x) = x := by
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact inner_map_map_of_isometry hB x y

theorem hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry
    (B : DiskMultiplier) (hB : HardyMultiplierIsometry B) :
    (hardyMultiplierModelSpace B)ᗮ =
      LinearMap.range ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk) := by
  let R : Submodule ℂ HardyDisk :=
    LinearMap.range ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk)
  have hclosed : IsClosed (R : Set HardyDisk) := isClosed_coe_range_of_isometry hB
  haveI : CompleteSpace R := hclosed.completeSpace_coe
  change Submodule.orthogonal (Submodule.orthogonal R) = R
  rw [Submodule.orthogonal_orthogonal]

theorem norm_sq_adjoint_hardyMul_of_isometry
    (B : DiskMultiplier) (hB : HardyMultiplierIsometry B) (g : HardyDisk) :
    ‖(hardyMul B).adjoint g‖ ^ 2 =
      ‖g‖ ^ 2 - ‖(hardyMultiplierModelSpace B).starProjection g‖ ^ 2 := by
  classical
  let K := hardyMultiplierModelSpace B
  set u : HardyDisk := K.starProjection g with hu
  set y : HardyDisk := g - u with hy
  have hymem : y ∈ Kᗮ := by
    rw [hy, hu]
    exact K.sub_starProjection_mem_orthogonal g
  obtain ⟨x, hx⟩ : ∃ x : HardyDisk, hardyMul B x = y := by
    have hrange : y ∈ LinearMap.range
        ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) := by
      rw [← hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry B hB]
      exact hymem
    simpa using hrange
  have humem : u ∈ K := by
    rw [hu]
    exact K.starProjection_apply_mem g
  have hadjU : (hardyMul B).adjoint u = 0 := by
    refine ext_inner_right ℂ fun x => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hxrange : hardyMul B x ∈ LinearMap.range
        ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) :=
      ⟨x, rfl⟩
    have huorth : u ∈ (LinearMap.range
        ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ :=
      humem
    have horth := ((LinearMap.range
      ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk)).mem_orthogonal _).1
        huorth (hardyMul B x) hxrange
    rw [← inner_conj_symm, horth, map_zero]
  have hsplit : g = u + y := by rw [hy]; abel
  have hadj : (hardyMul B).adjoint g = x := by
    rw [hsplit, map_add, hadjU, zero_add, ← hx,
      adjoint_hardyMul_comp_of_isometry B hB]
  have hperp : (inner ℂ u y : ℂ) = 0 :=
    ((K.mem_orthogonal y).1 hymem u humem)
  have hpyth : ‖g‖ ^ 2 = ‖u‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [hsplit]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u y hperp
  have hnx : ‖x‖ = ‖y‖ := by rw [← hx, hB]
  rw [hadj, hnx, hpyth, hu]
  ring

theorem generalizedSchurOperator_quadratic_eq_projectedAdjointDefect
    (F B : DiskMultiplier) (hB : HardyMultiplierIsometry B) (x : HardyDisk) :
    (inner ℂ x (generalizedSchurOperator F B x)).re =
      projectedAdjointDefectForm (hardyMultiplierModelSpace B) (hardyMul F) x := by
  have hnorm : ∀ (A : HardyDisk →L[ℂ] HardyDisk),
      (inner ℂ x (A (A.adjoint x))).re = ‖A.adjoint x‖ ^ 2 := by
    intro A
    rw [show inner ℂ x (A (A.adjoint x)) = inner ℂ (A.adjoint x) (A.adjoint x) by
      exact (ContinuousLinearMap.adjoint_inner_left A (A.adjoint x) x).symm]
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (A.adjoint x)).symm
  simp only [generalizedSchurOperator, sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, Complex.sub_re]
  rw [hnorm (hardyMul B), hnorm (hardyMul F),
    norm_sq_adjoint_hardyMul_of_isometry B hB, projectedAdjointDefectForm]
  ring

/-- Exact arbitrary-rank profile of the literal generalized-Schur kernel. -/
theorem generalizedSchurKernel_negativeDimension_iff_rankAtLeast
    (F B : DiskMultiplier) (hF : F.bd ≤ 1)
    (hB : HardyMultiplierIsometry B) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          generalizedSchurKernel F B z.1 w.1) r ↔
      RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace B) (hardyMul F) r := by
  let R := generalizedSchurRealization F B
  have hkernel : (fun z w : Metric.ball (0 : ℂ) 1 => R.kernel z.1 w.1) =
      (fun z w : Metric.ball (0 : ℂ) 1 => generalizedSchurKernel F B z.1 w.1) := by
    funext z w
    exact generalizedSchurRealization_kernel_eq F B
      (by
        have hz : dist z.1 0 < 1 := z.2
        simpa [dist_zero_right] using hz)
      (by
        have hw : dist w.1 0 < 1 := w.2
        simpa [dist_zero_right] using hw)
  rw [← hkernel, ← hasFiniteGramNegativeDimensionOn_iff_kernel R (Metric.ball 0 1) r]
  constructor
  · intro hgram
    have hsection := (R.hasFiniteGramNegativeDimensionOn_iff
      (Metric.ball 0 1) r).mp hgram
    have hnegative := (R.hasFiniteSectionNegativeDimensionOn_iff
      (Metric.ball 0 1) r).mp hsection
    obtain ⟨v, -, hv⟩ := hnegative
    apply (projectedAdjointDefect_hasFiniteNegativeDimension_iff_rankAtLeast
      (hardyMultiplierModelSpace B) (hardyMul F)
      ((norm_hardyMul_le F).trans hF) r).mp
    refine ⟨v, fun c hc => ?_⟩
    have hq := R.isNegativeTuple_quadratic_neg hv hc
    rw [RHTower.AnalyticHermitianKernelRealization.sectionQuadratic] at hq
    simpa only [R, generalizedSchurRealization,
      generalizedSchurOperator_quadratic_eq_projectedAdjointDefect F B hB,
      RHTower.AnalyticHermitianKernelRealization.sectionSynthesis] using hq
  · intro hrank
    have hform :=
      (projectedAdjointDefect_hasFiniteNegativeDimension_iff_rankAtLeast
        (hardyMultiplierModelSpace B) (hardyMul F)
        ((norm_hardyMul_le F).trans hF) r).mpr hrank
    obtain ⟨v, hv⟩ := hform
    have hnegative : R.HasNegativeDimensionOn (Metric.ball 0 1) r := by
      refine ⟨v, ?_, ?_⟩
      · intro i
        change v i ∈ (Submodule.span ℂ
          (R.kernelSection '' R.domain)).topologicalClosure
        rw [R.global_total]
        exact Submodule.mem_top
      · intro c hc
        have hc0 : c ≠ 0 := by
          intro hzero
          rw [hzero, norm_zero] at hc
          norm_num at hc
        have hq := hv c hc0
        rw [RHTower.AnalyticHermitianKernelRealization.sectionQuadratic]
        simpa only [R, generalizedSchurRealization,
          generalizedSchurOperator_quadratic_eq_projectedAdjointDefect F B hB,
          RHTower.AnalyticHermitianKernelRealization.sectionSynthesis] using hq
    have hsection := (R.hasFiniteSectionNegativeDimensionOn_iff
      (Metric.ball 0 1) r).mpr hnegative
    exact (R.hasFiniteGramNegativeDimensionOn_iff (Metric.ball 0 1) r).mpr hsection

end GaloisForLFunctions.HTGeometry
