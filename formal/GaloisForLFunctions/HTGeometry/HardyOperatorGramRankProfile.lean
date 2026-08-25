import GaloisForLFunctions.HTGeometry.KernelNegativeSquareCongruence
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel

/-!
# Exact rank profile of a Hardy-operator Gram kernel

For an arbitrary bounded operator with disk Hardy domain, the negative Gram kernel of its images of
Szegő sections has an `r`-dimensional negative subspace exactly when the operator has algebraic rank
at least `r`.  Density of the analytic Szegő sections makes the result valid without closed-range or
finite-rank assumptions.
-/

open Complex Metric
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Algebraic operator rank at least `r`, witnessed directly in the range. -/
def HardyOperatorRankAtLeast (T : HardyDisk →L[ℂ] K) (r : ℕ) : Prop :=
  ∃ v : Fin r → HardyDisk, LinearIndependent ℂ (fun i => T (v i))

/-- The negative Gram operator `-T†T` on disk Hardy space. -/
def hardyOperatorNegativeGramOperator (T : HardyDisk →L[ℂ] K) :
    HardyDisk →L[ℂ] HardyDisk :=
  -(T.adjoint.comp T)

theorem hardyOperatorNegativeGramOperator_hermitian
    (T : HardyDisk →L[ℂ] K) (x y : HardyDisk) :
    inner ℂ x (hardyOperatorNegativeGramOperator T y) =
      inner ℂ (hardyOperatorNegativeGramOperator T x) y := by
  change inner ℂ x (-(T.adjoint (T y))) = inner ℂ (-(T.adjoint (T x))) y
  rw [inner_neg_right, inner_neg_left,
    ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_left]

/-- Analytic total-section realization of the negative operator Gram. -/
def hardyOperatorNegativeGramRealization (T : HardyDisk →L[ℂ] K) :
    RHTower.AnalyticHermitianKernelRealization HardyDisk where
  domain := Metric.ball 0 1
  kernelSection := fun z => analyticHardyKernelSection ((starRingEnd ℂ) z)
  domain_preconnected := convex_ball 0 1 |>.isPreconnected
  coefficient_analytic := analyticOnNhd_inner_analyticHardyKernelSection
  global_total := conjugateAnalyticHardyKernelSection_global_total
  form := hardyOperatorNegativeGramOperator T
  form_hermitian := hardyOperatorNegativeGramOperator_hermitian T

/-- Literal negative Gram kernel on analytic Szegő sections. -/
def hardyOperatorNegativeGramKernel (T : HardyDisk →L[ℂ] K) (z w : ℂ) : ℂ :=
  -inner ℂ
    (T (analyticHardyKernelSection ((starRingEnd ℂ) w)))
    (T (analyticHardyKernelSection ((starRingEnd ℂ) z)))

theorem hardyOperatorNegativeGramRealization_kernel_eq
    (T : HardyDisk →L[ℂ] K) (z w : ℂ) :
    (hardyOperatorNegativeGramRealization T).kernel z w =
      hardyOperatorNegativeGramKernel T z w := by
  rw [RHTower.AnalyticHermitianKernelRealization.kernel,
    hardyOperatorNegativeGramRealization, hardyOperatorNegativeGramKernel]
  change inner ℂ _ (-(T.adjoint (T _))) = -inner ℂ (T _) (T _)
  rw [inner_neg_right, ContinuousLinearMap.adjoint_inner_right]

theorem hardyOperatorNegativeGramOperator_quadratic
    (T : HardyDisk →L[ℂ] K) (x : HardyDisk) :
    (inner ℂ x (hardyOperatorNegativeGramOperator T x)).re = -‖T x‖ ^ 2 := by
  change (inner ℂ x (-(T.adjoint (T x)))).re = -‖T x‖ ^ 2
  rw [inner_neg_right, ContinuousLinearMap.adjoint_inner_right, Complex.neg_re]
  exact congrArg Neg.neg
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (T x)).symm

/-- Exact arbitrary-rank profile of the literal negative Gram kernel. -/
theorem hardyOperatorNegativeGramKernel_negativeDimension_iff_rankAtLeast
    (T : HardyDisk →L[ℂ] K) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          hardyOperatorNegativeGramKernel T z.1 w.1) r ↔
      HardyOperatorRankAtLeast T r := by
  let R := hardyOperatorNegativeGramRealization T
  have hkernel : (fun z w : Metric.ball (0 : ℂ) 1 => R.kernel z.1 w.1) =
      fun z w => hardyOperatorNegativeGramKernel T z.1 w.1 := by
    funext z w
    exact hardyOperatorNegativeGramRealization_kernel_eq T z.1 w.1
  rw [← hkernel, ← hasFiniteGramNegativeDimensionOn_iff_kernel
    R (Metric.ball 0 1) r]
  constructor
  · intro hgram
    have hsection := (R.hasFiniteGramNegativeDimensionOn_iff
      (Metric.ball 0 1) r).mp hgram
    have hnegative := (R.hasFiniteSectionNegativeDimensionOn_iff
      (Metric.ball 0 1) r).mp hsection
    obtain ⟨v, -, hv⟩ := hnegative
    refine ⟨v, ?_⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hci
    have hc0 : c ≠ 0 := by
      intro hzero
      exact hci (congrFun hzero i)
    have hneg := R.isNegativeTuple_quadratic_neg hv hc0
    have hmap : T (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c) = 0 := by
      simpa only [RHTower.AnalyticHermitianKernelRealization.sectionSynthesis,
        map_sum, map_smul] using hc
    rw [RHTower.AnalyticHermitianKernelRealization.sectionQuadratic] at hneg
    change (inner ℂ _ (hardyOperatorNegativeGramOperator T _)).re < 0 at hneg
    rw [hardyOperatorNegativeGramOperator_quadratic, hmap, norm_zero,
      zero_pow (by norm_num)] at hneg
    norm_num at hneg
  · rintro ⟨v, hv⟩
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
        have hmap :
            T (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c) ≠ 0 := by
          intro hzero
          apply hc0
          funext i
          exact Fintype.linearIndependent_iff.mp hv c (by
            simpa only [RHTower.AnalyticHermitianKernelRealization.sectionSynthesis,
              map_sum, map_smul] using hzero) i
        rw [RHTower.AnalyticHermitianKernelRealization.sectionQuadratic]
        change (inner ℂ _ (hardyOperatorNegativeGramOperator T _)).re < 0
        rw [hardyOperatorNegativeGramOperator_quadratic]
        exact neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hmap))
    have hsection := (R.hasFiniteSectionNegativeDimensionOn_iff
      (Metric.ball 0 1) r).mpr hnegative
    exact (R.hasFiniteGramNegativeDimensionOn_iff (Metric.ball 0 1) r).mpr hsection

end GaloisForLFunctions.HTGeometry
