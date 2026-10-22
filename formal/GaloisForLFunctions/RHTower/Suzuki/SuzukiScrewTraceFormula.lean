/-
# Suzuki's trace and eigenvalue formula for the screw-kernel operator

This file closes the paragraph following Suzuki (2022), Theorem 1.5.  For the literal
operator on `L²([-a,a])` constructed in `SuzukiScrewTraceClass`, it proves

* the diagonal-kernel trace formula;
* symmetry from the real Hermitian kernel, with the Fubini interchange justified;
* Lidskii's eigenvalue-sum formula, with nonzero eigenvalues repeated by multiplicity.

All statements are unconditional.  In particular, no Riemann-hypothesis premise is used.
-/
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewTraceClass
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.LidskiiSelfAdjoint

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open RHTower

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiScrewTraceFormulaLocalInst1 : Encodable XiZeroCopy := Encodable.ofCountable _

/-- The actual Xi-divisor `ℓ²` carrier is separable because its canonical Hilbert basis has
countable index. -/
local instance suzukiScrewTraceFormulaLocalInst2 : TopologicalSpace.SeparableSpace XiDivisorL2 := by
  let b : HilbertBasis XiZeroCopy ℂ XiDivisorL2 :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ XiDivisorL2)
  have hsep : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range b) : Set XiDivisorL2) :=
    (Set.countable_range b).isSeparable.span
  have hdense : Dense (Submodule.span ℂ (Set.range b) : Set XiDivisorL2) := by
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  exact hdense.isSeparable_iff.mp hsep

theorem inner_suzukiDivisorFeature_diagonal (t : ℝ) :
    inner ℂ (star (suzukiDivisorFeature t)) (suzukiDivisorFeature (-t)) =
      suzukiScrewKernel t t := by
  change suzukiLeftFunctional t (suzukiDivisorFeature (-t)) = _
  rw [suzukiLeftFunctional_apply, suzukiScrewKernel_eq_tsum_exponential]
  apply tsum_congr
  intro q
  exact suzukiDivisorFeatureCoord_mul_eq_kernelTerm t t q

/-- Trace of Suzuki's literal screw-kernel operator equals the integral of its diagonal. -/
theorem opTrace_suzukiScrewIntegralOperator_eq_integral_diagonal
    {a : ℝ} (_ha : 0 ≤ a) :
    ContinuousLinearMap.opTrace (suzukiScrewIntegralOperator a) =
      ∫ t : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (t : ℝ) ∂volume := by
  rw [suzukiScrewIntegralOperator]
  have hleft := isHilbertSchmidt_kernelOperator
    (volume : Measure (SuzukiApertureInterval a)) (suzukiLeftFunctionalField a)
  have hright := isHilbertSchmidt_kernelOperator
    (volume : Measure (SuzukiApertureInterval a)) (suzukiRightFunctionalField a)
  calc
    ContinuousLinearMap.opTrace
        (suzukiLeftSynthesis a ∘L ContinuousLinearMap.adjoint (suzukiRightSynthesis a)) =
      ContinuousLinearMap.opTrace
        (ContinuousLinearMap.adjoint (suzukiRightSynthesis a) ∘L suzukiLeftSynthesis a) :=
        ContinuousLinearMap.opTrace_comp_comm hleft hright.adjoint
    _ = ContinuousLinearMap.hsInner (suzukiRightSynthesis a) (suzukiLeftSynthesis a) := by
      rw [ContinuousLinearMap.opTrace_comp_eq_hsInner, ContinuousLinearMap.adjoint_adjoint]
    _ = ∫ t : SuzukiApertureInterval a,
        inner ℂ
          ((InnerProductSpace.toDual ℂ XiDivisorL2).symm
            ((suzukiLeftFunctionalField a) t))
          ((InnerProductSpace.toDual ℂ XiDivisorL2).symm
            ((suzukiRightFunctionalField a) t)) ∂volume := by
      exact hsInner_kernelOperator
        (volume : Measure (SuzukiApertureInterval a))
        (suzukiRightFunctionalField a) (suzukiLeftFunctionalField a)
    _ = ∫ t : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (t : ℝ) ∂volume := by
      apply integral_congr_ae
      filter_upwards [
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
          (μ := (volume : Measure (SuzukiApertureInterval a)))
          (suzukiLeftFunctionalContinuous a),
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
          (μ := (volume : Measure (SuzukiApertureInterval a)))
          (suzukiRightFunctionalContinuous a)
      ] with t hleftField hrightField
      rw [suzukiLeftFunctionalField, hleftField,
        suzukiRightFunctionalField, hrightField]
      simp only [suzukiLeftFunctionalContinuous, suzukiRightFunctionalContinuous,
        suzukiLeftFunctional, suzukiRightFunctional]
      change inner ℂ
        ((InnerProductSpace.toDual ℂ XiDivisorL2).symm
          ((InnerProductSpace.toDual ℂ XiDivisorL2)
            (star (suzukiDivisorFeature (t : ℝ)))))
        ((InnerProductSpace.toDual ℂ XiDivisorL2).symm
          ((InnerProductSpace.toDual ℂ XiDivisorL2)
            (suzukiDivisorFeature (-(t : ℝ))))) = _
      rw [(InnerProductSpace.toDual ℂ XiDivisorL2).symm_apply_apply,
        (InnerProductSpace.toDual ℂ XiDivisorL2).symm_apply_apply]
      exact inner_suzukiDivisorFeature_diagonal (t : ℝ)

theorem opTrace_suzukiScrewIntegralOperator_eq_two_integral_psi
    {a : ℝ} (ha : 0 ≤ a) :
    ContinuousLinearMap.opTrace (suzukiScrewIntegralOperator a) =
      ((2 * ∫ t : SuzukiApertureInterval a, suzukiPsi (t : ℝ) ∂volume : ℝ) : ℂ) := by
  rw [opTrace_suzukiScrewIntegralOperator_eq_integral_diagonal ha]
  simp_rw [suzukiScrewKernel_self]
  rw [integral_complex_ofReal]
  push_cast
  rw [integral_const_mul]
  norm_num

/-- The literal Suzuki kernel is Hermitian. -/
theorem suzukiScrewKernel_conj_swap (t u : ℝ) :
    (starRingEnd ℂ) (suzukiScrewKernel t u) = suzukiScrewKernel u t := by
  rw [← ofReal_suzukiScrewKernelReal, ← ofReal_suzukiScrewKernelReal]
  rw [Complex.conj_ofReal]
  congr 1
  simp only [suzukiScrewKernelReal]
  rw [show u - t = -(t - u) by ring, suzukiPsi_neg]
  ring

theorem continuous_suzukiScrewKernel_on_aperture (a : ℝ) :
    Continuous fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      suzukiScrewKernel (p.1 : ℝ) (p.2 : ℝ) := by
  have hpair : Continuous fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      ((p.1 : ℝ), (p.2 : ℝ)) := by
    fun_prop
  have hreal := Complex.continuous_ofReal.comp
    (continuous_suzukiScrewKernelReal.comp hpair)
  exact hreal.congr fun p => ofReal_suzukiScrewKernelReal (p.1 : ℝ) (p.2 : ℝ)

theorem exists_suzukiScrewKernel_norm_bound (a : ℝ) :
    ∃ C : ℝ, ∀ t u : SuzukiApertureInterval a,
      ‖suzukiScrewKernel (t : ℝ) (u : ℝ)‖ ≤ C := by
  have hcont : Continuous fun p : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      ‖suzukiScrewKernel (p.1 : ℝ) (p.2 : ℝ)‖ :=
    (continuous_suzukiScrewKernel_on_aperture a).norm
  obtain ⟨C, hC⟩ := (isCompact_univ.bddAbove_image hcont.continuousOn)
  refine ⟨C, fun t u => hC ?_⟩
  exact ⟨(t, u), Set.mem_univ _, rfl⟩

theorem inner_suzukiApertureL2_eq_integral {a : ℝ}
    (f g : SuzukiApertureIntervalL2 a) :
    inner ℂ f g = ∫ t : SuzukiApertureInterval a,
      (starRingEnd ℂ) (f t) * g t ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
    RCLike.inner_apply' (f t) (g t))

/-- Absolute integrability needed for the Fubini step in kernel symmetry. -/
theorem integrable_suzukiScrewKernel_pair
    {a C : ℝ} (hC : ∀ t u : SuzukiApertureInterval a,
      ‖suzukiScrewKernel (t : ℝ) (u : ℝ)‖ ≤ C)
    (f g : SuzukiApertureIntervalL2 a) :
    Integrable (Function.uncurry fun t u : SuzukiApertureInterval a =>
      (starRingEnd ℂ) (f u) *
        (starRingEnd ℂ) (suzukiScrewKernel (t : ℝ) (u : ℝ)) * g t)
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
  have hf : Integrable (fun u : SuzukiApertureInterval a =>
      (starRingEnd ℂ) (f u)) :=
    ((Lp.memLp f).integrable (by norm_num)).norm.mono'
      (Complex.continuous_conj.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun u => by rw [RCLike.norm_conj])
  have hg : Integrable (fun t : SuzukiApertureInterval a => g t) :=
    (Lp.memLp g).integrable (by norm_num)
  have hprod : Integrable (fun z : SuzukiApertureInterval a × SuzukiApertureInterval a =>
      g z.1 * (starRingEnd ℂ) (f z.2))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) :=
    hg.mul_prod hf
  have hkernel : AEStronglyMeasurable
      (fun z : SuzukiApertureInterval a × SuzukiApertureInterval a =>
        (starRingEnd ℂ) (suzukiScrewKernel (z.1 : ℝ) (z.2 : ℝ)))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) :=
    (Complex.continuous_conj.comp
      (continuous_suzukiScrewKernel_on_aperture a)).aestronglyMeasurable
  have hbounded : Integrable
      (fun z : SuzukiApertureInterval a × SuzukiApertureInterval a =>
        (starRingEnd ℂ) (suzukiScrewKernel (z.1 : ℝ) (z.2 : ℝ)) *
          (g z.1 * (starRingEnd ℂ) (f z.2)))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
    refine hprod.bdd_mul (c := C) hkernel
      (Filter.Eventually.of_forall fun z => ?_)
    rw [RCLike.norm_conj]
    exact hC z.1 z.2
  refine hbounded.congr (Filter.Eventually.of_forall fun z => ?_)
  change (starRingEnd ℂ) (suzukiScrewKernel (z.1 : ℝ) (z.2 : ℝ)) *
      (g z.1 * (starRingEnd ℂ) (f z.2)) =
    (starRingEnd ℂ) (f z.2) *
      (starRingEnd ℂ) (suzukiScrewKernel (z.1 : ℝ) (z.2 : ℝ)) * g z.1
  ring

/-- Suzuki's literal integral operator is symmetric, unconditionally. -/
theorem suzukiScrewIntegralOperator_isSymmetric {a : ℝ} (ha : 0 ≤ a) :
    (suzukiScrewIntegralOperator a).IsSymmetric := by
  obtain ⟨C, hC⟩ := exists_suzukiScrewKernel_norm_bound a
  intro f g
  have hL : inner ℂ (suzukiScrewIntegralOperator a f) g =
      ∫ t : SuzukiApertureInterval a,
        ∫ u : SuzukiApertureInterval a,
          (starRingEnd ℂ) (f u) *
            (starRingEnd ℂ) (suzukiScrewKernel (t : ℝ) (u : ℝ)) * g t
          ∂volume ∂volume := by
    rw [inner_suzukiApertureL2_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [suzukiScrewIntegralOperator_coeFn ha f] with t ht
    rw [ht, ← integral_conj, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with u
    simp only [map_mul]
    ring
  have hR : inner ℂ f (suzukiScrewIntegralOperator a g) =
      ∫ u : SuzukiApertureInterval a,
        ∫ t : SuzukiApertureInterval a,
          (starRingEnd ℂ) (f u) *
            (starRingEnd ℂ) (suzukiScrewKernel (t : ℝ) (u : ℝ)) * g t
          ∂volume ∂volume := by
    rw [inner_suzukiApertureL2_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [suzukiScrewIntegralOperator_coeFn ha g] with u hu
    rw [hu, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [suzukiScrewKernel_conj_swap]
    ring
  change inner ℂ (suzukiScrewIntegralOperator a f) g =
    inner ℂ f (suzukiScrewIntegralOperator a g)
  rw [hL, hR]
  exact integral_integral_swap (integrable_suzukiScrewKernel_pair hC f g)

/-- Signed greedy enumeration of the eigenvalues of Suzuki's compact self-adjoint operator.
`LidskiiSelfAdjoint` proves that every nonzero eigenvalue occurs, with multiplicity. -/
noncomputable def suzukiScrewEigenvalue (a : ℝ) (n : ℕ) : ℝ :=
  ContinuousLinearMap.sgVal (suzukiScrewIntegralOperator a) n

/-- Lidskii formula for Suzuki's literal operator. -/
theorem suzukiScrewIntegralOperator_opTrace_eq_tsum_eigenvalues
    {a : ℝ} (ha : 0 < a) :
    ContinuousLinearMap.opTrace (suzukiScrewIntegralOperator a) =
      ∑' n : ℕ, ((suzukiScrewEigenvalue a n : ℝ) : ℂ) := by
  obtain ⟨A, B, hA, hB, hfac⟩ := suzukiScrewIntegralOperator_isTraceClass a
  have hcpt : IsCompactOperator (suzukiScrewIntegralOperator a) := by
    rw [hfac]
    exact (hA.comp_right B).isCompactOperator
  simpa only [suzukiScrewEigenvalue] using
    (ContinuousLinearMap.opTrace_eq_tsum_sgVal
      (S := suzukiScrewIntegralOperator a)
      (A := A) (B := B)
      hcpt (suzukiScrewIntegralOperator_isSymmetric ha.le)
      hA hB hfac)

/-- Exact unconditional Suzuki trace/eigenvalue/diagonal-integral identity. -/
theorem suzukiScrewIntegralOperator_eigenvalue_sum_eq_integral_diagonal
    {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, ((suzukiScrewEigenvalue a n : ℝ) : ℂ)) =
      ∫ t : SuzukiApertureInterval a,
        suzukiScrewKernel (t : ℝ) (t : ℝ) ∂volume := by
  rw [← suzukiScrewIntegralOperator_opTrace_eq_tsum_eigenvalues ha,
    opTrace_suzukiScrewIntegralOperator_eq_integral_diagonal ha.le]

end RHTower
