import GaloisForLFunctions.RHTower.BurnolCoPoissonTwoPrimeJointJets
import GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedContinuousLowerJetSystem
import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceDilation

/-!
# Canonical joint co-Poisson jets and their aperture cost

The common kernel of the original and Fourier leading completed Mellin jets
is closed and Fourier invariant inside the co-Poisson source. Orthogonal
projection off that kernel preserves both readings and gives their unique
minimum-norm source representative. Two original primes supply actual
preimages at their common aperture.

All literal integrals are used in the strict right half of the open strip.
The exact Xi multiplicity cancels the lower terms in the differentiated
Mellin dilation law. Canonical projection is coherent with this transport,
but the aperture shrinks and the two characters are reciprocal. Fixed
one-sided readings consequently have arbitrarily small minimum norm as
apertures shrink. At a fixed aperture, canonical projection of the original
window retains its strict bias after the two actual jet normalizations.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower

/-- The actual top completed Mellin jet, continuously extended from the Sonine carrier. -/
def burnolCoPoissonJointJetReader (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    evenSubspace →L[ℂ] ℂ := by
  letI : CompleteSpace (soninExtendedSpace b) :=
    (isClosed_soninExtendedSpace hb).completeSpace_coe
  exact (Classical.choose (exists_soninExtendedCompletedMellinJetEvaluator hb
    (burnolCoPoissonXiConormalOrder rho) hright
    (xi_divisor_support_re_mem_open_unit rho).2)).comp
      (soninExtendedSpace b).orthogonalProjectionOnto

theorem burnolCoPoissonJointJetReader_apply {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    burnolCoPoissonJointJetReader b hb rho hright f =
      iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w (f : SoninL2)) (rho : ℂ) := by
  letI : CompleteSpace (soninExtendedSpace b) :=
    (isClosed_soninExtendedSpace hb).completeSpace_coe
  have hfE := burnolCoPoissonSourceSpace_le_soninExtendedSpace hb hf
  change Classical.choose (exists_soninExtendedCompletedMellinJetEvaluator hb
    (burnolCoPoissonXiConormalOrder rho) hright
    (xi_divisor_support_re_mem_open_unit rho).2)
      ((soninExtendedSpace b).orthogonalProjectionOnto f) = _
  rw [show (soninExtendedSpace b).orthogonalProjectionOnto f = ⟨f, hfE⟩ from
    (soninExtendedSpace b).orthogonalProjectionOnto_mem_subspace_eq_self ⟨f, hfE⟩]
  exact Classical.choose_spec (exists_soninExtendedCompletedMellinJetEvaluator hb
    (burnolCoPoissonXiConormalOrder rho) hright
    (xi_divisor_support_re_mem_open_unit rho).2) ⟨f, hfE⟩

/-- Both completed top-jet readings on the same vector. -/
def burnolCoPoissonJointJetMap (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    evenSubspace →L[ℂ] ℂ × ℂ :=
  (burnolCoPoissonJointJetReader b hb rho hright).prod
    ((burnolCoPoissonJointJetReader b hb rho hright).comp
      soninCosineUnitary.toLinearIsometry.toContinuousLinearMap)

/-- The closed common kernel inside the actual co-Poisson source. -/
def burnolCoPoissonJointJetKernel (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    Submodule ℂ evenSubspace :=
  burnolCoPoissonSourceSpace b ⊓ (burnolCoPoissonJointJetMap b hb rho hright).ker

theorem isClosed_burnolCoPoissonJointJetKernel (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    IsClosed (burnolCoPoissonJointJetKernel b hb rho hright : Set evenSubspace) :=
  (isClosed_burnolCoPoissonSourceSpace b).inter
    (burnolCoPoissonJointJetMap b hb rho hright).isClosed_ker

theorem burnolCoPoissonJointJetMap_cosine (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) (f : evenSubspace) :
    burnolCoPoissonJointJetMap b hb rho hright (soninCosineUnitary f) =
      (burnolCoPoissonJointJetMap b hb rho hright f).swap := by
  simp [burnolCoPoissonJointJetMap, soninCosineUnitary_involutive]

theorem soninCosineUnitary_mem_coPoissonJointJetKernel {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonJointJetKernel b hb rho hright) :
    soninCosineUnitary f ∈ burnolCoPoissonJointJetKernel b hb rho hright := by
  refine ⟨soninCosineUnitary_mem_coPoissonSourceSpace hf.1, ?_⟩
  change burnolCoPoissonJointJetMap b hb rho hright (soninCosineUnitary f) = 0
  rw [burnolCoPoissonJointJetMap_cosine]
  have hzero : burnolCoPoissonJointJetMap b hb rho hright f = 0 := hf.2
  simp [hzero]

/-- Canonical representative with the same two leading jets. -/
def burnolCoPoissonJointJetCanonical (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    evenSubspace →L[ℂ] evenSubspace := by
  letI : CompleteSpace (burnolCoPoissonJointJetKernel b hb rho hright) :=
    (isClosed_burnolCoPoissonJointJetKernel b hb rho hright).completeSpace_coe
  exact ContinuousLinearMap.id ℂ evenSubspace -
    (burnolCoPoissonJointJetKernel b hb rho hright).starProjection

theorem burnolCoPoissonJointJetCanonical_mem {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    burnolCoPoissonJointJetCanonical b hb rho hright f ∈ burnolCoPoissonSourceSpace b := by
  letI : CompleteSpace (burnolCoPoissonJointJetKernel b hb rho hright) :=
    (isClosed_burnolCoPoissonJointJetKernel b hb rho hright).completeSpace_coe
  exact (burnolCoPoissonSourceSpace b).sub_mem hf
    ((burnolCoPoissonJointJetKernel b hb rho hright).starProjection_apply_mem f).1

theorem burnolCoPoissonJointJetCanonical_readings (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) (f : evenSubspace) :
    burnolCoPoissonJointJetMap b hb rho hright
      (burnolCoPoissonJointJetCanonical b hb rho hright f) =
        burnolCoPoissonJointJetMap b hb rho hright f := by
  letI : CompleteSpace (burnolCoPoissonJointJetKernel b hb rho hright) :=
    (isClosed_burnolCoPoissonJointJetKernel b hb rho hright).completeSpace_coe
  have hz := ((burnolCoPoissonJointJetKernel b hb rho hright).starProjection_apply_mem f).2
  change burnolCoPoissonJointJetMap b hb rho hright
    (f - (burnolCoPoissonJointJetKernel b hb rho hright).starProjection f) = _
  rw [map_sub, show burnolCoPoissonJointJetMap b hb rho hright
    ((burnolCoPoissonJointJetKernel b hb rho hright).starProjection f) = 0 from hz,
    sub_zero]

/-- Keeping both measurements restores exact Fourier covariance of the canonical representative. -/
theorem burnolCoPoissonJointJetCanonical_cosine (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) (f : evenSubspace) :
    burnolCoPoissonJointJetCanonical b hb rho hright (soninCosineUnitary f) =
      soninCosineUnitary (burnolCoPoissonJointJetCanonical b hb rho hright f) := by
  let K := burnolCoPoissonJointJetKernel b hb rho hright
  letI : CompleteSpace K :=
    (isClosed_burnolCoPoissonJointJetKernel b hb rho hright).completeSpace_coe
  have hproj : K.starProjection (soninCosineUnitary f) =
      soninCosineUnitary (K.starProjection f) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact soninCosineUnitary_mem_coPoissonJointJetKernel hb rho hright
        (K.starProjection_apply_mem f)
    · intro g hg
      have hFg : soninCosineUnitary g ∈ K :=
        soninCosineUnitary_mem_coPoissonJointJetKernel hb rho hright hg
      calc
        ⟪soninCosineUnitary f - soninCosineUnitary (K.starProjection f), g⟫_ℂ =
            ⟪soninCosineUnitary (f - K.starProjection f),
              soninCosineUnitary (soninCosineUnitary g)⟫_ℂ := by
                rw [map_sub, soninCosineUnitary_involutive]
        _ = ⟪f - K.starProjection f, soninCosineUnitary g⟫_ℂ :=
          soninCosineUnitary.inner_map_map _ _
        _ = 0 := Submodule.starProjection_inner_eq_zero f _ hFg
  change soninCosineUnitary f - K.starProjection (soninCosineUnitary f) =
    soninCosineUnitary (f - K.starProjection f)
  rw [hproj, map_sub]

theorem burnolCoPoissonJointJetCanonical_eq_of_readings {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f g : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b)
    (hg : g ∈ burnolCoPoissonSourceSpace b)
    (hread : burnolCoPoissonJointJetMap b hb rho hright f =
      burnolCoPoissonJointJetMap b hb rho hright g) :
    burnolCoPoissonJointJetCanonical b hb rho hright f =
      burnolCoPoissonJointJetCanonical b hb rho hright g := by
  let K := burnolCoPoissonJointJetKernel b hb rho hright
  letI : CompleteSpace K :=
    (isClosed_burnolCoPoissonJointJetKernel b hb rho hright).completeSpace_coe
  have hfg : f - g ∈ K := ⟨(burnolCoPoissonSourceSpace b).sub_mem hf hg, by
    change burnolCoPoissonJointJetMap b hb rho hright (f - g) = 0
    rw [map_sub, hread, sub_self]⟩
  have hP : K.starProjection (f - g) = f - g := K.starProjection_eq_self_iff.mpr hfg
  change f - K.starProjection f = g - K.starProjection g
  rw [map_sub] at hP
  exact sub_eq_sub_iff_sub_eq_sub.mpr hP.symm

/-- Exact energy split into the canonical source and the discarded joint-null source. -/
theorem burnolCoPoissonJointJetCanonical_energy (b : ℝ) (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) (f : evenSubspace) :
    ‖f‖ ^ 2 = ‖burnolCoPoissonJointJetCanonical b hb rho hright f‖ ^ 2 +
      ‖f - burnolCoPoissonJointJetCanonical b hb rho hright f‖ ^ 2 := by
  let K := burnolCoPoissonJointJetKernel b hb rho hright
  letI : CompleteSpace K :=
    (isClosed_burnolCoPoissonJointJetKernel b hb rho hright).completeSpace_coe
  have h := K.norm_sq_eq_add_norm_sq_starProjection f
  rw [Submodule.starProjection_orthogonal_val] at h
  change ‖f‖ ^ 2 = ‖f - K.starProjection f‖ ^ 2 +
    ‖f - (f - K.starProjection f)‖ ^ 2
  simpa [add_comm] using h

/-- Minimality is proved on the entire closed co-Poisson source. -/
theorem burnolCoPoissonJointJetCanonical_minimal {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f g : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b)
    (hg : g ∈ burnolCoPoissonSourceSpace b)
    (hread : burnolCoPoissonJointJetMap b hb rho hright g =
      burnolCoPoissonJointJetMap b hb rho hright f) :
    ‖burnolCoPoissonJointJetCanonical b hb rho hright f‖ ≤ ‖g‖ := by
  have h := burnolCoPoissonJointJetCanonical_energy b hb rho hright g
  rw [burnolCoPoissonJointJetCanonical_eq_of_readings hb rho hright hg hf hread] at h
  nlinarith [norm_nonneg g,
    norm_nonneg (burnolCoPoissonJointJetCanonical b hb rho hright f),
    sq_nonneg ‖g - burnolCoPoissonJointJetCanonical b hb rho hright f‖]


theorem burnolCoPoissonJointJetMap_apply {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    burnolCoPoissonJointJetMap b hb rho hright f =
      (iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w (f : SoninL2)) (rho : ℂ),
       iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
        (fun w => soninMellinEvaluation w (soninCosineUnitary f : SoninL2)) (rho : ℂ)) := by
  exact Prod.ext (burnolCoPoissonJointJetReader_apply hb rho hright hf)
    (burnolCoPoissonJointJetReader_apply hb rho hright
      (soninCosineUnitary_mem_coPoissonSourceSpace hf))

/-- Two original primes supply the actual preimage; no abstract surjectivity is assumed. -/
theorem burnolCoPoissonJointJet_exists_minimal
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) (u v : ℂ) :
    let b := Real.exp (-2 * (Real.log p + Real.log q))
    ∃ f : evenSubspace, f ∈ burnolCoPoissonSourceSpace b ∧
      burnolCoPoissonJointJetMap b (Real.exp_pos _) rho hright f = (u, v) ∧
      ∀ g ∈ burnolCoPoissonSourceSpace b,
        burnolCoPoissonJointJetMap b (Real.exp_pos _) rho hright g = (u, v) →
          ‖f‖ ≤ ‖g‖ := by
  dsimp only
  let b := Real.exp (-2 * (Real.log p + Real.log q))
  obtain ⟨L, hL, c, d, _, hf, _, hu, hv⟩ :=
    burnolWindowJointSource_two_prime_interpolation hp hq hpq rho u v
  let f := burnolWindowJointSource L hL c d
  have hfC : f ∈ burnolCoPoissonSourceSpace b :=
    (burnolCoPoissonAlgebraicSourceSpace b).le_topologicalClosure hf
  have hread : burnolCoPoissonJointJetMap b (Real.exp_pos _) rho hright f = (u, v) := by
    rw [burnolCoPoissonJointJetMap_apply (Real.exp_pos _) rho hright hfC]
    exact Prod.ext hu hv
  refine ⟨burnolCoPoissonJointJetCanonical b (Real.exp_pos _) rho hright f,
    burnolCoPoissonJointJetCanonical_mem (Real.exp_pos _) rho hright hfC, ?_, ?_⟩
  · rw [burnolCoPoissonJointJetCanonical_readings, hread]
  · intro g hg hgread
    exact burnolCoPoissonJointJetCanonical_minimal (Real.exp_pos _) rho hright hfC hg
      (hgread.trans hread.symm)

/-- Equal-norm minimizers with the same two readings are equal as actual sources. -/
theorem burnolCoPoissonJointJetCanonical_unique {b : ℝ} (hb : 0 < b)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f g : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b)
    (hg : g ∈ burnolCoPoissonSourceSpace b)
    (hread : burnolCoPoissonJointJetMap b hb rho hright g =
      burnolCoPoissonJointJetMap b hb rho hright f)
    (hnorm : ‖g‖ = ‖burnolCoPoissonJointJetCanonical b hb rho hright f‖) :
    g = burnolCoPoissonJointJetCanonical b hb rho hright f := by
  have h := burnolCoPoissonJointJetCanonical_energy b hb rho hright g
  rw [burnolCoPoissonJointJetCanonical_eq_of_readings hb rho hright hg hf hread] at h
  have hz : ‖g - burnolCoPoissonJointJetCanonical b hb rho hright f‖ = 0 := by
    rw [hnorm] at h
    nlinarith [norm_nonneg (g - burnolCoPoissonJointJetCanonical b hb rho hright f)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Vanishing of all lower source jets leaves precisely the Mellin dilation character. -/
theorem iteratedDeriv_coPoisson_topJet_dilation {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
      (fun w => soninMellinEvaluation w (evenDilationCLM r hr f : SoninL2)) (rho : ℂ) =
      (r : ℂ) ^ ((rho : ℂ) - 1 / 2) *
        iteratedDeriv (burnolCoPoissonXiConormalOrder rho)
          (fun w => soninMellinEvaluation w (f : SoninL2)) (rho : ℂ) := by
  let m := burnolCoPoissonXiConormalOrder rho
  let F : soninExtendedSpace b :=
    ⟨f, burnolCoPoissonSourceSpace_le_soninExtendedSpace hb hf⟩
  have hraw : AnalyticAt ℂ (fun w => soninMellinEvaluation w (f : SoninL2)) (rho : ℂ) := by
    have hc : AnalyticAt ℂ (soninExtendedCompletedMellinContinuation b hb F) (rho : ℂ) := by
      exact (soninEval_analyticAt hb
        (soninExtendedToSoninEvenExtended b hb F).property.1
        (soninExtendedToSoninEvenExtended b hb F).property.2
        (by linarith) (xi_divisor_support_re_mem_open_unit rho).2).mul
        (analyticAt_mellinCompletionFactor_of_re_pos (by linarith))
    exact hc.congr (eventuallyEq_soninEval_mul_completion_soninMellinEvaluation hb
      hright (xi_divisor_support_re_mem_open_unit rho).2 F)
  have hchar : ContDiffAt ℂ m (fun w : ℂ => (r : ℂ) ^ (w - 1 / 2)) (rho : ℂ) := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')]
    fun_prop
  have heq : (fun w => soninMellinEvaluation w (evenDilationCLM r hr f : SoninL2)) =
      (fun w : ℂ => (r : ℂ) ^ (w - 1 / 2)) *
        (fun w => soninMellinEvaluation w (f : SoninL2)) := by
    funext w
    exact soninMellinEvaluation_evenDilation w r hr f
  rw [heq, iteratedDeriv_mul hchar hraw.contDiffAt, Finset.sum_eq_single 0]
  · simp [m]
  · intro i hi hi0
    have him : m - i < m := by
      have hile : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      omega
    rw [iteratedDeriv_soninMellinEvaluation_eq_zero_of_mem_burnolCoPoissonSourceSpace_of_lt
      hb rho hright him hf, mul_zero]
  · simp

/-- The exact joint transport has reciprocal characters and a smaller aperture. -/
theorem burnolCoPoissonJointJetMap_dilation {b r : ℝ} (hb : 0 < b) (hr : 1 ≤ r)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    burnolCoPoissonJointJetMap (r⁻¹ * b) (mul_pos (inv_pos.mpr (zero_lt_one.trans_le hr)) hb)
      rho hright (evenDilationCLM r (zero_lt_one.trans_le hr) f) =
      ((r : ℂ) ^ ((rho : ℂ) - 1 / 2) *
        (burnolCoPoissonJointJetMap b hb rho hright f).1,
       ((r : ℂ) ^ ((rho : ℂ) - 1 / 2))⁻¹ *
        (burnolCoPoissonJointJetMap b hb rho hright f).2) := by
  have hr0 := zero_lt_one.trans_le hr
  rw [burnolCoPoissonJointJetMap_apply _ rho hright
    (evenDilation_mem_coPoissonSourceSpace hb hr hf),
    burnolCoPoissonJointJetMap_apply hb rho hright hf]
  apply Prod.ext
  · exact iteratedDeriv_coPoisson_topJet_dilation hb hr0 rho hright hf
  · have harg : (r : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr0.le]
      exact ne_of_lt Real.pi_pos
    simp only [soninCosineUnitary_evenDilation]
    rw [iteratedDeriv_coPoisson_topJet_dilation hb (inv_pos.mpr hr0) rho hright
      (soninCosineUnitary_mem_coPoissonSourceSpace hf), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg]


/-- Removing a joint-null source before dilation does not change the final canonical source. -/
theorem burnolCoPoissonJointJetCanonical_dilation_canonical {b r : ℝ} (hb : 0 < b)
    (hr : 1 ≤ r) (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    let hr0 := zero_lt_one.trans_le hr
    let hb' := mul_pos (inv_pos.mpr hr0) hb
    burnolCoPoissonJointJetCanonical (r⁻¹ * b) hb' rho hright
      (evenDilationCLM r hr0 (burnolCoPoissonJointJetCanonical b hb rho hright f)) =
    burnolCoPoissonJointJetCanonical (r⁻¹ * b) hb' rho hright
      (evenDilationCLM r hr0 f) := by
  dsimp only
  have hPf := burnolCoPoissonJointJetCanonical_mem hb rho hright hf
  apply burnolCoPoissonJointJetCanonical_eq_of_readings _ rho hright
    (evenDilation_mem_coPoissonSourceSpace hb hr hPf)
    (evenDilation_mem_coPoissonSourceSpace hb hr hf)
  rw [burnolCoPoissonJointJetMap_dilation hb hr rho hright hPf,
    burnolCoPoissonJointJetMap_dilation hb hr rho hright hf,
    burnolCoPoissonJointJetCanonical_readings]


/-- Canonical transport retains a one-sided reading with its exact norm and null-source cost. -/
theorem burnolCoPoissonJointJet_minimal_dilation_cost {b r : ℝ} (hb : 0 < b) (hr : 1 ≤ r)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) (u : ℂ)
    (hread : burnolCoPoissonJointJetMap b hb rho hright f = (u, 0)) :
    let hr0 := zero_lt_one.trans_le hr
    let hb' := mul_pos (inv_pos.mpr hr0) hb
    let v := ((r : ℂ) ^ ((rho : ℂ) - 1 / 2))⁻¹ • evenDilationCLM r hr0 f
    let g := burnolCoPoissonJointJetCanonical (r⁻¹ * b) hb' rho hright v
    g ∈ burnolCoPoissonSourceSpace (r⁻¹ * b) ∧
      burnolCoPoissonJointJetMap (r⁻¹ * b) hb' rho hright g = (u, 0) ∧
      ‖g‖ ≤ r ^ (1 / 2 - (rho : ℂ).re) * ‖f‖ ∧
      (r ^ (1 / 2 - (rho : ℂ).re) * ‖f‖) ^ 2 = ‖g‖ ^ 2 + ‖v - g‖ ^ 2 ∧
      ∀ h ∈ burnolCoPoissonSourceSpace (r⁻¹ * b),
        burnolCoPoissonJointJetMap (r⁻¹ * b) hb' rho hright h = (u, 0) →
          ‖g‖ ≤ ‖h‖ := by
  dsimp only
  let hr0 := zero_lt_one.trans_le hr
  let hb' := mul_pos (inv_pos.mpr hr0) hb
  let lam := (r : ℂ) ^ ((rho : ℂ) - 1 / 2)
  let v := lam⁻¹ • evenDilationCLM r hr0 f
  have hlam : lam ≠ 0 := by
    dsimp only [lam]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne')]
    exact Complex.exp_ne_zero _
  have hv : v ∈ burnolCoPoissonSourceSpace (r⁻¹ * b) :=
    (burnolCoPoissonSourceSpace (r⁻¹ * b)).smul_mem _
      (evenDilation_mem_coPoissonSourceSpace hb hr hf)
  have hvread : burnolCoPoissonJointJetMap (r⁻¹ * b) hb' rho hright v = (u, 0) := by
    dsimp only [v]
    rw [map_smul, burnolCoPoissonJointJetMap_dilation hb hr rho hright hf, hread]
    change (lam⁻¹ * (lam * u), lam⁻¹ * (lam⁻¹ * 0)) = (u, 0)
    simp [hlam]
  have hvnorm : ‖v‖ = r ^ (1 / 2 - (rho : ℂ).re) * ‖f‖ := by
    rw [show v = lam⁻¹ • evenDilationCLM r hr0 f from rfl, norm_smul,
      norm_evenDilationCLM_apply, norm_inv,
      show ‖lam‖ = r ^ ((rho : ℂ).re - 1 / 2) by
        simp [lam, Complex.norm_cpow_eq_rpow_re_of_pos hr0], ← Real.rpow_neg hr0.le]
    congr 2
    ring
  refine ⟨burnolCoPoissonJointJetCanonical_mem hb' rho hright hv, ?_, ?_, ?_, ?_⟩
  · rw [burnolCoPoissonJointJetCanonical_readings, hvread]
  · exact (burnolCoPoissonJointJetCanonical_minimal hb' rho hright hv hv rfl).trans
      hvnorm.le
  · rw [← hvnorm]
    exact burnolCoPoissonJointJetCanonical_energy _ hb' rho hright v
  · intro h hh hhread
    exact burnolCoPoissonJointJetCanonical_minimal hb' rho hright hv hh
      (hhread.trans hvread.symm)

/-- The actual two-prime source has minimum-norm fixed readings at arbitrarily small norm
when the aperture is allowed to shrink. -/
theorem burnolCoPoissonJointJet_small_minimal_sources
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {eps : ℝ} (heps : 0 < eps) :
    let b := Real.exp (-2 * (Real.log p + Real.log q))
    ∃ (r : ℝ) (hr : 1 ≤ r) (g : evenSubspace),
      g ∈ burnolCoPoissonSourceSpace (r⁻¹ * b) ∧
      burnolCoPoissonJointJetMap (r⁻¹ * b)
        (mul_pos (inv_pos.mpr (zero_lt_one.trans_le hr)) (Real.exp_pos _)) rho hright g =
          (1, 0) ∧
      0 < ‖g‖ ∧ ‖g‖ < eps ∧
      ∀ h ∈ burnolCoPoissonSourceSpace (r⁻¹ * b),
        burnolCoPoissonJointJetMap (r⁻¹ * b)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans_le hr)) (Real.exp_pos _)) rho hright h =
            (1, 0) → ‖g‖ ≤ ‖h‖ := by
  dsimp only
  let b := Real.exp (-2 * (Real.log p + Real.log q))
  obtain ⟨f, hf, hfread, _⟩ := burnolCoPoissonJointJet_exists_minimal hp hq hpq rho hright 1 0
  have hlim : Tendsto (fun r : ℝ => r ^ (1 / 2 - (rho : ℂ).re) * ‖f‖) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hright)).mul_const ‖f‖
    simpa [neg_sub] using ht
  obtain ⟨r, hr, hrs⟩ := (eventually_ge_atTop (1 : ℝ)).and
    (hlim.eventually (gt_mem_nhds heps)) |>.exists
  let hr0 := zero_lt_one.trans_le hr
  let hb' := mul_pos (inv_pos.mpr hr0) (Real.exp_pos (-2 * (Real.log p + Real.log q)))
  let v := ((r : ℂ) ^ ((rho : ℂ) - 1 / 2))⁻¹ • evenDilationCLM r hr0 f
  let g := burnolCoPoissonJointJetCanonical (r⁻¹ * b) hb' rho hright v
  obtain ⟨hg, hgread, hgnorm, _, hgmin⟩ :=
    burnolCoPoissonJointJet_minimal_dilation_cost (Real.exp_pos _) hr rho hright hf 1 hfread
  have hgpos : 0 < ‖g‖ := by
    apply norm_pos_iff.mpr
    intro hz
    change burnolCoPoissonJointJetMap (r⁻¹ * b) hb' rho hright g = (1, 0) at hgread
    rw [hz, map_zero] at hgread
    have hz' := congrArg Prod.fst hgread
    norm_num at hz'
  exact ⟨r, hr, g, hg, hgread, hgpos, hgnorm.trans_lt hrs, hgmin⟩


/-- Canonical projection retains the original window's strict normalization bias. -/
theorem burnolCoPoissonJointJetCanonical_window_radial_bias {L : ℝ} (hL : 0 < L)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    let b := Real.exp (-(2 * L))
    let f := burnolWindowJointSource L hL 1 0
    let g := burnolCoPoissonJointJetCanonical b (Real.exp_pos _) rho hright f
    Real.exp (L * (2 * (rho : ℂ).re - 1)) *
        ‖(burnolWindowCompletedTopJet L hL rho)⁻¹ • g‖ ^ 2 <
      ‖(burnolWindowFourierCompletedTopJet L hL rho)⁻¹ • soninCosineUnitary g‖ ^ 2 := by
  dsimp only
  let b := Real.exp (-(2 * L))
  let f := burnolWindowJointSource L hL 1 0
  let g := burnolCoPoissonJointJetCanonical b (Real.exp_pos _) rho hright f
  have hf : f ∈ burnolCoPoissonSourceSpace b :=
    (burnolCoPoissonAlgebraicSourceSpace b).le_topologicalClosure
      (burnolWindowJointSource_mem_algebraicSource (Real.exp_pos _) hL le_rfl 1 0).1
  obtain ⟨hJ, hK⟩ := burnolWindowCompletedTopJets_ne_zero hL rho
  have hread : (burnolCoPoissonJointJetMap b (Real.exp_pos _) rho hright g).1 =
      burnolWindowCompletedTopJet L hL rho := by
    rw [show g = burnolCoPoissonJointJetCanonical b (Real.exp_pos _) rho hright f from rfl,
      burnolCoPoissonJointJetCanonical_readings,
      burnolCoPoissonJointJetMap_apply (Real.exp_pos _) rho hright hf]
    simpa only [f, one_mul, zero_mul, add_zero] using
      (burnolWindowJointSource_top_jets hL rho 1 0).1
  have hg : g ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hread
    exact hJ hread.symm
  have hgpos := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hg)
  have hJpos := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hJ)
  have hKpos := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hK)
  have hX : ‖(burnolWindowCompletedTopJet L hL rho)⁻¹ • g‖ =
      ‖g‖ / ‖burnolWindowCompletedTopJet L hL rho‖ := by
    rw [norm_smul, norm_inv, div_eq_mul_inv, mul_comm]
  have hY : ‖(burnolWindowFourierCompletedTopJet L hL rho)⁻¹ • soninCosineUnitary g‖ =
      ‖g‖ / ‖burnolWindowFourierCompletedTopJet L hL rho‖ := by
    rw [norm_smul, norm_inv, soninCosineUnitary.norm_map, div_eq_mul_inv, mul_comm]
  change Real.exp (L * (2 * (rho : ℂ).re - 1)) *
      ‖(burnolWindowCompletedTopJet L hL rho)⁻¹ • g‖ ^ 2 <
    ‖(burnolWindowFourierCompletedTopJet L hL rho)⁻¹ • soninCosineUnitary g‖ ^ 2
  rw [hX, hY, div_pow, div_pow, ← mul_div_assoc, div_lt_div_iff₀ hJpos hKpos]
  have hs := mul_lt_mul_of_pos_left
    (burnolWindowCompletedTopJets_strict_radial_bias hL rho hright) hgpos
  nlinarith


/-- The literal leading-jet reader has no aperture-uniform Hilbert bound at a right-half Xi divisor. -/
theorem burnolCoPoissonJointJet_no_uniform_aperture_bound
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    let b := Real.exp (-2 * (Real.log p + Real.log q))
    ¬ ∃ C : ℝ, ∀ (r : ℝ) (hr : 1 ≤ r) (g : evenSubspace),
      g ∈ burnolCoPoissonSourceSpace (r⁻¹ * b) →
      ‖(burnolCoPoissonJointJetMap (r⁻¹ * b)
        (mul_pos (inv_pos.mpr (zero_lt_one.trans_le hr)) (Real.exp_pos _))
        rho hright g).1‖ ≤ C * ‖g‖ := by
  dsimp only
  rintro ⟨C, hC⟩
  have hden : 0 < |C| + 1 := by positivity
  obtain ⟨r, hr, g, hg, hgread, _, hgsmall, _⟩ :=
    burnolCoPoissonJointJet_small_minimal_sources hp hq hpq rho hright
      (one_div_pos.mpr hden)
  have hbound := hC r hr g hg
  rw [hgread] at hbound
  norm_num at hbound
  change 1 ≤ C * ‖g‖ at hbound
  have hsmall := (lt_div_iff₀ hden).mp hgsmall
  have hle : C * ‖g‖ ≤ (|C| + 1) * ‖g‖ :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (norm_nonneg g)
  nlinarith

end RHTower
