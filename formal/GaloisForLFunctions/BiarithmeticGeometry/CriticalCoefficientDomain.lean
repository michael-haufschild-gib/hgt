import GaloisForLFunctions.BiarithmeticGeometry.CriticalPartialSumCore
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationCompletion

/-!
# Closure and continuous duality of the critical coefficient domain

Square-summable partial sums define a complex subspace of `ell1`.
Corrected finite coefficients identify its closure with the kernel of
total evaluation. Evaluation gives the exact distance to that kernel,
and the corpus augmentation theorem identifies every continuous
functional annihilating the critical domain.
-/

noncomputable section
open Finset Filter Topology
open HTGeometry.ConstraintMotiveRelativity
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The normalized complex coefficient space of one critical prime tower. -/
abbrev CriticalCoefficientSpace := lp (fun _ : ℕ => ℂ) 1

/-- Total coefficient evaluation, using the existing continuous augmentation. -/
def criticalTotalEvaluation : CriticalCoefficientSpace →L[ℂ] ℂ := augCLM

theorem criticalTotalEvaluation_apply (g : CriticalCoefficientSpace) :
    criticalTotalEvaluation g = ∑' r, g r := by
  simp only [criticalTotalEvaluation, augCLM, wtCLM_apply, one_mul]

theorem norm_criticalTotalEvaluation_le (g : CriticalCoefficientSpace) :
    ‖criticalTotalEvaluation g‖ ≤ ‖g‖ := by
  rw [criticalTotalEvaluation_apply, norm_eq_tsum_one]
  exact norm_tsum_le_tsum_norm (summable_norm_lp_one g)

theorem criticalTotalEvaluation_single (z : ℂ) :
    criticalTotalEvaluation (lp.single 1 0 z) = z := by
  rw [criticalTotalEvaluation_apply]
  simp only [lp.coeFn_single, tsum_pi_single]

private theorem criticalPartialSum_add (g h : CriticalCoefficientSpace) (M : ℕ) :
    criticalCoefficientPartialSum (g + h : CriticalCoefficientSpace) M =
      criticalCoefficientPartialSum g M + criticalCoefficientPartialSum h M := by
  simp only [criticalCoefficientPartialSum, lp.coeFn_add, Pi.add_apply, sum_add_distrib]

private theorem criticalPartialSum_smul (z : ℂ) (g : CriticalCoefficientSpace) (M : ℕ) :
    criticalCoefficientPartialSum (z • g : CriticalCoefficientSpace) M =
      z * criticalCoefficientPartialSum g M := by
  simp only [criticalCoefficientPartialSum, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_sum]

private theorem norm_add_sq_bound (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have htri := pow_le_pow_left₀ (norm_nonneg (u + v)) (norm_add_le u v) 2
  nlinarith only [htri, sq_nonneg (‖u‖ - ‖v‖)]

private theorem summable_sq_criticalPartialSum_add (g h : CriticalCoefficientSpace)
    (hg : Summable fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2)
    (hh : Summable fun M => ‖criticalCoefficientPartialSum h M‖ ^ 2) :
    Summable (fun M => ‖criticalCoefficientPartialSum (g + h : CriticalCoefficientSpace) M‖ ^ 2) := by
  apply ((hg.mul_left 2).add (hh.mul_left 2)).of_nonneg_of_le (fun M => sq_nonneg _)
  intro M
  rw [criticalPartialSum_add]
  exact norm_add_sq_bound _ _

private theorem summable_sq_criticalPartialSum_smul (z : ℂ) (g : CriticalCoefficientSpace)
    (hg : Summable fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2) :
    Summable (fun M => ‖criticalCoefficientPartialSum (z • g : CriticalCoefficientSpace) M‖ ^ 2) := by
  simpa only [criticalPartialSum_smul, norm_mul, mul_pow] using hg.mul_left (‖z‖ ^ 2)

/-- Normalized coefficients whose inclusive partial sums have finite square energy. -/
def criticalCoefficientDomain : Submodule ℂ CriticalCoefficientSpace where
  carrier := {g | Summable fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2}
  zero_mem' := by
    change Summable (fun M => ‖criticalCoefficientPartialSum (0 : CriticalCoefficientSpace) M‖ ^ 2)
    simpa only [criticalCoefficientPartialSum, lp.coeFn_zero, Pi.zero_apply,
      sum_const_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  add_mem' := fun hg hh => summable_sq_criticalPartialSum_add _ _ hg hh
  smul_mem' := fun z g hg => summable_sq_criticalPartialSum_smul z g hg

theorem mem_criticalCoefficientDomain (g : CriticalCoefficientSpace) :
    g ∈ criticalCoefficientDomain ↔
      Summable (fun M => ‖criticalCoefficientPartialSum g M‖ ^ 2) := Iff.rfl

/-- Critical finite square energy forces zero total evaluation. -/
theorem criticalTotalEvaluation_eq_zero_of_mem {g : CriticalCoefficientSpace}
    (hg : g ∈ criticalCoefficientDomain) : criticalTotalEvaluation g = 0 := by
  rw [criticalTotalEvaluation_apply]
  exact tsum_eq_zero_of_summable_sq_partialSum g (summable_norm_lp_one g) hg

/-- The corrected finite core as actual elements of the normalized coefficient space. -/
def criticalFiniteCoefficientCore (g : CriticalCoefficientSpace) (N : ℕ) :
    CriticalCoefficientSpace :=
  ⟨criticalCorrectedTruncation g N, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      summable_norm_criticalCorrectedTruncation g N)⟩

theorem criticalFiniteCoefficientCore_mem (g : CriticalCoefficientSpace) (N : ℕ) :
    criticalFiniteCoefficientCore g N ∈ criticalCoefficientDomain :=
  summable_sq_partialSum_criticalCorrectedTruncation g N

/-- The finite core approaches every zero-evaluation coefficient vector in its actual norm. -/
theorem criticalFiniteCoefficientCore_tendsto (g : CriticalCoefficientSpace)
    (hg : criticalTotalEvaluation g = 0) :
    Tendsto (criticalFiniteCoefficientCore g) atTop (𝓝 g) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (N : ℕ) : ‖criticalFiniteCoefficientCore g N - g‖ =
      ∑' r, ‖criticalCorrectedTruncation g N r - g r‖ := by
    rw [norm_eq_tsum_one]
    rfl
  simp only [he]
  have hz : (∑' r, g r) = 0 := by rwa [criticalTotalEvaluation_apply] at hg
  simpa only [hz, norm_zero] using
    criticalCorrectedTruncation_norm_error_tendsto g (summable_norm_lp_one g)

/-- The closure of critical payment is precisely the zero-evaluation hyperplane. -/
theorem closure_criticalCoefficientDomain :
    closure (criticalCoefficientDomain : Set CriticalCoefficientSpace) =
      {g | criticalTotalEvaluation g = 0} := by
  apply le_antisymm
  · apply closure_minimal
    · exact fun g hg => criticalTotalEvaluation_eq_zero_of_mem hg
    · exact isClosed_singleton.preimage criticalTotalEvaluation.continuous
  · intro g hg
    exact isClosed_closure.mem_of_tendsto (criticalFiniteCoefficientCore_tendsto g hg)
      (Eventually.of_forall fun N => subset_closure (criticalFiniteCoefficientCore_mem g N))

theorem criticalCoefficientDomain_topologicalClosure :
    criticalCoefficientDomain.topologicalClosure = criticalTotalEvaluation.ker := by
  ext g
  change g ∈ closure (criticalCoefficientDomain : Set CriticalCoefficientSpace) ↔
    criticalTotalEvaluation g = 0
  rw [closure_criticalCoefficientDomain]
  rfl

/-- The total evaluation norm is attained as the distance to its kernel. -/
theorem criticalTotalEvaluation_minimum_distance (g : CriticalCoefficientSpace) :
    ∃ z : CriticalCoefficientSpace, criticalTotalEvaluation z = 0 ∧
      ‖g - z‖ = ‖criticalTotalEvaluation g‖ ∧
      ∀ w : CriticalCoefficientSpace, criticalTotalEvaluation w = 0 →
        ‖criticalTotalEvaluation g‖ ≤ ‖g - w‖ := by
  refine ⟨g - lp.single 1 0 (criticalTotalEvaluation g), ?_, ?_, ?_⟩
  · rw [map_sub, criticalTotalEvaluation_single, sub_self]
  · rw [sub_sub_cancel, lp.norm_single (by norm_num)]
  · intro w hw
    have h := norm_criticalTotalEvaluation_le (g - w)
    simpa only [map_sub, hw, sub_zero] using h

/-- Every continuous functional vanishing on critical payment is a scalar total evaluation. -/
theorem criticalCoefficientDomain_continuous_annihilator
    (L : CriticalCoefficientSpace →L[ℂ] ℂ)
    (hL : ∀ g ∈ criticalCoefficientDomain, L g = 0) :
    ∀ g, L g = L (lp.single 1 0 (1 : ℂ)) * criticalTotalEvaluation g := by
  have hclosure : closure (criticalCoefficientDomain : Set CriticalCoefficientSpace) ⊆
      {g | L g = 0} := closure_minimal hL (isClosed_singleton.preimage L.continuous)
  have hkernel : ∀ g : CriticalCoefficientSpace, augCLM g = 0 → L g = 0 := by
    intro g hg
    apply hclosure
    rw [closure_criticalCoefficientDomain]
    exact hg
  simpa only [inv_one, criticalTotalEvaluation] using
    eq_smul_augCLM_of_vanishing (P := ℕ) 0 L hkernel

end GaloisForLFunctions.BiarithmeticGeometry

