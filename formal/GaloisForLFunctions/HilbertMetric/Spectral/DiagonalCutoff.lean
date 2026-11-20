import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cutoff inversion of diagonal measurements

On the retained modes the error is rescaled measurement noise. On the discarded
modes it is the original signal. This gives an exact squared error decomposition
for any finite observation, including modes with different multiplicities.
-/

namespace GaloisForLFunctions.HilbertMetric.DiagonalCutoff

noncomputable section

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Divide by the positive gain on the retained coordinates. -/
def recover [DecidableEq ι] (kept : Finset ι) (gain : ι → Set.Ioi (0 : ℝ))
    (data : ι → E) (i : ι) : E :=
  if i ∈ kept then ((gain i : ℝ)⁻¹) • data i else 0

/-- Positive attenuation preserves injectivity on the complete set of coordinates. -/
theorem measure_injective (gain : ι → Set.Ioi (0 : ℝ)) :
    Function.Injective (fun signal : ι → E => fun i => (gain i : ℝ) • signal i) := by
  intro x y h
  funext i
  have hi := congrFun h i
  have he := congrArg (fun v : E => (gain i : ℝ)⁻¹ • v) hi
  simpa only [inv_smul_smul₀ (gain i).2.ne'] using he

/-- The retained error depends only on measurement noise. -/
theorem recover_sub [DecidableEq ι] (kept : Finset ι) (gain : ι → Set.Ioi (0 : ℝ))
    (signal noise : ι → E) (i : ι) :
    recover kept gain (fun j => (gain j : ℝ) • signal j + noise j) i - signal i =
      if i ∈ kept then (gain i : ℝ)⁻¹ • noise i else -signal i := by
  by_cases hi : i ∈ kept
  · simp only [recover, if_pos hi, smul_add, inv_smul_smul₀ (gain i).2.ne', add_sub_cancel_left]
  · simp only [recover, if_neg hi, zero_sub]

/-- Exact split into amplified retained noise and discarded signal energy. -/
theorem squared_error [DecidableEq ι] (modes kept : Finset ι)
    (gain : ι → Set.Ioi (0 : ℝ)) (signal noise : ι → E) :
    (∑ i ∈ modes, ‖recover kept gain (fun j => (gain j : ℝ) • signal j + noise j) i -
      signal i‖ ^ 2) =
      (∑ i ∈ modes with i ∈ kept, ((gain i : ℝ)⁻¹) ^ 2 * ‖noise i‖ ^ 2) +
      (∑ i ∈ modes with i ∉ kept, ‖signal i‖ ^ 2) := by
  rw [← Finset.sum_filter_add_sum_filter_not modes (· ∈ kept)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hki := (Finset.mem_filter.mp hi).2
    simp only [recover_sub, if_pos hki, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (gain i).2.le), mul_pow]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hki := (Finset.mem_filter.mp hi).2
    simp only [recover_sub, if_neg hki, norm_neg]

end

end GaloisForLFunctions.HilbertMetric.DiagonalCutoff
