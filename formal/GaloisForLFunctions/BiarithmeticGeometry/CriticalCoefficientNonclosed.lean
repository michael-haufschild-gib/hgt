import GaloisForLFunctions.BiarithmeticGeometry.CriticalCoefficientDomain
import GaloisForLFunctions.BiarithmeticGeometry.CriticalUnpaidSequence

/-!
# The actual complex critical coefficient domain is not closed

The inverse-square-root-tail differences define a norm-two vector in
complex `ell1`. Its total evaluation is zero but its partial-sum square
energy diverges. Corrected finite members converge to this explicit
vector, witnessing the precise gap between payment and its closure.
-/

noncomputable section
open Finset Filter Topology
open HTGeometry.ConstraintMotiveRelativity
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The explicit unpaid boundary sequence in the actual complex coefficient space. -/
def criticalUnpaidCoefficientVector : CriticalCoefficientSpace :=
  ⟨fun r => (criticalUnpaidCoeff r : ℂ), memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Complex.norm_real, Real.norm_eq_abs] using
      summable_abs_criticalUnpaidCoeff)⟩

/-- The explicit unpaid vector has exact coefficient norm two. -/
theorem norm_criticalUnpaidCoefficientVector : ‖criticalUnpaidCoefficientVector‖ = 2 := by
  rw [norm_eq_tsum_one]
  change (∑' r, ‖(criticalUnpaidCoeff r : ℂ)‖) = 2
  simpa only [Complex.norm_real, Real.norm_eq_abs] using tsum_abs_criticalUnpaidCoeff

theorem criticalUnpaidCoefficientVector_evaluation :
    criticalTotalEvaluation criticalUnpaidCoefficientVector = 0 := by
  rw [criticalTotalEvaluation_apply]
  change (∑' r, (criticalUnpaidCoeff r : ℂ)) = 0
  rw [← Complex.ofReal_tsum, tsum_criticalUnpaidCoeff, Complex.ofReal_zero]

/-- Zero evaluation does not supply finite critical response energy. -/
theorem criticalUnpaidCoefficientVector_not_mem :
    criticalUnpaidCoefficientVector ∉ criticalCoefficientDomain := by
  intro h
  apply not_summable_sq_criticalUnpaidCoeff_partialSum
  change Summable (fun M : ℕ => ‖∑ r ∈ range (M + 1), (criticalUnpaidCoeff r : ℂ)‖ ^ 2) at h
  simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- The explicit unpaid vector lies in the closure of the actual critical coefficient domain. -/
theorem criticalUnpaidCoefficientVector_mem_closure :
    criticalUnpaidCoefficientVector ∈ closure (criticalCoefficientDomain : Set CriticalCoefficientSpace) := by
  rw [closure_criticalCoefficientDomain]
  exact criticalUnpaidCoefficientVector_evaluation

/-- The complete finite core converges in coefficient norm to this unpaid boundary vector. -/
theorem criticalUnpaidCoefficientVector_finiteCore_tendsto :
    Tendsto (criticalFiniteCoefficientCore criticalUnpaidCoefficientVector) atTop
      (𝓝 criticalUnpaidCoefficientVector) :=
  criticalFiniteCoefficientCore_tendsto _ criticalUnpaidCoefficientVector_evaluation

/-- The actual complex partial-sum domain is not closed in coefficient norm. -/
theorem not_isClosed_criticalCoefficientDomain :
    ¬IsClosed (criticalCoefficientDomain : Set CriticalCoefficientSpace) := by
  intro h
  apply criticalUnpaidCoefficientVector_not_mem
  change criticalUnpaidCoefficientVector ∈ (criticalCoefficientDomain : Set CriticalCoefficientSpace)
  simpa only [h.closure_eq] using criticalUnpaidCoefficientVector_mem_closure

end GaloisForLFunctions.BiarithmeticGeometry

