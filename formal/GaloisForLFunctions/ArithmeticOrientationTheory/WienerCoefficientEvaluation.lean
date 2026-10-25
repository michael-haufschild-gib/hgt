import GaloisForLFunctions.ArithmeticOrientationTheory.TheCriticalWienerAlgebraIsABanachAlgebra
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Continuous Wiener coefficient evaluation

Every arithmetic coefficient is a continuous linear functional. Positive
point masses are linearly independent, so every Wiener algebra is infinite-dimensional.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory.WienerAlgebraAt

/-- Every fixed Wiener coefficient is controlled by its weighted norm. -/
theorem norm_coefficient_le {σ : ℝ} (a : WienerAlgebraAt σ) (n : ℕ) :
    ‖a.toFn n‖ ≤ (n : ℝ) ^ σ * ‖a‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero, norm_zero]
    positivity
  · have h := a.summable_norm.le_tsum n (fun _ _ => norm_nonneg _)
    change ‖LSeries.term (⇑a.toFn) σ n‖ ≤ ‖a‖ at h
    rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.ofReal_re] at h
    have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    exact ((div_le_iff₀ hp).mp h).trans_eq (mul_comm _ _)

/-- Continuous evaluation at one arithmetic coefficient. -/
def coefficientLinear (σ : ℝ) (n : ℕ) : WienerAlgebraAt σ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => a.toFn n
      map_add' := fun a b => by simp only [toFn_add, ArithmeticFunction.add_apply]
      map_smul' := fun z a => by
        rw [toFn_smul]
        rfl }
    ((n : ℝ) ^ σ) (fun a => norm_coefficient_le a n)

theorem coefficientLinear_apply {σ : ℝ} (a : WienerAlgebraAt σ) (n : ℕ) :
    coefficientLinear σ n a = a.toFn n := rfl


/-- Positive point masses are linearly independent at every Wiener weight. -/
theorem pointMass_succ_linearIndependent (σ : ℝ) :
    LinearIndependent ℂ (fun n : ℕ => (pointMass (σ := σ) (n + 1))) := by
  rw [linearIndependent_iff']
  intro S c h j hj
  have hc := congrArg (coefficientLinear σ (j + 1)) h
  simpa [map_sum, map_smul, coefficientLinear_apply, toFn_zero, ArithmeticFunction.zero_apply, toFn_pointMass,
    pointMassFn_apply, Nat.add_left_inj, hj] using hc

/-- The Wiener algebra has infinitely many independent coefficient directions. -/
theorem not_finiteDimensional (σ : ℝ) : ¬ FiniteDimensional ℂ (WienerAlgebraAt σ) := by
  intro h
  letI := h
  have hc := (pointMass_succ_linearIndependent σ).lt_aleph0_of_finiteDimensional
  simp only [Cardinal.mk_nat, lt_self_iff_false] at hc

end GaloisForLFunctions.ArithmeticOrientationTheory.WienerAlgebraAt

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.WienerAlgebraAt.pointMass_succ_linearIndependent
