import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm
import GaloisForLFunctions.RHTower.FiniteFluxPassport

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The exponential simple-zero realizer has exact analytic order one at its centre. -/
theorem analyticOrderAt_simpleZeroExponentialRealizer_zero (P : Polynomial ℂ) :
    analyticOrderAt (simpleZeroExponentialRealizer P) 0 = (1 : ℕ∞) :=
  (simpleZeroExponentialRealizer_analyticAt P 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (simpleZeroExponentialRealizer_zero P) (deriv_simpleZeroExponentialRealizer_zero_ne P)

/-- The canonical residue-filled flux of the exponential simple-zero realizer is exactly its
polynomial completed-flux passport, including the removable centre. -/
theorem fluxGerm_simpleZeroExponentialRealizer_eq_polynomialCompletedFluxPassport
    (P : Polynomial ℂ) :
    fluxGerm (simpleZeroExponentialRealizer P) 0 =
      fun x => (polynomialCompletedFluxPassport P).eval x := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [fluxGerm_zero, analyticOrderAt_simpleZeroExponentialRealizer_zero]
    simp [polynomialCompletedFluxPassport]
  · rw [fluxGerm_of_ne_zero _ _ hx]
    simpa using (polynomialCompletedFluxPassport_eval_eq_neg_mul_logDeriv P hx).symm

/-- Translate the exponential simple-zero realizer to a prescribed centre. -/
def shiftedSimpleZeroExponentialRealizer (P : Polynomial ℂ) (ρ : ℂ) (z : ℂ) : ℂ :=
  simpleZeroExponentialRealizer P (z - ρ)

theorem shiftedSimpleZeroExponentialRealizer_differentiable (P : Polynomial ℂ) (ρ : ℂ) :
    Differentiable ℂ (shiftedSimpleZeroExponentialRealizer P ρ) := by
  unfold shiftedSimpleZeroExponentialRealizer
  have hdiff : Differentiable ℂ (simpleZeroExponentialRealizer P) :=
    fun z => (simpleZeroExponentialRealizer_analyticAt P z).differentiableAt
  exact hdiff.comp (differentiable_id.sub_const ρ)

@[simp] theorem shiftedSimpleZeroExponentialRealizer_zero (P : Polynomial ℂ) (ρ : ℂ) :
    shiftedSimpleZeroExponentialRealizer P ρ ρ = 0 := by
  simp [shiftedSimpleZeroExponentialRealizer]

theorem deriv_shiftedSimpleZeroExponentialRealizer_ne_zero (P : Polynomial ℂ) (ρ : ℂ) :
    deriv (shiftedSimpleZeroExponentialRealizer P ρ) ρ ≠ 0 := by
  change deriv (fun z => simpleZeroExponentialRealizer P (z - ρ)) ρ ≠ 0
  rw [deriv_comp_sub_const]
  simpa using deriv_simpleZeroExponentialRealizer_zero_ne P

/-- Translation preserves the polynomial completed-flux passport exactly. -/
theorem fluxGerm_shiftedSimpleZeroExponentialRealizer_eq_polynomialCompletedFluxPassport
    (P : Polynomial ℂ) (ρ : ℂ) :
    fluxGerm (shiftedSimpleZeroExponentialRealizer P ρ) ρ =
      fun x => (polynomialCompletedFluxPassport P).eval x := by
  funext x
  have hcomp := fluxGerm_comp_affine (f := simpleZeroExponentialRealizer P)
    (μ := (1 : ℂ)) (ν := -ρ) (z := ρ) (n := 1) one_ne_zero
    (fun w => simpleZeroExponentialRealizer_analyticAt P w) (by
      simpa using analyticOrderAt_simpleZeroExponentialRealizer_zero P) x
  calc
    fluxGerm (shiftedSimpleZeroExponentialRealizer P ρ) ρ x =
        fluxGerm (simpleZeroExponentialRealizer P) 0 x := by
      change fluxGerm (fun z => simpleZeroExponentialRealizer P (z - ρ)) ρ x = _
      simpa [sub_eq_add_neg] using hcomp
    _ = (polynomialCompletedFluxPassport P).eval x :=
      congrFun (fluxGerm_simpleZeroExponentialRealizer_eq_polynomialCompletedFluxPassport P) x

end RHTower
