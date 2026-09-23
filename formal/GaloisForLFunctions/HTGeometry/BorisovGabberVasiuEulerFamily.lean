import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuPolynomialJacobian
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.LinearCombination


/-!
# Explicit Euler families with determinant one

The characteristic-two case of Borisov--Gabber--Vasiu, Example 21.4, classifies
all polynomial solutions of `f + X f' = a`. Substitution into the paper's weighted
Jacobian formula gives explicit determinant-one endomorphisms in every positive
dimension, with arbitrary polynomial parameters and characteristic-power twists.
-/

open Polynomial
noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]

/-- Exact characteristic-two solution set of the scalar Euler equation in BGV Example 21.4. -/
theorem bgv_eulerEquation_charTwo (f : Polynomial R) (a : R) :
    f + X * f.derivative = C a ↔
      ∃ g : Polynomial R, f = C a + X * Polynomial.expand R 2 g := by
  have htwo : (2 : Polynomial R) = 0 := CharP.cast_eq_zero (Polynomial R) 2
  constructor
  · intro h
    have hd := congrArg Polynomial.derivative h
    simp only [map_add, Polynomial.derivative_mul, Polynomial.derivative_X,
      one_mul, Polynomial.derivative_C] at hd
    have hz : X * f.derivative.derivative = 0 := by
      linear_combination hd - f.derivative * htwo
    have hdd : f.derivative.derivative = 0 :=
      (mul_eq_zero.mp hz).resolve_left Polynomial.X_ne_zero
    refine ⟨Polynomial.contract 2 f.derivative, ?_⟩
    rw [Polynomial.expand_contract 2 hdd (by omega)]
    linear_combination h - X * f.derivative * htwo
  · rintro ⟨g, rfl⟩
    have he : (Polynomial.expand R 2 g).derivative = 0 := by
      rw [Polynomial.derivative_expand]
      simp only [Nat.cast_ofNat, htwo, zero_mul, mul_zero]
    rw [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X, he]
    linear_combination X * Polynomial.expand R 2 g * htwo

/-- Every polynomial parameter gives a proved scalar Jacobian response, without an ODE premise. -/
theorem bgv_eulerResponse_charTwo (a : R) (g : Polynomial R) :
    (C a + X * Polynomial.expand R 2 g) +
      X * (C a + X * Polynomial.expand R 2 g).derivative = C a :=
  (bgv_eulerEquation_charTwo _ a).mpr ⟨g, rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A distinguished coordinate carrying the full Euler family; every other factor is one. -/
def bgvEulerFactors (a : R) (g : Polynomial R) : Option ι → Polynomial R :=
  fun i => i.elim (C a + X * Polynomial.expand R 2 g) (fun _ => 1)

/-- The scalar response of this entire multivariable family is the prescribed constant. -/
theorem bgv_eulerFactors_response (a : R) (g : Polynomial R) :
    bgvJacobianResponse (fun _ : Option ι => 1) (bgvEulerFactors a g) = C a := by
  have hp : (∏ j ∈ Finset.univ.erase (none : Option ι), bgvEulerFactors a g j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    cases j with
    | none => simp at hj
    | some j => rfl
  simp only [bgvJacobianResponse, Fintype.prod_option, Fintype.sum_option]
  rw [hp]
  simpa [bgvEulerFactors] using bgv_eulerResponse_charTwo a g

/-- A closed determinant-one family in every positive dimension, including arbitrary
characteristic-power twists of the shared source. -/
theorem bgv_eulerFamily_jacobian_one (g : Polynomial R) (L : MvPolynomial (Option ι) R) :
    let w := L ^ (2 : ℕ) * ∏ j : Option ι, MvPolynomial.X j
    (jacobian R (Option ι) (bgvSharedSourceMap (bgvEulerFactors 1 g) w)).det = 1 := by
  have h := bgv_det_jacobian_twistedSource_response 2 L
    (fun _ : Option ι => 1) (bgvEulerFactors 1 g)
  simpa only [pow_one, bgv_eulerFactors_response, Polynomial.aeval_C, map_one] using h

/-- The same explicit family preserves the determinant of the corpus's differential pullback. -/
theorem bgv_eulerFamily_pullback_det_one (g : Polynomial R)
    (L : MvPolynomial (Option ι) R) :
    let w := L ^ (2 : ℕ) * ∏ j : Option ι, MvPolynomial.X j
    LinearMap.det (pullbackDifferential R (Option ι)
      (bgvSharedSourceMap (bgvEulerFactors 1 g) w)) = 1 := by
  dsimp only
  rw [det_pullbackDifferential]
  exact bgv_eulerFamily_jacobian_one g L

end GaloisForLFunctions.HTGeometry
