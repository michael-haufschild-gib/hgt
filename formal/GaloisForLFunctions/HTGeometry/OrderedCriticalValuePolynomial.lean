import GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial coordinates for the actual critical-value map

The constant-first coordinate homeomorphism identifies the parameter space with affine
complex space. Universal critical positions and their critical product give explicit
multivariate polynomials whose evaluations are exactly the actual critical values.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

abbrev Coordinate (n : ℕ) := Fin (n + 1) → ℂ

def parameterOfCoordinates {n : ℕ} (θ : Coordinate n) : Parameter n :=
  (fun i => θ i.succ, θ 0)

def parameterCoordinates {n : ℕ} (v : Parameter n) : Coordinate n := Fin.cons v.2 v.1

@[simp] theorem parameterOfCoordinates_parameterCoordinates {n : ℕ} (v : Parameter n) :
    parameterOfCoordinates (parameterCoordinates v) = v := by
  simp [parameterOfCoordinates, parameterCoordinates]

@[simp] theorem parameterCoordinates_parameterOfCoordinates {n : ℕ} (θ : Coordinate n) :
    parameterCoordinates (parameterOfCoordinates θ) = θ := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [parameterOfCoordinates, parameterCoordinates]

def coordinateHomeomorph (n : ℕ) : Parameter n ≃ₜ Coordinate n where
  toFun := parameterCoordinates
  invFun := parameterOfCoordinates
  left_inv := parameterOfCoordinates_parameterCoordinates
  right_inv := parameterCoordinates_parameterOfCoordinates
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [parameterCoordinates] using (continuous_snd : Continuous fun v : Parameter n => v.2)
    · simp only [parameterCoordinates, Fin.cons_succ]
      fun_prop
  continuous_invFun := by unfold parameterOfCoordinates; fun_prop

abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ

def positionPolynomial (n : ℕ) : Fin (n + 1) → CoordinatePolynomial n :=
  Fin.cons (-∑ i : Fin n, MvPolynomial.X i.succ) (fun i => MvPolynomial.X i.succ)

def criticalProductPolynomial (n : ℕ) : Polynomial (CoordinatePolynomial n) :=
  ∏ j, (Polynomial.X - Polynomial.C (positionPolynomial n j))

def valuePolynomial (n : ℕ) (j : Fin (n + 1)) : CoordinatePolynomial n :=
  MvPolynomial.C (n + 2 : ℂ) *
      (∑ k ∈ Finset.range (n + 2),
        (criticalProductPolynomial n).coeff k * MvPolynomial.C (1 / ((k : ℂ) + 1)) *
          positionPolynomial n j ^ (k + 1)) + MvPolynomial.X 0

@[simp] theorem eval_positionPolynomial {n : ℕ} (θ : Coordinate n) (j : Fin (n + 1)) :
    MvPolynomial.eval θ (positionPolynomial n j) = position (parameterOfCoordinates θ) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [positionPolynomial, position, parameterOfCoordinates]
  · simp [positionPolynomial, position, parameterOfCoordinates]

theorem map_criticalProductPolynomial {n : ℕ} (θ : Coordinate n) :
    (criticalProductPolynomial n).map (MvPolynomial.eval θ) =
      criticalProduct (parameterOfCoordinates θ) := by
  simp [criticalProductPolynomial, criticalProduct, Polynomial.map_prod]

/-- Every actual critical-value coordinate is evaluation of an explicitly constructed
multivariate polynomial in the parameter coordinates. -/
theorem eval_valuePolynomial {n : ℕ} (θ : Coordinate n) (j : Fin (n + 1)) :
    MvPolynomial.eval θ (valuePolynomial n j) =
      valuesWithConstant (parameterOfCoordinates θ) j := by
  simp only [valuePolynomial, map_add, map_mul, map_sum, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, eval_positionPolynomial]
  unfold valuesWithConstant polyAntideriv
  rw [natDegree_criticalProduct]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_X, parameterOfCoordinates]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff k) (map_criticalProductPolynomial θ)
  simp only [Polynomial.coeff_map] at hc
  rw [hc]
  simp [div_eq_mul_inv, parameterOfCoordinates]

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
