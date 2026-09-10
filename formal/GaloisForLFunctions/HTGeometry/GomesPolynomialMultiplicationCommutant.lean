import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionShiftConjugacy
import Mathlib.Algebra.Algebra.Bilinear

/-!
# What preserving polynomial multiplication remembers

The reconstruction experiment now retains the polynomial module structure.
A real-linear map commuting with multiplication by X must itself be multiplication
by its value on1. Thus one coordinate action already enforces all polynomial actions.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Actual multiplication by a real polynomial, as a real-linear operator. -/
def gomesPolynomialMultiplicationMap (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  LinearMap.mul ℝ ℝ[X] P

/-- The coordinate-compatible real-linear maps on the polynomial domain. -/
abbrev GomesPolynomialXCompatibleMap :=
  {E : ℝ[X] →ₗ[ℝ] ℝ[X] //
    E.comp (gomesPolynomialMultiplicationMap X) =
      (gomesPolynomialMultiplicationMap X).comp E}

/-- Compatibility with the coordinate action, evaluated on any polynomial. -/
theorem gomesPolynomialXCompatibleMap_apply_X (E : GomesPolynomialXCompatibleMap) (P : ℝ[X]) :
    E.val (X * P) = X * E.val P :=
  congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f P) E.property

/-- One value determines the action of a coordinate-compatible map on every polynomial. -/
theorem gomesPolynomialXCompatibleMap_apply (E : GomesPolynomialXCompatibleMap) (P : ℝ[X]) :
    E.val P = E.val 1 * P := by
  induction P using Polynomial.induction_on with
  | C a =>
    have hc : C a = a • (1 : ℝ[X]) := by simp only [smul_eq_C_mul, mul_one]
    rw [hc, map_smul]
    simp only [smul_eq_C_mul, mul_one]
    ring
  | add P Q hp hq => rw [map_add, hp, hq, mul_add]
  | monomial n a ih =>
    have hp : C a * (X : ℝ[X]) ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [hp, gomesPolynomialXCompatibleMap_apply_X, ih]
    ring

/-- The full commutant of coordinate multiplication consists exactly of polynomial multipliers. -/
theorem gomesPolynomialMultiplication_X_commutant_iff (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    E.comp (gomesPolynomialMultiplicationMap X) =
        (gomesPolynomialMultiplicationMap X).comp E ↔
      E = gomesPolynomialMultiplicationMap (E 1) := by
  constructor
  · intro h
    apply LinearMap.ext
    intro P
    exact gomesPolynomialXCompatibleMap_apply ⟨E, h⟩ P
  · intro h
    rw [h]
    apply LinearMap.ext
    intro P
    simp only [LinearMap.comp_apply, gomesPolynomialMultiplicationMap, LinearMap.mul_apply']
    ring

/-- Constant polynomial multipliers are scalar linear maps. -/
theorem gomesPolynomialMultiplicationMap_constant (c : ℝ) :
    gomesPolynomialMultiplicationMap (C c) = c • (LinearMap.id : ℝ[X] →ₗ[ℝ] ℝ[X]) := by
  apply LinearMap.ext
  intro P
  simp only [gomesPolynomialMultiplicationMap, LinearMap.mul_apply', LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_C_mul]

/-- The multiplier presentation is faithful, as evaluation on1 recovers its polynomial. -/
theorem gomesPolynomialMultiplicationMap_injective :
    Function.Injective gomesPolynomialMultiplicationMap := by
  intro P Q h
  have he := congrArg (fun f : ℝ[X] →ₗ[ℝ] ℝ[X] => f 1) h
  simpa only [gomesPolynomialMultiplicationMap, LinearMap.mul_apply', mul_one] using he

/-- Every pair of polynomial multipliers commutes on the full polynomial domain. -/
theorem gomesPolynomialMultiplicationMap_commute (P Q : ℝ[X]) :
    (gomesPolynomialMultiplicationMap P).comp (gomesPolynomialMultiplicationMap Q) =
      (gomesPolynomialMultiplicationMap Q).comp (gomesPolynomialMultiplicationMap P) := by
  apply LinearMap.ext
  intro R
  simp only [LinearMap.comp_apply, gomesPolynomialMultiplicationMap, LinearMap.mul_apply']
  ring

/-- Preserving the single coordinate action is equivalent to preserving every polynomial action. -/
theorem gomesPolynomialMultiplication_all_compatible_iff (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    (∀ P : ℝ[X], E.comp (gomesPolynomialMultiplicationMap P) =
      (gomesPolynomialMultiplicationMap P).comp E) ↔
      E.comp (gomesPolynomialMultiplicationMap X) =
        (gomesPolynomialMultiplicationMap X).comp E := by
  constructor
  · intro h; exact h X
  · intro h P
    rw [(gomesPolynomialMultiplication_X_commutant_iff E).mp h]
    exact gomesPolynomialMultiplicationMap_commute _ _

end GaloisForLFunctions.HTGeometry
