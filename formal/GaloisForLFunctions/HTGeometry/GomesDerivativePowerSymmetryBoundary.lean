import GaloisForLFunctions.HTGeometry.GomesDerivativePowerChainTransfers
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# The exact symmetry boundary across all derivative orders

The zeroth power has every endomorphism as a symmetry, so its centralizer is also
noncommutative. Together with the residue-chain classification, the first derivative
is the unique order with a commutative full symmetry algebra.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
/-- The identity operator's full symmetry algebra is noncommutative on the polynomial space. -/
theorem gomesPolynomialDerivativePowerCommutant_zero_noncommutative :
    ¬ (∀ E F : GomesPolynomialDerivativePowerCommutant K 0, E * F = F * E) := by
  have hmem (T : Module.End K K[X]) : T ∈ gomesPolynomialDerivativePowerCommutantAlgebra K 0 := by
    rw [gomesPolynomialDerivativePowerCommutant_zero]
    trivial
  let E : GomesPolynomialDerivativePowerCommutant K 0 := ⟨Polynomial.derivative, hmem _⟩
  let F : GomesPolynomialDerivativePowerCommutant K 0 := ⟨LinearMap.mulLeft K (X : K[X]), hmem _⟩
  intro h
  have hEF : (Polynomial.derivative : Module.End K K[X]) * LinearMap.mulLeft K (X : K[X]) =
      LinearMap.mulLeft K (X : K[X]) * Polynomial.derivative :=
    congrArg Subtype.val (h E F)
  have hc := congrArg (fun T : Module.End K K[X] => T (1 : K[X])) hEF
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, mul_one,
    Polynomial.derivative_X, Polynomial.derivative_one, mul_zero] at hc
  exact (one_ne_zero : (1 : K[X]) ≠ 0) hc

/-- Over all natural orders, the full symmetry algebra is commutative precisely at the first derivative. -/
theorem gomesPolynomialDerivativePowerCommutant_all_orders_commutative_iff (m : ℕ) :
    (∀ E F : GomesPolynomialDerivativePowerCommutant K m, E * F = F * E) ↔ m = 1 := by
  cases m with
  | zero =>
      constructor
      · intro h
        exact False.elim (gomesPolynomialDerivativePowerCommutant_zero_noncommutative K h)
      · intro h
        exact False.elim (Nat.zero_ne_one h)
  | succ n => exact gomesPolynomialDerivativePowerCommutant_commutative_iff K (n + 1)

/-- Every derivative order at least two has a nonzero square-zero symmetry. -/
theorem gomesPolynomialDerivativeHigherPower_nilpotent_symmetry (n : ℕ) :
    ∃ E : GomesPolynomialDerivativePowerCommutant K (n + 2), E ≠ 0 ∧ E * E = 0 := by
  let i : Fin (n + 2) := ⟨0, Nat.zero_lt_succ (n + 1)⟩
  let j : Fin (n + 2) := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  exact ⟨gomesDerivativePowerChainTransfer K (n + 2) i j,
    gomesDerivativePowerChainTransfer_ne_zero K (n + 2) i j,
    (gomesDerivativePowerChainTransfer_square_zero_iff K (n + 2) i j).mpr hij⟩

/-- The first derivative has no nonzero square-zero symmetry. -/
theorem gomesPolynomialDerivativeFirstPower_square_zero_iff
    (E : GomesPolynomialDerivativePowerCommutant K 1) : E * E = 0 ↔ E = 0 := by
  constructor
  · intro h
    have hm := congrArg (gomesPolynomialDerivativePowerCommutantEquiv K 1) h
    rw [map_mul, map_zero] at hm
    have hc := congrArg (fun M : Matrix (Fin 1) (Fin 1) (PowerSeries K) => M 0 0) hm
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.zero_apply] at hc
    have he : gomesPolynomialDerivativePowerCommutantEquiv K 1 E 0 0 = 0 := mul_self_eq_zero.mp hc
    apply (gomesPolynomialDerivativePowerCommutantEquiv K 1).injective
    rw [map_zero]
    apply Matrix.ext
    intro i j
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    subst j
    exact he
  · rintro rfl
    exact mul_zero _

end GaloisForLFunctions.HTGeometry
