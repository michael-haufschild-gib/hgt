import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.DifferentialConstantLinearFamilyMatroid
import GaloisForLFunctions.HTGeometry.ToricLogTail

/-!
# Exact differential matroid of Laurent-monomial families

Coordinatewise logarithmic differentiation converts a finite Laurent-monomial family into the
integer exponent matrix acting on the logarithmic derivatives of its palette.  Since logarithmic
differentiation preserves the complete differential matroid and a differentially independent
palette has independent logarithmic derivatives, no nonlinear differential relation is lost or
created: the resulting matroid is exactly the ordinary row matroid of the exponent matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix Set
open scoped Differential

noncomputable section

universe u

/-- Laurent monomials with one integral exponent row per output coordinate. -/
def integerLaurentMonomialFamily
    {K m n : Type u} [Field K] [Fintype n]
    (A : Matrix m n ℤ) (x : n → K) : m → K :=
  fun i ↦ ∏ j, x j ^ A i j

/-- The same integral matrix viewed over a characteristic-zero coefficient field. -/
def integerCastMatrix
    (C : Type u) [Field C] [CharZero C]
    {m n : Type u} (A : Matrix m n ℤ) : Matrix m n C :=
  fun i j ↦ (A i j : C)

/-- **Exact Laurent-monomial differential matroid.**  Every differential dependence among a
finite family of Laurent monomials in a differentially independent palette is already an ordinary
linear dependence among its integral exponent rows. -/
theorem differentialFamilyMatroid_integerLaurentMonomialFamily_eq_linearFamilyMatroid
    {C K m n : Type u} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K]
    [CharZero C] [CharZero K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℤ) (x : n → K) (hx : DifferentialIndependent C x) :
    differentialFamilyMatroid (F := C) (integerLaurentMonomialFamily A x) =
      linearFamilyMatroid (integerCastMatrix C A) := by
  rw [differentialFamilyMatroid_deriv_div_self_eq]
  have hx0 : ∀ j, x j ≠ 0 := by
    intro j hzero
    exact (hx.algebraicIndependent.transcendental j)
      (hzero ▸ isAlgebraic_zero)
  have hlog :
      (fun i ↦ ((integerLaurentMonomialFamily A x i)′ /
        integerLaurentMonomialFamily A x i)) =
        matrixLinearForms (A := K) (integerCastMatrix C A) (fun j ↦ (x j)′ / x j) := by
    funext i
    have hi := congrFun (toricLogCurrent_characterMatrix A x hx0) i
    simpa [toricLogCurrent, integerLaurentMonomialFamily, integerCastMatrix,
      matrixLinearForms] using hi
  rw [hlog]
  apply differentialFamilyMatroid_matrixLinearForms_eq_linearFamilyMatroid
  · intro i j
    simp [integerCastMatrix]
  · exact (differentialIndependent_deriv_div_self_iff x).mp hx

/-- Independence interface for every selected Laurent-monomial subfamily. -/
theorem differentialFamilyMatroid_integerLaurentMonomialFamily_indep_iff
    {C K m n : Type u} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K]
    [CharZero C] [CharZero K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℤ) (x : n → K) (hx : DifferentialIndependent C x)
    (I : Set m) :
    (differentialFamilyMatroid (F := C) (integerLaurentMonomialFamily A x)).Indep I ↔
      LinearIndependent C (fun i : I ↦ integerCastMatrix C A i) := by
  rw [differentialFamilyMatroid_integerLaurentMonomialFamily_eq_linearFamilyMatroid A x hx]
  exact linearFamilyMatroid_indep_iff _ I

/-- Numerical rank formula for every finite Laurent-monomial packet. -/
theorem differentialFamilyMatroid_integerLaurentMonomialFamily_eRk_finset
    {C K m n : Type u} [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K]
    [CharZero C] [CharZero K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℤ) (x : n → K) (hx : DifferentialIndependent C x)
    (I : Finset m) :
    (differentialFamilyMatroid (F := C) (integerLaurentMonomialFamily A x)).eRk
        (↑I : Set m) =
      (Module.finrank C
        (Submodule.span C (integerCastMatrix C A '' (↑I : Set m))) : ℕ∞) := by
  rw [differentialFamilyMatroid_integerLaurentMonomialFamily_eq_linearFamilyMatroid A x hx]
  exact linearFamilyMatroid_eRk_finset (integerCastMatrix C A) I

end

end GaloisForLFunctions.HTGeometry
