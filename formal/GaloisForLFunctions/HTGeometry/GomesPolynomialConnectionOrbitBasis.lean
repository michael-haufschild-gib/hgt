import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionIterates
import Mathlib.Algebra.Polynomial.Sequence

/-!
# A complete basis of polynomial connection orbits

For coefficient degree m, index n selects the (n / m)-th iterate of X^(n % m).
The resulting polynomial has degree exactly n. The polynomial-sequence basis
construction proves that these m orbit chains exhaust the whole polynomial space.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Interleave the connection orbits of the monomials below the coefficient degree. -/
def gomesPolynomialConnectionOrbitPolynomial
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) : ℝ[X] :=
  (gomesPolynomialFirstOrderOperator A.val)^[n / A.val.natDegree]
    (X ^ (n % A.val.natDegree))

/-- Every interleaved orbit polynomial is nonzero. -/
theorem gomesPolynomialConnectionOrbitPolynomial_ne_zero
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionOrbitPolynomial A n ≠ 0 :=
  gomesPolynomialFirstOrder_nonconstant_iterate_ne_zero A
    ⟨_, pow_ne_zero _ X_ne_zero⟩ _

/-- The orbit enumeration hits each natural degree exactly once. -/
theorem gomesPolynomialConnectionOrbitPolynomial_natDegree
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    (gomesPolynomialConnectionOrbitPolynomial A n).natDegree = n := by
  unfold gomesPolynomialConnectionOrbitPolynomial
  rw [gomesPolynomialFirstOrder_nonconstant_iterate_degree A
    ⟨_, pow_ne_zero _ X_ne_zero⟩, natDegree_X_pow]
  exact Nat.div_add_mod' n A.val.natDegree

/-- The same degree identity in the polynomial degree type, including nonvanishing. -/
theorem gomesPolynomialConnectionOrbitPolynomial_degree
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    (gomesPolynomialConnectionOrbitPolynomial A n).degree = n := by
  rw [degree_eq_natDegree (gomesPolynomialConnectionOrbitPolynomial_ne_zero A n),
    gomesPolynomialConnectionOrbitPolynomial_natDegree]

/-- The degree-indexed sequence attached to a nonconstant connection. -/
def gomesPolynomialConnectionOrbitSequence
    (A : GomesNonconstantPolynomialCoefficient) : Polynomial.Sequence ℝ where
  elems' := gomesPolynomialConnectionOrbitPolynomial A
  degree_eq' := gomesPolynomialConnectionOrbitPolynomial_degree A

/-- All orbit polynomials form a basis of the full polynomial space. -/
def gomesPolynomialConnectionOrbitBasis
    (A : GomesNonconstantPolynomialCoefficient) : Module.Basis ℕ ℝ ℝ[X] :=
  (gomesPolynomialConnectionOrbitSequence A).basis fun n =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr
      (gomesPolynomialConnectionOrbitPolynomial_ne_zero A n))

/-- Basis vectors are precisely the iterated monomial seeds. -/
theorem gomesPolynomialConnectionOrbitBasis_apply
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialConnectionOrbitBasis A n = gomesPolynomialConnectionOrbitPolynomial A n :=
  (gomesPolynomialConnectionOrbitSequence A).basis_eq_self _ n

/-- The connection shifts every orbit polynomial by exactly its coefficient degree. -/
theorem gomesPolynomialConnectionOrbitPolynomial_shift
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialFirstOrderOperator A.val (gomesPolynomialConnectionOrbitPolynomial A n) =
      gomesPolynomialConnectionOrbitPolynomial A (n + A.val.natDegree) := by
  unfold gomesPolynomialConnectionOrbitPolynomial
  rw [Nat.add_div_right n (gomesNonconstantPolynomialCoefficient_degree_pos A),
    Nat.add_mod_right, Function.iterate_succ_apply']

/-- On its orbit basis, the connection is the shift with coefficient-degree step. -/
theorem gomesPolynomialConnectionOrbitBasis_shift
    (A : GomesNonconstantPolynomialCoefficient) (n : ℕ) :
    gomesPolynomialFirstOrderLinearMap A.val (gomesPolynomialConnectionOrbitBasis A n) =
      gomesPolynomialConnectionOrbitBasis A (n + A.val.natDegree) := by
  simp only [gomesPolynomialConnectionOrbitBasis_apply]
  exact gomesPolynomialConnectionOrbitPolynomial_shift A n

end GaloisForLFunctions.HTGeometry
