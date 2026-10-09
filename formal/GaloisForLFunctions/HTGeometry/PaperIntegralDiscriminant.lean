import GaloisForLFunctions.HTGeometry.PaperIntegralSymmetricBaseChange
import GaloisForLFunctions.HTGeometry.PermutationAction
import GaloisForLFunctions.HTGeometry.SymmetricCoefficientNonSquare

/-!
# The generic discriminant over arbitrary commutative coefficient rings

The native permutation-action Vandermonde agrees with the determinant
convention used by the integral retraction. Its square descends to a
regular coefficient polynomial, naturally under every coefficient map.
Over a field this is exactly the existing native discriminant polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The native permutation-action and determinant Vandermonde conventions agree. -/
theorem paperUniversalVandermonde_eq_native : paperUniversalVandermonde K n = vandermonde K n := by
  classical
  have hp : Equiv.Perm.finPairsLT n =
      (Finset.univ : Finset (Fin n)).sigma (fun i => Finset.univ.filter (fun j => j < i)) := by
    ext a
    simp only [Equiv.Perm.mem_finPairsLT, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hi (i : Fin n) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    ext j
    simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [vandermonde, hp, Finset.prod_sigma]
  simp only [paperUniversalVandermonde, vandermondeProd, hi, Finset.prod_filter]
  exact Finset.prod_comm

/-- The native permutation-action Vandermonde is cancellable even over rings with zero divisors. -/
theorem paperNativeVandermonde_regular : IsRegular (vandermonde K n) := by
  rw [← paperUniversalVandermonde_eq_native]
  exact paperUniversalVandermonde_regular K n

private theorem universalVandermonde_square_symmetric :
    (paperUniversalVandermonde K n * paperUniversalVandermonde K n).IsSymmetric := by
  rw [paperUniversalVandermonde_eq_native, ← pow_two]
  exact isSymmetric_vandermonde_sq K n

/-- The integral generic discriminant in elementary-symmetric coefficient coordinates. -/
def paperIntegralDiscriminantPolynomial : MvPolynomial (Fin n) K :=
  paperIntegralSymmetricCoefficientRetraction K n
    (paperUniversalVandermonde K n * paperUniversalVandermonde K n)

/-- Root substitution recovers the actual universal Vandermonde square. -/
theorem paperIntegralDiscriminantPolynomial_spec :
    aeval (fun i : Fin n => esymm (Fin n) K (i + 1))
      (paperIntegralDiscriminantPolynomial K n) =
        paperUniversalVandermonde K n * paperUniversalVandermonde K n := by
  rw [paperIntegralDiscriminantPolynomial, paperIntegralSymmetricCoefficientRetraction_spec,
    paperIntegralSymmetricProjection_fixed K n _ (universalVandermonde_square_symmetric K n)]

/-- The generic discriminant is a regular coefficient polynomial over every commutative ring. -/
theorem paperIntegralDiscriminantPolynomial_regular :
    IsRegular (paperIntegralDiscriminantPolynomial K n) := by
  have hinj : Function.Injective
      (aeval (R := K) (fun i : Fin n => esymm (Fin n) K (i + 1))) := by
    intro p q h
    have hr := congrArg (paperIntegralSymmetricCoefficientRetraction K n) h
    simpa only [paperIntegralSymmetricCoefficientRetraction_map] using hr
  have hl : IsLeftRegular (paperIntegralDiscriminantPolynomial K n) := by
    intro p q h
    apply hinj
    apply ((paperUniversalVandermonde_regular K n).mul
      (paperUniversalVandermonde_regular K n)).left
    have he := congrArg (aeval (R := K) (fun i : Fin n => esymm (Fin n) K (i + 1))) h
    simpa only [map_mul, paperIntegralDiscriminantPolynomial_spec] using he
  exact ⟨hl, fun p q h => hl (by simpa only [mul_comm] using h)⟩

/-- No power of the integral discriminant vanishes except over the zero coefficient ring. -/
theorem paperIntegralDiscriminantPolynomial_pow_eq_zero_iff (m : ℕ) :
    paperIntegralDiscriminantPolynomial K n ^ m = 0 ↔ (1 : K) = 0 := by
  constructor
  · intro h
    have he : (1 : MvPolynomial (Fin n) K) = 0 :=
      ((paperIntegralDiscriminantPolynomial_regular K n).pow m).left
        (by simpa only [mul_one, mul_zero] using h)
    simpa only [map_one, map_zero] using congrArg
      (constantCoeff : MvPolynomial (Fin n) K →+* K) he
  · intro h
    letI : Subsingleton K := subsingleton_of_zero_eq_one h.symm
    exact Subsingleton.elim _ _

/-- The integral generic discriminant commutes with arbitrary coefficient homomorphisms. -/
theorem paperIntegralDiscriminantPolynomial_baseChange
    {L : Type*} [CommRing L] (f : K →+* L) :
    MvPolynomial.map f (paperIntegralDiscriminantPolynomial K n) =
      paperIntegralDiscriminantPolynomial L n := by
  simp only [paperIntegralDiscriminantPolynomial,
    paperIntegralSymmetricCoefficientRetraction_baseChange,
    map_mul, paperUniversalVandermonde_baseChange]

/-- Over a field the integral construction is exactly the corpus's original discriminant. -/
theorem paperIntegralDiscriminantPolynomial_eq_native
    (F : Type*) [Field F] (d : ℕ) :
    paperIntegralDiscriminantPolynomial F d = discCoeffPoly F d := by
  apply (esymmAlgEquiv F d).injective
  apply Subtype.ext
  rw [esymmAlgEquiv_apply_coe, paperIntegralDiscriminantPolynomial_spec,
    esymmAlgEquiv_discCoeffPoly]
  rfl

end

end GaloisForLFunctions.HTGeometry
