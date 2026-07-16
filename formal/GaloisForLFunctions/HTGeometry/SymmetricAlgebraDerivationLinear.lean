import GaloisForLFunctions.HTGeometry.SymmetricAlgebraDerivation

/-!
# Linearity of the symmetric-algebra derivation construction

The derivation induced by a linear state action depends linearly on that action.  This turns a
linear pencil of internal principal symbols into a genuine linear law space of derivations, which
is required before its Lie commutator can be compared with horizon secant geometry.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [AddCommGroup M] [Module K M]

theorem symmetricPolynomialDerivation_add (T U : Module.End K M) :
    symmetricPolynomialDerivation (T + U) =
      symmetricPolynomialDerivation T + symmetricPolynomialDerivation U := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [symmetricPolynomialDerivation]

theorem symmetricPolynomialDerivation_smul (c : K) (T : Module.End K M) :
    symmetricPolynomialDerivation (c • T) =
      c • symmetricPolynomialDerivation T := by
  apply MvPolynomial.derivation_ext
  intro j
  simp [symmetricPolynomialDerivation]

/-- Transporting the induced symmetric derivation to the chosen polynomial presentation recovers
the polynomial derivation used in its construction. -/
theorem symmetricAlgebraDerivation_equiv_apply
    (T : Module.End K M) (x : SymmetricAlgebra K M) :
    symmetricPolynomialEquiv (K := K) (M := M)
        (symmetricAlgebraDerivation T x) =
      symmetricPolynomialDerivation T
        (symmetricPolynomialEquiv (K := K) (M := M) x) := by
  simp [symmetricAlgebraDerivation]

theorem symmetricAlgebraDerivation_add (T U : Module.End K M) :
    symmetricAlgebraDerivation (T + U) =
      symmetricAlgebraDerivation T + symmetricAlgebraDerivation U := by
  ext x
  apply (symmetricPolynomialEquiv (K := K) (M := M)).injective
  simp only [symmetricAlgebraDerivation_equiv_apply, Derivation.add_apply, map_add]
  rw [symmetricPolynomialDerivation_add, Derivation.add_apply]

theorem symmetricAlgebraDerivation_smul (c : K) (T : Module.End K M) :
    symmetricAlgebraDerivation (c • T) =
      c • symmetricAlgebraDerivation T := by
  ext x
  apply (symmetricPolynomialEquiv (K := K) (M := M)).injective
  simp only [symmetricAlgebraDerivation_equiv_apply, Derivation.smul_apply, map_smul]
  rw [symmetricPolynomialDerivation_smul, Derivation.smul_apply]

/-- Linear state actions extend linearly to derivations of the symmetric observable algebra. -/
def symmetricAlgebraDerivationLinearMap :
    Module.End K M →ₗ[K]
      Derivation K (SymmetricAlgebra K M) (SymmetricAlgebra K M) where
  toFun := symmetricAlgebraDerivation
  map_add' := symmetricAlgebraDerivation_add
  map_smul' := symmetricAlgebraDerivation_smul

end

end GaloisForLFunctions.HTGeometry
