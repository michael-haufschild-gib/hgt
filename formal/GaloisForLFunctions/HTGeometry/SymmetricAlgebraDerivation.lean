import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie

/-!
# Linear state actions as derivations of a symmetric observable algebra

Every linear endomorphism `T` of a vector space extends canonically to a derivation of its symmetric
algebra by the law `D_T(ι(m)) = ι(Tm)`.  We construct the derivation through a chosen basis and the
polynomial presentation of the symmetric algebra, then prove the generator formula, which makes the
result independent of the presentation.  Commuting linear actions induce commuting derivations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [AddCommGroup M] [Module K M]

/-- The chosen basis index used only to construct the induced derivation. -/
abbrev SymmetricBasisIndex (K : Type u) (M : Type v)
    [Field K] [AddCommGroup M] [Module K M] :=
  Module.Free.ChooseBasisIndex K M

/-- A chosen vector-space basis. -/
def symmetricChosenBasis : Module.Basis (SymmetricBasisIndex K M) K M :=
  Module.Free.chooseBasis K M

/-- The polynomial presentation of the symmetric observable algebra in the chosen basis. -/
def symmetricPolynomialEquiv :
    SymmetricAlgebra K M ≃ₐ[K] MvPolynomial (SymmetricBasisIndex K M) K :=
  SymmetricAlgebra.equivMvPolynomial (symmetricChosenBasis (K := K) (M := M))

/-- The polynomial derivation that sends a basis variable to the linear observable `ι(T b)`. -/
def symmetricPolynomialDerivation (T : M →ₗ[K] M) :
    Derivation K (MvPolynomial (SymmetricBasisIndex K M) K)
      (MvPolynomial (SymmetricBasisIndex K M) K) :=
  MvPolynomial.mkDerivation K fun j =>
    symmetricPolynomialEquiv (K := K) (M := M)
      (SymmetricAlgebra.ι K M (T (symmetricChosenBasis (K := K) (M := M) j)))

/-- The polynomial derivation acts on every linear observable by the original state action. -/
theorem symmetricPolynomialDerivation_on_ι
    (T : M →ₗ[K] M) (m : M) :
    symmetricPolynomialDerivation T
        (symmetricPolynomialEquiv (K := K) (M := M)
          (SymmetricAlgebra.ι K M m)) =
      symmetricPolynomialEquiv (K := K) (M := M)
        (SymmetricAlgebra.ι K M (T m)) := by
  let b := symmetricChosenBasis (K := K) (M := M)
  let e := symmetricPolynomialEquiv (K := K) (M := M)
  let D := symmetricPolynomialDerivation T
  let left : M →ₗ[K] MvPolynomial (SymmetricBasisIndex K M) K :=
    D.toLinearMap.comp (e.toLinearMap.comp (SymmetricAlgebra.ι K M))
  let right : M →ₗ[K] MvPolynomial (SymmetricBasisIndex K M) K :=
    e.toLinearMap.comp ((SymmetricAlgebra.ι K M).comp T)
  have hmaps : left = right := by
    apply b.ext
    intro j
    simp [left, right, D, e, b, symmetricPolynomialDerivation,
      symmetricPolynomialEquiv, symmetricChosenBasis]
  exact LinearMap.congr_fun hmaps m

/-- The induced derivation of the symmetric observable algebra. -/
def symmetricAlgebraDerivation (T : M →ₗ[K] M) :
    Derivation K (SymmetricAlgebra K M) (SymmetricAlgebra K M) :=
  let e := symmetricPolynomialEquiv (K := K) (M := M)
  let D := symmetricPolynomialDerivation T
  Derivation.mk'
    (e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap))
    (by
      intro x y
      change e.symm (D (e (x * y))) =
        x • e.symm (D (e y)) + y • e.symm (D (e x))
      simp [Derivation.leibniz])

/-- **Observable-action law.**  The induced derivation sends the observable of a state to the
observable of its transformed state. -/
theorem symmetricAlgebraDerivation_ι
    (T : M →ₗ[K] M) (m : M) :
    symmetricAlgebraDerivation T (SymmetricAlgebra.ι K M m) =
      SymmetricAlgebra.ι K M (T m) := by
  apply (symmetricPolynomialEquiv (K := K) (M := M)).injective
  simp [symmetricAlgebraDerivation,
    symmetricPolynomialDerivation_on_ι]

/-- Commuting linear state actions induce commuting polynomial derivations. -/
theorem symmetricPolynomialDerivation_commute
    (T U : M →ₗ[K] M) (hTU : Function.Commute T U) :
    Function.Commute (symmetricPolynomialDerivation T)
      (symmetricPolynomialDerivation U) := by
  let b := symmetricChosenBasis (K := K) (M := M)
  let e := symmetricPolynomialEquiv (K := K) (M := M)
  let DT := symmetricPolynomialDerivation T
  let DU := symmetricPolynomialDerivation U
  have hbracket : ⁅DT, DU⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [Derivation.commutator_apply]
    have hDU : DU (MvPolynomial.X j) =
        e (SymmetricAlgebra.ι K M (U (b j))) := by
      simp [DU, e, b, symmetricPolynomialDerivation,
        symmetricPolynomialEquiv, symmetricChosenBasis]
    have hDT : DT (MvPolynomial.X j) =
        e (SymmetricAlgebra.ι K M (T (b j))) := by
      simp [DT, e, b, symmetricPolynomialDerivation,
        symmetricPolynomialEquiv, symmetricChosenBasis]
    rw [hDU, hDT]
    rw [symmetricPolynomialDerivation_on_ι,
      symmetricPolynomialDerivation_on_ι, hTU (b j), sub_self]
    rfl
  intro p
  have hp := Derivation.congr_fun hbracket p
  rw [Derivation.commutator_apply] at hp
  simpa using sub_eq_zero.mp hp

/-- **Commuting observable dynamics.**  Commuting linear state actions extend to commuting
derivations of the full symmetric observable algebra. -/
theorem symmetricAlgebraDerivation_commute
    (T U : M →ₗ[K] M) (hTU : Function.Commute T U) :
    Function.Commute (symmetricAlgebraDerivation T)
      (symmetricAlgebraDerivation U) := by
  let e := symmetricPolynomialEquiv (K := K) (M := M)
  have hp := symmetricPolynomialDerivation_commute T U hTU
  intro x
  apply e.injective
  simpa [e, symmetricAlgebraDerivation] using hp (e x)

end

end GaloisForLFunctions.HTGeometry
