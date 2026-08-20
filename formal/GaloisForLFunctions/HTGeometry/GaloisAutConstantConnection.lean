import GaloisForLFunctions.HTGeometry.DifferenceGaloisEndgame
import GaloisForLFunctions.HTGeometry.ConstantGaloisConnection
import GaloisForLFunctions.HTGeometry.FundamentalMatrixIsomonodromy

/-!
# A constant Galois group forces a connection over the base

If every Galois automorphism commutes with the derivation and moves the fundamental matrix by a
matrix of constants, the crossed-homomorphism law makes the logarithmic derivative of the
fundamental matrix Galois invariant, and the Galois correspondence puts its entries in the base
field.  Together with the isomonodromy equation carried by a fundamental matrix, that is the step
from a constant Galois group to isomonodromy over the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

variable {K R C : Type*} [Field K] [CommRing R] [Nontrivial R] [Differential R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- **A constant Galois group forces a connection over the base.**  If every Galois automorphism
commutes with the derivation and moves the fundamental matrix by a constant matrix, the logarithmic
derivative of the fundamental matrix has entries in the base field. -/
theorem exists_base_logDerivMatrix_of_galoisAutAt_constant
    (E : Subalgebra C (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n R) [Invertible Y]
    (hδ : ∀ χ ∈ S, ∀ x : R, (galoisAutAt E b hgen hindep χ) (Differential.deriv x)
      = Differential.deriv ((galoisAutAt E b hgen hindep χ) x))
    (hconst : ∀ χ ∈ S,
      matrixDeriv (⅟Y * Y.map ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R → R)) = 0) :
    ∀ i j, ∃ a : K, logDerivMatrix Y i j = algebraMap K R a := by
  intro i j
  refine exists_eq_algebraMap_of_forall_galoisAutAt E b hgen hindep S hsep ?_
  intro χ hχ
  set φ : R →+* R := ((galoisAutAt E b hgen hindep χ : R →ₐ[C] R) : R →+* R) with hφ
  letI hYσ : Invertible (Y.map φ) := invertibleMapRingHom φ Y
  letI hg : Invertible (⅟Y * Y.map φ) :=
    { invOf := ⅟(Y.map φ) * Y
      invOf_mul_self := by
        rw [mul_assoc, ← mul_assoc Y, mul_invOf_self Y, one_mul, invOf_mul_self (Y.map φ)]
      mul_invOf_self := by
        rw [mul_assoc, ← mul_assoc (Y.map φ), mul_invOf_self (Y.map φ), one_mul,
          invOf_mul_self Y] }
  have hYg : Y.map φ = Y * (⅟Y * Y.map φ) := by
    rw [← mul_assoc, mul_invOf_self Y, one_mul]
  have h := logDerivMatrix_map_eq_self φ (hδ χ hχ) Y (⅟Y * Y.map φ) hYg (hconst χ hχ)
  have h2 := congrFun (congrFun h i) j
  have h3 : φ (logDerivMatrix Y i j) = logDerivMatrix Y i j := by
    simpa [Matrix.map_apply] using h2
  exact h3

end

end GaloisForLFunctions.HTGeometry
