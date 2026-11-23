import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineRationalPoints
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialPrimePoints
import GaloisForLFunctions.HTGeometry.AlgebraPointResidueField
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! First-order interpolation at finitely many rational points of an affine chart. -/

open AlgebraicGeometry CategoryTheory Function
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)} {U : X.Opens}

/-- Prescribed first-order residues at distinct rational points are the residues of
a single section on their common affine chart. -/
theorem exists_affine_section_firstJets (hU : IsAffineOpen U) {J : Type*} [Finite J]
    (y : J → {y : X.BaseFieldPointOver K s // y.hom default ∈ U}) (hy : Function.Injective y)
    (g : J → SectionRing s U) :
    ∃ a : SectionRing s U, ∀ j,
      a - g j ∈ RingHom.ker (affinePointEval (y j).1 (y j).2).toRingHom ^ 2 := by
  let m (j : J) := RingHom.ker (affinePointEval (y j).1 (y j).2).toRingHom
  have hm : Function.Injective m := by
    intro i j h
    apply hy
    apply (affinePointEquiv hU).injective
    apply rationalPolynomialPointPrime_injective K (SectionRing s U)
    exact Subtype.ext h
  letI (j : J) : (m j).IsMaximal := algebraPointKernel_isMaximal _
  have hc : Pairwise (IsCoprime on fun j => m j ^ 2) :=
    fun _ _ hij => (Ideal.isCoprime_of_isMaximal (hm.ne hij)).pow
  exact Ideal.exists_forall_sub_mem_ideal hc g

end GlobalTheory.SchemeCohomology
