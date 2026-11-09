import GaloisForLFunctions.HTGeometry.MonicRootDiscriminant
import GaloisForLFunctions.HTGeometry.MonicDistinctRootFactorization
import Mathlib.RingTheory.Discriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Power-basis and polynomial discriminants

Embeddings of a separable simple field extension give all distinct roots
of its generator's minimal polynomial. The trace determinant and the
Sylvester discriminant are consequently the same Vandermonde square.
-/

noncomputable section
open Finset Polynomial
namespace GaloisForLFunctions.HTGeometry
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

/-- A separable power basis has exactly the Sylvester discriminant of its minimal polynomial. -/
theorem powerBasis_discr_eq_minpoly_discr (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  classical
  letI : Module.Finite K L := pb.finite
  let E := AlgebraicClosure K
  let e : Fin pb.dim ≃ (L →ₐ[K] E) :=
    (Fintype.equivFinOfCardEq ((AlgHom.card K L E).trans pb.finrank)).symm
  let x : Fin pb.dim → E := fun i => e i pb.gen
  have hx : Function.Injective x := by
    intro i j hij
    apply e.injective
    exact pb.algHom_ext hij
  have hroot (i : Fin pb.dim) :
      ((minpoly K pb.gen).map (algebraMap K E)).IsRoot (x i) := by
    change Polynomial.eval (x i) ((minpoly K pb.gen).map (algebraMap K E)) = 0
    rw [eval_map_algebraMap]
    change aeval (e i pb.gen) (minpoly K pb.gen) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  have hm := minpoly.monic pb.isIntegral_gen
  have hn : ((minpoly K pb.gen).map (algebraMap K E)).natDegree = pb.dim :=
    (hm.natDegree_map _).trans pb.natDegree_minpoly
  have hp := eq_prod_X_sub_C_of_monic_of_injective_roots (hm.map _) hn hx hroot
  apply (algebraMap K E).injective
  rw [map_discr_of_monic _ hm, hp, discr_rootPolynomial]
  simpa only [vandermondeProd, Finset.prod_pow] using
    Algebra.discr_powerBasis_eq_prod K E pb e

/-- The residue-field power-basis discriminant is the discriminant of its monic defining polynomial. -/
theorem adjoinRoot_powerBasis_discr_eq {F : Type*} [Field F] [PerfectField F]
    {f : F[X]} (hf : f.Monic) (hi : Irreducible f) :
    Algebra.discr F (AdjoinRoot.powerBasis hi.ne_zero).basis = f.discr := by
  letI : Fact (Irreducible f) := ⟨hi⟩
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  rw [powerBasis_discr_eq_minpoly_discr, AdjoinRoot.minpoly_powerBasis_gen_of_monic hf]

#print axioms powerBasis_discr_eq_minpoly_discr
#print axioms adjoinRoot_powerBasis_discr_eq
end GaloisForLFunctions.HTGeometry
