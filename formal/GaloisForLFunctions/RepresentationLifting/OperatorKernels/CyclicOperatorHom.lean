import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CyclicQuotientHom
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Polynomial cyclic modules and concrete operator kernels

For any linear operator `T`, polynomial-linear maps from `K[X]/(p)` to
the module on which `X` acts as `T` are exactly the vectors in `ker p(T)`.
This converts the cyclic generator reduction into a coefficient-field
linear equivalence, usable for dimension statements about actual operators.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Polynomial-module homomorphisms into the module defined by the given operator. -/
abbrev CyclicOperatorHom (T : Module.End K V) (p : K[X]) :=
  CyclicQuotient p →ₗ[K[X]] Module.AEval' T

/-- Forgetting the polynomial action identifies its annihilator with the evaluated kernel. -/
def operatorAnnihilatorEquiv (T : Module.End K V) (p : K[X]) :
    (LinearMap.ker (LinearMap.lsmul K[X] (Module.AEval' T) p)).restrictScalars K ≃ₗ[K]
      LinearMap.ker (aeval T p) where
  toFun v := ⟨(Module.AEval'.of T).symm v.val, by
    exact congrArg (Module.AEval'.of T).symm v.property⟩
  invFun v := ⟨Module.AEval'.of T v.val, by
    exact congrArg (Module.AEval'.of T) v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact evaluation-at-one correspondence for every polynomial and every linear operator. -/
def cyclicOperatorHomEquiv (T : Module.End K V) (p : K[X]) :
    CyclicOperatorHom T p ≃ₗ[K] LinearMap.ker (aeval T p) :=
  ((cyclicQuotientHomEquiv (M := Module.AEval' T) p).restrictScalars K).trans
    (operatorAnnihilatorEquiv T p)

/-- An operator's solution-space dimension is the dimension of the corresponding Hom space. -/
theorem finrank_cyclicOperatorHom (T : Module.End K V) (p : K[X]) :
    Module.finrank K (CyclicOperatorHom T p) = Module.finrank K (LinearMap.ker (aeval T p)) :=
  (cyclicOperatorHomEquiv T p).finrank_eq

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.cyclicOperatorHomEquiv
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.finrank_cyclicOperatorHom
