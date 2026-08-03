import GaloisForLFunctions.RHTower.CCMRationalMoritaTraceClassAlgebra
import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonOneCyclic
import GaloisForLFunctions.RHTower.CCMRationalAdelicCyclicRestrictionFormula
import GaloisForLFunctions.RHTower.CyclicBarAlgHomMorphism
import GaloisForLFunctions.RHTower.CyclicModuleCokernel

/-!
# Exact rational adeles class-space cyclic module

The Morita representation at every nonzero adelic base assembles pointwise into an algebra
homomorphism from the exact unitized CCM source to the algebra of trace-class Morita sections.
Cyclic-bar functoriality then supplies the full all-degree class-space cyclic morphism.  Restriction
to `ker ε₀ ∩ ker ε₁` is literal composition in the category of cyclic modules.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-- Algebra of normalized trace-class Morita sections over all genuine adelic bases. -/
abbrev CCMRationalAdelicMoritaClassSpaceAlgebra :=
  CCMRationalAdelicMoritaBase → CCMRationalMoritaTraceClassUnitization

/-- Exact pointwise Morita restriction to the rational adeles class space. -/
def ccmRationalAdelicMoritaClassSpaceAlgHom :
    Source →ₐ[ℂ] CCMRationalAdelicMoritaClassSpaceAlgebra where
  toFun x base :=
    ccmRationalAdelicMoritaUnitizedHom base.bInf_ne_zero base.bFin x
  map_one' := by
    funext base
    change ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin 1 = 1
    exact (ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin).map_one
  map_mul' x y := by
    funext base
    change ccmRationalAdelicMoritaUnitizedHom
        base.bInf_ne_zero base.bFin (x * y) =
      ccmRationalAdelicMoritaUnitizedHom base.bInf_ne_zero base.bFin x *
        ccmRationalAdelicMoritaUnitizedHom base.bInf_ne_zero base.bFin y
    exact map_mul (ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin) x y
  map_zero' := by
    funext base
    change ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin 0 = 0
    exact map_zero (ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin)
  map_add' x y := by
    funext base
    change ccmRationalAdelicMoritaUnitizedHom
        base.bInf_ne_zero base.bFin (x + y) =
      ccmRationalAdelicMoritaUnitizedHom base.bInf_ne_zero base.bFin x +
        ccmRationalAdelicMoritaUnitizedHom base.bInf_ne_zero base.bFin y
    exact map_add (ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin) x y
  commutes' z := by
    funext base
    rw [Pi.algebraMap_apply]
    exact (ccmRationalAdelicMoritaUnitizedHom
      base.bInf_ne_zero base.bFin).commutes z

@[simp]
theorem ccmRationalAdelicMoritaClassSpaceAlgHom_apply
    (x : Source) (base : CCMRationalAdelicMoritaBase) :
    ccmRationalAdelicMoritaClassSpaceAlgHom x base =
      ccmRationalAdelicMoritaUnitizedHom
        base.bInf_ne_zero base.bFin x :=
  rfl

/-- Full cyclic module of algebraic trace-class Morita sections on the rational adeles class
space. -/
abbrev CCMRationalAdelicClassSpaceCyclicModule : CyclicModule ℂ :=
  cyclicBarCyclicModule
    (R := ℂ) (A := CCMRationalAdelicMoritaClassSpaceAlgebra)

/-- Full all-degree cyclic restriction from the unitized adelic crossed product. -/
def ccmRationalAdelicClassSpaceCyclicHom :
    CyclicModule.Hom CCMRationalAdelicSourceCyclicModule
      CCMRationalAdelicClassSpaceCyclicModule :=
  cyclicBarAlgHomCyclicHom ccmRationalAdelicMoritaClassSpaceAlgHom

@[simp]
theorem ccmRationalAdelicClassSpaceCyclicHom_app (n : ℕ) :
    ccmRationalAdelicClassSpaceCyclicHom.simplicial.app (.op (.mk n)) =
      ModuleCat.ofHom
        (cyclicBarAlgHomDegree ccmRationalAdelicMoritaClassSpaceAlgHom n) :=
  rfl

/-- Exact CCM reduced-source restriction into the full class-space cyclic module. -/
def ccmRationalAdelicReducedClassSpaceCyclicHom :
    CyclicModule.Hom CCMRationalAdelicReducedSourceCyclicModule
      CCMRationalAdelicClassSpaceCyclicModule :=
  CyclicModule.Hom.comp ccmRationalAdelicReducedSourceCyclicInclusion
    ccmRationalAdelicClassSpaceCyclicHom

/-- Algebraic relative CCM cyclic module before closing the reduced restriction range. -/
abbrev CCMRationalAdelicAlgebraicRelativeCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicReducedClassSpaceCyclicHom.cokernel

/-- Canonical projection of class-space chains to the algebraic relative cyclic module. -/
def ccmRationalAdelicAlgebraicRelativeCyclicProjection :
    CCMRationalAdelicClassSpaceCyclicModule.simplicial ⟶
      CCMRationalAdelicAlgebraicRelativeCyclicModule.simplicial :=
  ccmRationalAdelicReducedClassSpaceCyclicHom.cokernelProjection

end RHTower
end GaloisForLFunctions
