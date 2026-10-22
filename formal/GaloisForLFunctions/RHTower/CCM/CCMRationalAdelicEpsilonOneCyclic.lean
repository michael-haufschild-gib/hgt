import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonOne
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonZeroCyclic
import GaloisForLFunctions.RHTower.CyclicModuleDoubleKernel

/-!
# Both CCM endpoints and the genuine reduced cyclic source

The Haar endpoint trace is lifted in every cyclic degree by the universal trace-to-cyclic-morphism
construction. Together with the zero-fixed-point endpoint, it defines the reduced rational CCM
source as the literal degreewise intersection `ker ε₀ ∩ ker ε₁` in the category of cyclic
modules. Faces, degeneracies, and cyclic rotation are inherited without a degree-zero proxy.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Second CCM endpoint cyclic morphism `ε₁ⁿ`, induced by adelic Haar trace. -/
def ccmRationalAdelicEpsilonOneCyclicHom :
    CyclicModule.Hom CCMRationalAdelicSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalAdelicEpsilonOne
    ccmRationalAdelicEpsilonOne_isTrace

@[simp]
theorem ccmRationalAdelicEpsilonOneCyclicHom_app (n : ℕ) :
    ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app (.op (.mk n)) =
      ModuleCat.ofHom
        (cyclicBarTraceAugmentation ccmRationalAdelicEpsilonOne n) :=
  rfl

/-- First endpoint restricted to the correct nonunital cyclic source. -/
def ccmRationalAdelicNonunitalEpsilonZeroCyclicHom :
    CyclicModule.Hom CCMRationalAdelicNonunitalSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  CyclicModule.Hom.comp ccmRationalAdelicNonunitalSourceCyclicInclusion
    ccmRationalAdelicEpsilonZeroCyclicHom

/-- Haar endpoint restricted to the correct nonunital cyclic source. -/
def ccmRationalAdelicNonunitalEpsilonOneCyclicHom :
    CyclicModule.Hom CCMRationalAdelicNonunitalSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  CyclicModule.Hom.comp ccmRationalAdelicNonunitalSourceCyclicInclusion
    ccmRationalAdelicEpsilonOneCyclicHom

/-- Genuine reduced CCM cyclic source: first remove the adjoined scalar unit, then impose
`ker ε₀ ∩ ker ε₁`. -/
abbrev CCMRationalAdelicReducedSourceCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.doubleKernel
    ccmRationalAdelicNonunitalEpsilonOneCyclicHom

/-- Canonical inclusion of the reduced cyclic source into the full source. -/
def ccmRationalAdelicReducedSourceCyclicInclusion :
  CyclicModule.Hom CCMRationalAdelicReducedSourceCyclicModule
      CCMRationalAdelicSourceCyclicModule :=
  CyclicModule.Hom.comp
    (ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.doubleKernelInclusion
      ccmRationalAdelicNonunitalEpsilonOneCyclicHom)
    ccmRationalAdelicNonunitalSourceCyclicInclusion

/-- Membership in the reduced degree is exactly simultaneous vanishing of both endpoints. -/
theorem ccmRationalAdelicReducedSourceCyclicModule_mem_iff
    (n : ℕ)
    (x : CCMRationalAdelicNonunitalSourceCyclicModule.simplicial.obj
      (.op (.mk n))) :
    x ∈ ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.doubleKernelSubmodule
        ccmRationalAdelicNonunitalEpsilonOneCyclicHom (.op (.mk n)) ↔
      ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.simplicial.app
          (.op (.mk n)) x = 0 ∧
        ccmRationalAdelicNonunitalEpsilonOneCyclicHom.simplicial.app
          (.op (.mk n)) x = 0 :=
  CyclicModule.Hom.mem_doubleKernelSubmodule_iff _ _ _ _

end RHTower
end GaloisForLFunctions
