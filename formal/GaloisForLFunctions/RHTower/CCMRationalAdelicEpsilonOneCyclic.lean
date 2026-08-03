import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonOne
import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonZeroCyclic
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

/-- Genuine reduced CCM cyclic source `ker ε₀ ∩ ker ε₁`. -/
abbrev CCMRationalAdelicReducedSourceCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicEpsilonZeroCyclicHom.doubleKernel
    ccmRationalAdelicEpsilonOneCyclicHom

/-- Canonical inclusion of the reduced cyclic source into the full source. -/
def ccmRationalAdelicReducedSourceCyclicInclusion :
    CyclicModule.Hom CCMRationalAdelicReducedSourceCyclicModule
      CCMRationalAdelicSourceCyclicModule :=
  ccmRationalAdelicEpsilonZeroCyclicHom.doubleKernelInclusion
    ccmRationalAdelicEpsilonOneCyclicHom

/-- Membership in the reduced degree is exactly simultaneous vanishing of both endpoints. -/
theorem ccmRationalAdelicReducedSourceCyclicModule_mem_iff
    (n : ℕ)
    (x : CCMRationalAdelicSourceCyclicModule.simplicial.obj (.op (.mk n))) :
    x ∈ ccmRationalAdelicEpsilonZeroCyclicHom.doubleKernelSubmodule
        ccmRationalAdelicEpsilonOneCyclicHom (.op (.mk n)) ↔
      ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app (.op (.mk n)) x = 0 ∧
        ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app (.op (.mk n)) x = 0 :=
  CyclicModule.Hom.mem_doubleKernelSubmodule_iff _ _ _ _

end RHTower
end GaloisForLFunctions
