import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonZero
import GaloisForLFunctions.RHTower.CyclicBarTraceMorphism

/-!
# The first CCM endpoint as a genuine cyclic-module morphism

This file applies the universal trace-to-cyclic-morphism theorem to the actual minimal unitization
of the rational adelic crossed product.  Thus `ε₀ⁿ` exists in every cyclic degree and is not a
degree-zero proxy.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Genuine tensor cyclic bar of the actual rational CCM source algebra. -/
abbrev CCMRationalAdelicSourceCyclicModule : CyclicModule ℂ :=
  cyclicBarCyclicModule
    (R := ℂ) (A := CCMRationalAdelicCyclicSourceAlgebra)

/-- First CCM endpoint cyclic morphism `ε₀ⁿ`. -/
def ccmRationalAdelicEpsilonZeroCyclicHom :
    CyclicModule.Hom CCMRationalAdelicSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalAdelicEpsilonZero
    ccmRationalAdelicEpsilonZero_isTrace

@[simp]
theorem ccmRationalAdelicEpsilonZeroCyclicHom_app (n : ℕ) :
    ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app (.op (.mk n)) =
      ModuleCat.ofHom
        (cyclicBarTraceAugmentation ccmRationalAdelicEpsilonZero n) :=
  rfl

end RHTower
end GaloisForLFunctions
