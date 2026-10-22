import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicReducedStrongCyclicHom
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicTopology

/-!
# Exact closed relative CCM cyclic module over the rational adeles

This is the literal degreewise closed cokernel required by CCM Definition
4.10: target is the continuous-field cyclic submodule whose main-diagonal
trace lies in `S(C_ℚ)`, topology is projective on ambient fields and LF on the
strong diagonal coordinate, and source is the exact double-endpoint reduced
adelic cyclic module.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

/-- Exact rational CCM relative cyclic module: strong target modulo closure of
the genuine reduced adelic restriction range. -/
def CCMRationalAdelicClosedStrongRelativeCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicReducedStrongCyclicHom.closedCokernel
    ccmRationalStrongCyclicTopology

/-- Canonical projection from exact strong chains to the closed relative CCM
cyclic module. -/
def ccmRationalAdelicClosedStrongRelativeCyclicProjection :
    CCMRationalStrongCyclicTarget.simplicial ⟶
      CCMRationalAdelicClosedStrongRelativeCyclicModule.simplicial :=
  ccmRationalAdelicReducedStrongCyclicHom.closedCokernelProjection
    ccmRationalStrongCyclicTopology

/-- Degreewise closed restriction range used in the exact relative module. -/
abbrev CCMRationalAdelicClosedStrongRestrictionRange (n : ℕ) :=
  ccmRationalStrongCyclicTopology.closedRange
    ccmRationalAdelicReducedStrongCyclicHom (.op (.mk n))

@[simp]
theorem ccmRationalAdelicClosedStrongRelativeCyclicProjection_apply
    (n : ℕ) (x : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalAdelicClosedStrongRelativeCyclicProjection.app
        (.op (.mk n)) x =
      (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ x :=
  rfl

end GaloisForLFunctions.RHTower
