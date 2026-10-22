import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicClosedStrongRelativeCyclicModule
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicReducedSourceClassSpaceAction
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicActionContinuity
import GaloisForLFunctions.RHTower.ClosedCyclicModuleEndomorphism

/-!
# CCM Lefschetz action on the exact closed relative cyclic module

Source translation, exact restriction equivariance, and continuity of strong
class-space translation imply that every `c in C_Q` preserves the closure of
the genuine reduced-source range.  Thus the literal CCM Lefschetz action
descends to the Definition 4.10 closed relative cyclic module.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection

/-- **Exact closed-relative CCM Lefschetz correspondence.** -/
def ccmRationalAdelicClosedStrongLefschetz (c : Section) :
    CyclicModule.Hom CCMRationalAdelicClosedStrongRelativeCyclicModule
      CCMRationalAdelicClosedStrongRelativeCyclicModule :=
  ccmRationalAdelicReducedStrongCyclicHom.closedCokernelEnd
    ccmRationalStrongCyclicTopology
    (ccmRationalAdelicReducedSourceCyclicClassSpaceRightAction c)
    (ccmRationalStrongCyclicRightAction c)
    (ccmRationalAdelicReducedStrongCyclicHom_classSpaceRightAction c)
    (ccmRationalStrongCyclicRightActionDegree_continuous c)

@[simp]
theorem ccmRationalAdelicClosedStrongLefschetz_mkQ
    (c : Section) (n : ℕ)
    (y : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongLefschetz c).simplicial.app
        (.op (.mk n))
        ((CCMRationalAdelicClosedStrongRestrictionRange n).mkQ y) =
      (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ
        (ccmRationalStrongCyclicRightActionDegree c n y) :=
  rfl

/-- The identity class acts identically on the exact closed quotient. -/
theorem ccmRationalAdelicClosedStrongLefschetz_one_degree
    (n : ℕ)
    (q : CCMRationalAdelicClosedStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongLefschetz 1).simplicial.app
        (.op (.mk n)) q = q := by
  obtain ⟨y, rfl⟩ :=
    (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ_surjective q
  rw [ccmRationalAdelicClosedStrongLefschetz_mkQ,
    ccmRationalStrongCyclicRightActionDegree_one]

/-- Multiplication in the class-space section is composition of descended
Lefschetz correspondences. -/
theorem ccmRationalAdelicClosedStrongLefschetz_mul_degree
    (c d : Section) (n : ℕ)
    (q : CCMRationalAdelicClosedStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongLefschetz c).simplicial.app (.op (.mk n))
        ((ccmRationalAdelicClosedStrongLefschetz d).simplicial.app
          (.op (.mk n)) q) =
      (ccmRationalAdelicClosedStrongLefschetz (c * d)).simplicial.app
        (.op (.mk n)) q := by
  obtain ⟨y, rfl⟩ :=
    (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ_surjective q
  rw [ccmRationalAdelicClosedStrongLefschetz_mkQ,
    ccmRationalAdelicClosedStrongLefschetz_mkQ,
    ccmRationalAdelicClosedStrongLefschetz_mkQ,
    ccmRationalStrongCyclicRightActionDegree_mul]

/-- Every descended Lefschetz correspondence is invertible, independently of
whether the quotient is later shown nonzero. -/
theorem ccmRationalAdelicClosedStrongLefschetz_leftInverse_degree
    (c : Section) (n : ℕ)
    (q : CCMRationalAdelicClosedStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongLefschetz c⁻¹).simplicial.app (.op (.mk n))
        ((ccmRationalAdelicClosedStrongLefschetz c).simplicial.app
          (.op (.mk n)) q) = q := by
  rw [ccmRationalAdelicClosedStrongLefschetz_mul_degree]
  simpa using ccmRationalAdelicClosedStrongLefschetz_one_degree n q

end GaloisForLFunctions.RHTower
