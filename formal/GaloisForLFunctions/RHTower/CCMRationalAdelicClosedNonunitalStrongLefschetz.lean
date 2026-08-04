import GaloisForLFunctions.RHTower.CCMRationalNonunitalStrongCyclicActionContinuity
import GaloisForLFunctions.RHTower.ClosedCyclicModuleEndomorphism

/-!
# Closed relative CCM module and Lefschetz action for the literal target

This is the closed cokernel of the sealed reduced adelic restriction inside
the cyclic module of the nonunital algebra of continuous trace-class fields.
Continuity and exact equivariance make every class-space translation preserve
the closed range, hence descend to the literal Definition 4.10 recipient.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection

/-- Literal rational CCM relative cyclic module: Definition 4.9 target modulo
the closure of the exact reduced-source restriction range. -/
def CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule :
    CyclicModule ℂ :=
  ccmRationalAdelicReducedNonunitalStrongCyclicHom.closedCokernel
    ccmRationalNonunitalStrongCyclicTopology

/-- Canonical projection to the literal closed relative cyclic module. -/
def ccmRationalAdelicClosedNonunitalStrongRelativeCyclicProjection :
    CCMRationalNonunitalStrongCyclicTarget.simplicial ⟶
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule.simplicial :=
  ccmRationalAdelicReducedNonunitalStrongCyclicHom.closedCokernelProjection
    ccmRationalNonunitalStrongCyclicTopology

/-- Degreewise closed exact restriction range. -/
abbrev CCMRationalAdelicClosedNonunitalStrongRestrictionRange (n : ℕ) :=
  ccmRationalNonunitalStrongCyclicTopology.closedRange
    ccmRationalAdelicReducedNonunitalStrongCyclicHom (.op (.mk n))

@[simp]
theorem ccmRationalAdelicClosedNonunitalStrongRelativeCyclicProjection_apply
    (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalAdelicClosedNonunitalStrongRelativeCyclicProjection.app
        (.op (.mk n)) x =
      (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ x :=
  rfl

/-- **Literal closed-relative CCM Lefschetz correspondence.** -/
def ccmRationalAdelicClosedNonunitalStrongLefschetz (c : Section) :
    CyclicModule.Hom
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule :=
  ccmRationalAdelicReducedNonunitalStrongCyclicHom.closedCokernelEnd
    ccmRationalNonunitalStrongCyclicTopology
    (ccmRationalAdelicTwistedReducedSourceCyclicClassSpaceRightAction c)
    (ccmRationalNonunitalStrongCyclicRightAction c)
    (ccmRationalAdelicReducedNonunitalStrongCyclicHom_classSpaceRightAction c)
    (ccmRationalNonunitalStrongCyclicRightActionDegree_continuous c)

@[simp]
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_mkQ
    (c : Section) (n : ℕ)
    (y : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
        (.op (.mk n))
        ((CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ y) =
      (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ
        (ccmRationalNonunitalStrongCyclicRightActionDegree c n y) :=
  rfl

/-- Identity class acts identically on the literal closed quotient. -/
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_one_degree
    (n : ℕ)
    (q :
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongLefschetz 1).simplicial.app
        (.op (.mk n)) q = q := by
  obtain ⟨y, rfl⟩ :=
    (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ_surjective q
  rw [ccmRationalAdelicClosedNonunitalStrongLefschetz_mkQ,
    ccmRationalNonunitalStrongCyclicRightActionDegree_one]

/-- Multiplication is composition of descended literal Lefschetz
correspondences. -/
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_mul_degree
    (c d : Section) (n : ℕ)
    (q :
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz d).simplicial.app
          (.op (.mk n)) q) =
      (ccmRationalAdelicClosedNonunitalStrongLefschetz (c * d)).simplicial.app
        (.op (.mk n)) q := by
  obtain ⟨y, rfl⟩ :=
    (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ_surjective q
  rw [ccmRationalAdelicClosedNonunitalStrongLefschetz_mkQ,
    ccmRationalAdelicClosedNonunitalStrongLefschetz_mkQ,
    ccmRationalAdelicClosedNonunitalStrongLefschetz_mkQ,
    ccmRationalNonunitalStrongCyclicRightActionDegree_mul]

/-- Every literal descended Lefschetz correspondence is invertible. -/
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_leftInverse_degree
    (c : Section) (n : ℕ)
    (q :
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongLefschetz c⁻¹).simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk n)) q) = q := by
  rw [ccmRationalAdelicClosedNonunitalStrongLefschetz_mul_degree]
  simpa using
    ccmRationalAdelicClosedNonunitalStrongLefschetz_one_degree n q

end GaloisForLFunctions.RHTower
