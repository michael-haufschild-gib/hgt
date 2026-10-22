import GaloisForLFunctions.RHTower.CCM.CCMRationalNonunitalStrongCyclicTopology
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicActionContinuity
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongCyclicLefschetz

/-!
# Continuous class-space action on literal nonunital strong chains

The faithful global-to-pointwise field embedding intertwines right
translation.  Since pointwise-field translation is continuous for the
projective/LF graph topology, literal nonunital translation is continuous for
the induced faithful topology.  Identity and product laws are reflected back
through the injective cyclic embedding.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev FieldUnit :=
  CCMRationalContinuousTraceNormIdealFieldUnitization

theorem ccmRationalNonunitalFieldToPointwiseAlgHom_rightAction
    (c : Section) (x : FieldUnit) :
    ccmRationalNonunitalFieldToPointwiseAlgHom
        (ccmRationalNonunitalFieldRightActionAlgHom c x) =
      ccmRationalContinuousTraceNormFieldRightActionAlgHom c
        (ccmRationalNonunitalFieldToPointwiseAlgHom x) := by
  apply ContinuousMap.ext
  intro b
  rw [ccmRationalNonunitalFieldToPointwiseAlgHom_apply,
    ccmRationalContinuousTraceNormIdealFieldUnitizationEvaluation_rightAction]
  rfl

/-- Faithful embedding intertwines class-space action in every cyclic
degree. -/
theorem ccmRationalNonunitalStrongCyclicEmbedding_rightAction
    (c : Section) (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalNonunitalStrongCyclicEmbeddingDegree n
        (ccmRationalNonunitalStrongCyclicRightActionDegree c n x) =
      ccmRationalStrongCyclicRightActionDegree c n
        (ccmRationalNonunitalStrongCyclicEmbeddingDegree n x) := by
  apply Subtype.ext
  change cyclicBarAlgHomDegree
      ccmRationalNonunitalFieldToPointwiseAlgHom n
      (cyclicBarAlgHomDegree
        (ccmRationalNonunitalFieldRightActionAlgHom c) n x.1) =
    cyclicBarAlgHomDegree
      (ccmRationalContinuousTraceNormFieldRightActionAlgHom c) n
      (cyclicBarAlgHomDegree
        ccmRationalNonunitalFieldToPointwiseAlgHom n x.1)
  rw [← cyclicBarAlgHomDegree_comp, ← cyclicBarAlgHomDegree_comp]
  have hAlg :
      ccmRationalNonunitalFieldToPointwiseAlgHom.comp
          (ccmRationalNonunitalFieldRightActionAlgHom c) =
        (ccmRationalContinuousTraceNormFieldRightActionAlgHom c).comp
          ccmRationalNonunitalFieldToPointwiseAlgHom := by
    apply AlgHom.ext
    intro y
    exact ccmRationalNonunitalFieldToPointwiseAlgHom_rightAction c y
  rw [hAlg]

/-- Every degreewise class-space action on literal Definition 4.9 is
continuous. -/
theorem ccmRationalNonunitalStrongCyclicRightActionDegree_continuous
    (c : Section) (n : ℕ) :
    @Continuous
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (ccmRationalNonunitalStrongCyclicRightActionDegree c n) := by
  letI : TopologicalSpace
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalNonunitalStrongCyclicDegreeTopology n
  have htop :
      ccmRationalStrongCyclicTopology.topology (.op (.mk n)) =
        ccmRationalStrongCyclicDegreeTopology n := by
    rfl
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicDegreeTopology n
  rw [continuous_induced_rng]
  have hembed :
      @Continuous
        (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
        (CCMRationalStrongCyclicTarget.simplicial.degree n)
        (ccmRationalNonunitalStrongCyclicDegreeTopology n)
        (ccmRationalStrongCyclicDegreeTopology n)
        (ccmRationalNonunitalStrongCyclicEmbeddingDegree n) := by
    rw [← htop]
    exact continuous_ccmRationalNonunitalStrongCyclicEmbeddingDegree n
  have h :=
    (ccmRationalStrongCyclicRightActionDegree_continuous c n).comp
      hembed
  convert h using 1
  funext x
  exact ccmRationalNonunitalStrongCyclicEmbedding_rightAction c n x

/-- Identity class acts identically on literal nonunital strong chains. -/
theorem ccmRationalNonunitalStrongCyclicRightActionDegree_one
    (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalNonunitalStrongCyclicRightActionDegree 1 n x = x := by
  apply ccmRationalNonunitalStrongCyclicEmbeddingDegree_injective n
  rw [ccmRationalNonunitalStrongCyclicEmbedding_rightAction,
    ccmRationalStrongCyclicRightActionDegree_one]

/-- Product of class-space elements is composition of literal target
actions. -/
theorem ccmRationalNonunitalStrongCyclicRightActionDegree_mul
    (c d : Section) (n : ℕ)
    (x : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    ccmRationalNonunitalStrongCyclicRightActionDegree c n
        (ccmRationalNonunitalStrongCyclicRightActionDegree d n x) =
      ccmRationalNonunitalStrongCyclicRightActionDegree (c * d) n x := by
  apply ccmRationalNonunitalStrongCyclicEmbeddingDegree_injective n
  rw [ccmRationalNonunitalStrongCyclicEmbedding_rightAction,
    ccmRationalNonunitalStrongCyclicEmbedding_rightAction,
    ccmRationalNonunitalStrongCyclicEmbedding_rightAction,
    ccmRationalStrongCyclicRightActionDegree_mul]

end GaloisForLFunctions.RHTower
