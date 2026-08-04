import GaloisForLFunctions.RHTower.CCMRationalNonunitalStrongCyclicEmbedding

/-!
# Natural topology on the literal nonunital CCM strong cyclic target

The globally unitized ideal-field cyclic module carries the topology induced
by its faithful cyclic embedding into continuous pointwise-unitized fields
with the verified projective/LF graph topology.  Faithfulness in every cyclic
degree is proved in the imported module, so this is a genuine subspace
topology, not a quotient or diagonal-only topology.

Cyclic naturality of the embedding transports continuity of every simplex
operator and Connes rotation without replaying the projective tensor
estimates.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

/-- Faithful subspace topology on one literal nonunital strong cyclic
degree. -/
@[reducible]
def ccmRationalNonunitalStrongCyclicDegreeTopology (n : ℕ) :
    TopologicalSpace
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :=
  TopologicalSpace.induced
    (ccmRationalNonunitalStrongCyclicEmbeddingDegree n)
    (ccmRationalStrongCyclicTopology.topology (.op (.mk n)))

theorem ccmRationalNonunitalStrongCyclicDegreeContinuousAdd (n : ℕ) :
    @ContinuousAdd
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n) inferInstance := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicTopology.topology (.op (.mk n))
  letI : ContinuousAdd
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicTopology.continuousAdd (.op (.mk n))
  exact continuousAdd_induced
    (ccmRationalNonunitalStrongCyclicEmbeddingDegree n)

theorem ccmRationalNonunitalStrongCyclicDegreeContinuousSMul (n : ℕ) :
    @ContinuousSMul ℂ
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      inferInstance inferInstance
      (ccmRationalNonunitalStrongCyclicDegreeTopology n) := by
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicTopology.topology (.op (.mk n))
  letI : ContinuousSMul ℂ
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicTopology.continuousSMul (.op (.mk n))
  exact continuousSMul_induced
    (ccmRationalNonunitalStrongCyclicEmbeddingDegree n)

theorem continuous_ccmRationalNonunitalStrongCyclicEmbeddingDegree
    (n : ℕ) :
    @Continuous
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (ccmRationalStrongCyclicTopology.topology (.op (.mk n)))
      (ccmRationalNonunitalStrongCyclicEmbeddingDegree n) :=
  continuous_induced_dom

@[reducible]
def ccmRationalNonunitalStrongCyclicObjectTopology :
    ∀ j : SimplexCategoryGenRelᵒᵖ,
      TopologicalSpace
        (CCMRationalNonunitalStrongCyclicTarget.simplicial.obj j) :=
  fun j => TopologicalSpace.induced
    (ccmRationalNonunitalStrongCyclicEmbedding.simplicial.app j)
    (ccmRationalStrongCyclicTopology.topology j)

theorem continuous_ccmRationalNonunitalStrongCyclicSimplicial
    {j k : SimplexCategoryGenRelᵒᵖ} (g : j ⟶ k) :
    @Continuous
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.obj j)
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.obj k)
      (ccmRationalNonunitalStrongCyclicObjectTopology j)
      (ccmRationalNonunitalStrongCyclicObjectTopology k)
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.map g) := by
  letI : TopologicalSpace
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.obj j) :=
    ccmRationalNonunitalStrongCyclicObjectTopology j
  letI : TopologicalSpace
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.obj k) :=
    ccmRationalNonunitalStrongCyclicObjectTopology k
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.obj j) :=
    ccmRationalStrongCyclicTopology.topology j
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.obj k) :=
    ccmRationalStrongCyclicTopology.topology k
  rw [continuous_induced_rng]
  have hembed :
      @Continuous
        (CCMRationalNonunitalStrongCyclicTarget.simplicial.obj j)
        (CCMRationalStrongCyclicTarget.simplicial.obj j)
        (ccmRationalNonunitalStrongCyclicObjectTopology j)
        (ccmRationalStrongCyclicTopology.topology j)
        (ccmRationalNonunitalStrongCyclicEmbedding.simplicial.app j).hom :=
    continuous_induced_dom
  have h :=
    (ccmRationalStrongCyclicTopology.simplicial_continuous g).comp
      hembed
  convert h using 1
  funext x
  have hnat :=
    ccmRationalNonunitalStrongCyclicEmbedding.simplicial.naturality g
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat) x

theorem continuous_ccmRationalNonunitalStrongCyclicRotate (n : ℕ) :
    @Continuous
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (ccmRationalNonunitalStrongCyclicDegreeTopology n)
      (CCMRationalNonunitalStrongCyclicTarget.cyclic n) := by
  letI : TopologicalSpace
      (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalNonunitalStrongCyclicDegreeTopology n
  letI : TopologicalSpace
      (CCMRationalStrongCyclicTarget.simplicial.degree n) :=
    ccmRationalStrongCyclicTopology.topology (.op (.mk n))
  rw [continuous_induced_rng]
  have hembed :
      @Continuous
        (CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n)
        (CCMRationalStrongCyclicTarget.simplicial.degree n)
        (ccmRationalNonunitalStrongCyclicDegreeTopology n)
        (ccmRationalStrongCyclicTopology.topology (.op (.mk n)))
        (ccmRationalNonunitalStrongCyclicEmbeddingDegree n) :=
    continuous_induced_dom
  have h :=
    (ccmRationalStrongCyclicTopology.cyclic_continuous n).comp
      hembed
  convert h using 1
  funext x
  have hnat :=
    ccmRationalNonunitalStrongCyclicEmbedding.cyclic_naturality n
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat) x

/-- Compatible faithful projective/LF topology on literal CCM Definition
4.9. -/
def ccmRationalNonunitalStrongCyclicTopology :
    CyclicModule.Topology CCMRationalNonunitalStrongCyclicTarget where
  topology := fun j =>
    ccmRationalNonunitalStrongCyclicObjectTopology j
  continuousAdd j := by
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.obj j) :=
      ccmRationalStrongCyclicTopology.topology j
    letI : ContinuousAdd
        (CCMRationalStrongCyclicTarget.simplicial.obj j) :=
      ccmRationalStrongCyclicTopology.continuousAdd j
    exact continuousAdd_induced
      (ccmRationalNonunitalStrongCyclicEmbedding.simplicial.app j).hom
  continuousSMul j := by
    letI : TopologicalSpace
        (CCMRationalStrongCyclicTarget.simplicial.obj j) :=
      ccmRationalStrongCyclicTopology.topology j
    letI : ContinuousSMul ℂ
        (CCMRationalStrongCyclicTarget.simplicial.obj j) :=
      ccmRationalStrongCyclicTopology.continuousSMul j
    exact continuousSMul_induced
      (ccmRationalNonunitalStrongCyclicEmbedding.simplicial.app j).hom
  simplicial_continuous g :=
    continuous_ccmRationalNonunitalStrongCyclicSimplicial g
  cyclic_continuous n :=
    continuous_ccmRationalNonunitalStrongCyclicRotate n

end GaloisForLFunctions.RHTower
