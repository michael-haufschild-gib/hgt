import GaloisForLFunctions.RHTower.CCMRationalAdelicClassSpaceCyclicContinuity
import GaloisForLFunctions.RHTower.ClosedCyclicModuleCokernel

/-!
# Closed coefficientwise-projective CCM relative cyclic module

Continuity of the face and degeneracy generators propagates, by the exact generator-relation
presentation of the simplex category, to every simplicial map.  This packages the natural
coefficientwise projective topology on the full adelic class-space cyclic module and forms the
degreewise quotient by closure of the exact reduced-source range.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Sections := CCMRationalAdelicMoritaClassSpaceAlgebra

@[reducible]
def ccmRationalAdelicClassSpaceObjectTopology :
    ∀ a : SimplexCategoryGenRel,
      TopologicalSpace
        (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj (.op a)) :=
  SimplexCategoryGenRel.rec fun n =>
    ccmRationalAdelicClassSpaceProjectiveTopology n

theorem continuous_ccmRationalAdelicClassSpaceSimplicialUnop {a b : SimplexCategoryGenRel}
    (g : a ⟶ b) :
    @Continuous
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj (.op b))
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj (.op a))
      (ccmRationalAdelicClassSpaceObjectTopology b) (ccmRationalAdelicClassSpaceObjectTopology a)
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.map g.op) := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b g =>
    @Continuous
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj (.op b))
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj (.op a))
      (ccmRationalAdelicClassSpaceObjectTopology b) (ccmRationalAdelicClassSpaceObjectTopology a)
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.map g.op)
  apply SimplexCategoryGenRel.hom_induction P
  · intro n
    dsimp [P]
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections n) :=
      ccmRationalAdelicClassSpaceProjectiveTopology n
    have hmap := CCMRationalAdelicClassSpaceCyclicModule.simplicial.map_id
      (Opposite.op (SimplexCategoryGenRel.mk n))
    rw [hmap]
    exact continuous_id
  · intro n m u i hu
    dsimp [P] at hu ⊢
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections n) :=
      ccmRationalAdelicClassSpaceProjectiveTopology n
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections m) :=
      ccmRationalAdelicClassSpaceProjectiveTopology m
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections (m + 1)) :=
      ccmRationalAdelicClassSpaceProjectiveTopology (m + 1)
    rw [Functor.map_comp]
    exact hu.comp (continuous_ccmRationalAdelicClassSpaceFace i)
  · intro n m u i hu
    dsimp [P] at hu ⊢
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections n) :=
      ccmRationalAdelicClassSpaceProjectiveTopology n
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections m) :=
      ccmRationalAdelicClassSpaceProjectiveTopology m
    letI : TopologicalSpace (CyclicBarTensor ℂ Sections (m + 1)) :=
      ccmRationalAdelicClassSpaceProjectiveTopology (m + 1)
    rw [Functor.map_comp]
    exact hu.comp (continuous_ccmRationalAdelicClassSpaceDegeneracy i)

theorem continuous_ccmRationalAdelicClassSpaceSimplicial {j k : SimplexCategoryGenRelᵒᵖ}
    (g : j ⟶ k) :
    @Continuous
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj j)
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.obj k)
      (ccmRationalAdelicClassSpaceObjectTopology j.unop) (ccmRationalAdelicClassSpaceObjectTopology k.unop)
      (CCMRationalAdelicClassSpaceCyclicModule.simplicial.map g) :=
  continuous_ccmRationalAdelicClassSpaceSimplicialUnop g.unop

def ccmRationalAdelicClassSpaceProjectiveCyclicTopology :
    GaloisForLFunctions.RHTower.CyclicModule.Topology
      CCMRationalAdelicClassSpaceCyclicModule where
  topology := fun (j : SimplexCategoryGenRelᵒᵖ) =>
    ccmRationalAdelicClassSpaceObjectTopology j.unop
  continuousAdd j := by
    rcases j with ⟨⟨n⟩⟩
    exact ccmRationalAdelicClassSpaceProjectiveContinuousAdd n
  continuousSMul j := by
    rcases j with ⟨⟨n⟩⟩
    exact ccmRationalAdelicClassSpaceProjectiveContinuousSMul n
  simplicial_continuous g := continuous_ccmRationalAdelicClassSpaceSimplicial g
  cyclic_continuous n := continuous_ccmRationalAdelicClassSpaceRotate n

def CCMRationalAdelicClosedRelativeCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicReducedClassSpaceCyclicHom.closedCokernel
    ccmRationalAdelicClassSpaceProjectiveCyclicTopology

def ccmRationalAdelicClosedRelativeCyclicProjection :
    CCMRationalAdelicClassSpaceCyclicModule.simplicial ⟶
      CCMRationalAdelicClosedRelativeCyclicModule.simplicial :=
  ccmRationalAdelicReducedClassSpaceCyclicHom.closedCokernelProjection
    ccmRationalAdelicClassSpaceProjectiveCyclicTopology

end GaloisForLFunctions.RHTower
