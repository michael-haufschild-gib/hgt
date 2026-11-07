/-
The quotient variational Laplacian is adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicGradientIsClosable
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The self-adjoint nonnegative cubic quotient Laplacian

The adjoint of the energy-space mass embedding solves the coercive weak
problem. Its mass projection is a positive self-adjoint injective resolvent
with dense range. Inverting this resolvent on its range defines the closed,
densely defined, nonnegative self-adjoint quotient Laplacian.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma kernelEnergyGraph_inner (u v : KernelEnergyGraph) :
    inner ℂ u v=inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v) := rfl

lemma kernelEnergyMass_norm_le (u : KernelEnergyGraph) : ‖kernelEnergyMass u‖≤‖u‖ := by
  have hh := kernelEnergyGraph_norm_sq u
  nlinarith only [hh, sq_nonneg ‖kernelEnergyGradient u‖,norm_nonneg (kernelEnergyMass u),norm_nonneg u]

lemma kernelEnergyMass_opNorm_le : ‖kernelEnergyMass‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using kernelEnergyMass_norm_le)

def kernelVariationalSolution : KernelQuotientL2 →L[ℂ] KernelEnergyGraph :=
  kernelEnergyMass.adjoint

lemma kernelVariationalSolution_equation (F : KernelQuotientL2) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyMass (kernelVariationalSolution F)) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution F)) (kernelEnergyGradient v)=
        inner ℂ F (kernelEnergyMass v) := by
  rw [←kernelEnergyGraph_inner]
  exact kernelEnergyMass.adjoint_inner_left v F

lemma kernelVariationalSolution_unique (F : KernelQuotientL2) (u : KernelEnergyGraph)
    (hu : ∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v)) :
    u=kernelVariationalSolution F := by
  apply ext_inner_right ℂ
  intro v
  rw [kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  exact (hu v).trans (kernelVariationalSolution_equation F v).symm

theorem kernelVariationalSolution_existsUnique (F : KernelQuotientL2) :
    ∃!u : KernelEnergyGraph,∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v) :=
  ⟨kernelVariationalSolution F,kernelVariationalSolution_equation F,
    fun u hu => kernelVariationalSolution_unique F u hu⟩

lemma kernelVariationalSolution_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalSolution F‖≤‖F‖ := by
  have hnorm : ‖kernelVariationalSolution‖=‖kernelEnergyMass‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    ‖kernelVariationalSolution F‖≤‖kernelVariationalSolution‖*‖F‖ :=
      kernelVariationalSolution.le_opNorm F
    _ ≤1*‖F‖ := mul_le_mul_of_nonneg_right (hnorm ▸ kernelEnergyMass_opNorm_le) (norm_nonneg F)
    _ = _ := one_mul _

def kernelVariationalResolvent : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  kernelEnergyMass.comp kernelVariationalSolution

lemma kernelVariationalResolvent_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalResolvent F‖≤‖F‖ :=
  (kernelEnergyMass_norm_le _).trans (kernelVariationalSolution_norm_le F)

private lemma selfAdjoint_comp_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.comp A.adjoint) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelVariationalResolvent_selfAdjoint : IsSelfAdjoint kernelVariationalResolvent :=
  selfAdjoint_comp_adjoint kernelEnergyMass

lemma kernelVariationalResolvent_positive (F : KernelQuotientL2) :
    0≤(inner ℂ F (kernelVariationalResolvent F)).re := by
  change 0≤(inner ℂ F (kernelEnergyMass (kernelEnergyMass.adjoint F))).re
  rw [←kernelEnergyMass.adjoint_inner_left]
  exact inner_self_nonneg (𝕜 := ℂ) (x := kernelEnergyMass.adjoint F)

lemma kernelVariationalResolvent_injective : Function.Injective kernelVariationalResolvent := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  change kernelEnergyMass (kernelVariationalSolution F)=0 at hF
  have hu : kernelVariationalSolution F=0 := kernelEnergyMass_injective (by
    rw [map_zero]
    exact hF)
  have he : (fun g : KernelQuotientL2 => inner ℂ F g)=(fun _ => (0 : ℂ)) :=
    kernelEnergyMass_dense.equalizer (by fun_prop) continuous_const (by
      funext v
      change inner ℂ F (kernelEnergyMass v)=0
      rw [←kernelEnergyMass.adjoint_inner_left]
      change inner ℂ (kernelVariationalSolution F) v=0
      rw [hu,inner_zero_left])
  exact inner_self_eq_zero.mp (congrFun he F)

lemma kernelVariationalResolvent_dense : DenseRange kernelVariationalResolvent := by
  change Dense (kernelVariationalResolvent.range : Set KernelQuotientL2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hh := kernelVariationalResolvent.orthogonal_ker
  rw [LinearMap.ker_eq_bot.mpr kernelVariationalResolvent_injective,Submodule.bot_orthogonal_eq_top,
    kernelVariationalResolvent_selfAdjoint.adjoint_eq] at hh
  exact hh.symm
def kernelLaplacianEquation : (KernelQuotientL2 × KernelQuotientL2) →L[ℂ] KernelQuotientL2 :=
  kernelVariationalResolvent.comp ((ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)+
    (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelQuotientL2))-
      (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)

def kernelLaplacianGraph : Submodule ℂ (KernelQuotientL2 × KernelQuotientL2) :=
  kernelLaplacianEquation.ker

lemma mem_kernelLaplacianGraph (u f : KernelQuotientL2) :
    (u,f)∈kernelLaplacianGraph ↔ kernelVariationalResolvent (u+f)=u := by
  change kernelVariationalResolvent (u+f)-u=0 ↔ _
  exact sub_eq_zero

lemma kernelLaplacianGraph_unique (x : KernelQuotientL2 × KernelQuotientL2)
    (hx : x∈kernelLaplacianGraph) (hz : x.1=0) : x.2=0 := by
  have hh := (mem_kernelLaplacianGraph x.1 x.2).mp hx
  rw [hz,zero_add] at hh
  apply kernelVariationalResolvent_injective
  rw [map_zero]
  exact hh

def kernelEnergyLaplacian : KernelQuotientL2 →ₗ.[ℂ] KernelQuotientL2 :=
  kernelLaplacianGraph.toLinearPMap

lemma kernelEnergyLaplacian_graph : kernelEnergyLaplacian.graph=kernelLaplacianGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelLaplacianGraph_unique

lemma kernelEnergyLaplacian_closed : kernelEnergyLaplacian.IsClosed := by
  rw [LinearPMap.IsClosed,kernelEnergyLaplacian_graph]
  exact kernelLaplacianEquation.isClosed_ker

lemma kernelEnergyLaplacian_resolvent_graph (F : KernelQuotientL2) :
    (kernelVariationalResolvent F,F-kernelVariationalResolvent F)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  congr 1
  abel

lemma kernelEnergyLaplacian_resolvent_domain (F : KernelQuotientL2) :
    kernelVariationalResolvent F∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_resolvent_graph F)

lemma kernelEnergyLaplacian_resolvent_apply (F : KernelQuotientL2) :
    kernelEnergyLaplacian ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩=
      F-kernelVariationalResolvent F :=
  kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph _)
    (kernelEnergyLaplacian_resolvent_graph F) rfl

lemma kernelEnergyLaplacian_dense_domain :
    Dense (kernelEnergyLaplacian.domain : Set KernelQuotientL2) := by
  apply kernelVariationalResolvent_dense.mono
  rintro _ ⟨F,rfl⟩
  exact kernelEnergyLaplacian_resolvent_domain F

lemma kernelEnergyLaplacian_resolvent_relation (u : kernelEnergyLaplacian.domain) :
    kernelVariationalResolvent (kernelEnergyLaplacian u+u)=u := by
  have hh := kernelEnergyLaplacian.mem_graph u
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hh
  simpa only [add_comm] using hh

lemma kernelEnergyLaplacian_isFormalAdjoint :
    kernelEnergyLaplacian.IsFormalAdjoint kernelEnergyLaplacian := by
  intro u v
  have hh := kernelVariationalResolvent_selfAdjoint.isSymmetric
    (kernelEnergyLaplacian u+u) (kernelEnergyLaplacian v+v)
  simp only [ContinuousLinearMap.coe_coe] at hh
  rw [kernelEnergyLaplacian_resolvent_relation,kernelEnergyLaplacian_resolvent_relation] at hh
  simp only [inner_add_left,inner_add_right] at hh
  exact add_right_cancel hh.symm

lemma kernelEnergyLaplacian_form (u : kernelEnergyLaplacian.domain) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyLaplacian u) (kernelEnergyMass v)=
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
        (kernelEnergyGradient v) := by
  have hh := kernelVariationalSolution_equation (kernelEnergyLaplacian u+u) v
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he,inner_add_left] at hh
  exact (add_left_cancel (hh.trans (add_comm _ _))).symm

lemma kernelEnergyLaplacian_nonnegative (u : kernelEnergyLaplacian.domain) :
    0≤(inner ℂ (kernelEnergyLaplacian u) (u : KernelQuotientL2)).re := by
  have hh := kernelEnergyLaplacian_form u
    (kernelVariationalSolution (kernelEnergyLaplacian u+u))
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he] at hh
  rw [hh]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem kernelEnergyLaplacian_selfAdjoint : IsSelfAdjoint kernelEnergyLaplacian := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro x hx
    obtain ⟨u,hu,hv⟩ := (kernelEnergyLaplacian.adjoint.mem_graph_iff).mp hx
    change (x.1,x.2)∈kernelEnergyLaplacian.graph
    rw [←hu,←hv,kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
    apply ext_inner_right ℂ
    intro F
    have ha := LinearPMap.adjoint_isFormalAdjoint kernelEnergyLaplacian_dense_domain u
      ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩
    rw [kernelEnergyLaplacian_resolvent_apply] at ha
    have hs := kernelVariationalResolvent_selfAdjoint.isSymmetric
      ((u : KernelQuotientL2)+kernelEnergyLaplacian.adjoint u) F
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs,inner_add_left,ha,inner_sub_right]
    abel
  · exact LinearPMap.IsFormalAdjoint.le_adjoint kernelEnergyLaplacian_dense_domain
      kernelEnergyLaplacian_isFormalAdjoint

#print axioms kernelVariationalSolution_existsUnique
#print axioms kernelVariationalResolvent_injective
#print axioms kernelEnergyLaplacian_closed
#print axioms kernelEnergyLaplacian_dense_domain
#print axioms kernelEnergyLaplacian_nonnegative
#print axioms kernelEnergyLaplacian_selfAdjoint
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
