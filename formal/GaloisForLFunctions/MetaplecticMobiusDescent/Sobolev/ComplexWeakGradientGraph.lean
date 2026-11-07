/-
Complex weak-gradient graph adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicVolumeIsInvariant
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The complex Euclidean weak-gradient Hilbert space

The distributional gradient equations define a closed subspace of
`L² × L²(ℂ³)`. Injectivity of the map from `L²` to distributions makes
its mass projection injective. Schwartz functions give a dense mass range.
-/

noncomputable section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)
abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2

lemma euclideanL2Distribution_injective : Function.Injective euclideanL2Distribution := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

/-- Distributional differentiation minus the proposed gradient coordinates. -/
def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

/-- The closed graph cut out by all three distributional gradient equations. -/
def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker

lemma mem_euclideanWeakGradientGraph (f : EuclideanL2) (g : EuclideanGradientL2) :
    (f,g)∈euclideanWeakGradientGraph ↔ ∀j,
      ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)=euclideanL2Distribution (g j) := by
  change (fun j => ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)-
    euclideanL2Distribution (g j))=0 ↔ _
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

/-- A zero mass component has zero weak gradient, by distributional injectivity. -/
lemma euclideanWeakGradientGraph_unique (x : EuclideanL2 × EuclideanGradientL2)
    (hx : x∈euclideanWeakGradientGraph) (hzero : x.1=0) : x.2=0 := by
  have hh := (mem_euclideanWeakGradientGraph x.1 x.2).mp hx
  apply (WithLp.equiv 2 (Fin 3 → EuclideanL2)).injective
  funext j
  change x.2 j=(0:EuclideanL2)
  apply euclideanL2Distribution_injective
  simpa only [hzero,map_zero,lineDerivOp_zero,WithLp.ofLp_zero,Pi.zero_apply] using (hh j).symm

def euclideanWeakGradient : EuclideanL2 →ₗ.[ℂ] EuclideanGradientL2 :=
  euclideanWeakGradientGraph.toLinearPMap

lemma euclideanWeakGradient_graph : euclideanWeakGradient.graph=euclideanWeakGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ euclideanWeakGradientGraph_unique

theorem euclideanWeakGradient_closed : euclideanWeakGradient.IsClosed := by
  rw [LinearPMap.IsClosed,euclideanWeakGradient_graph]
  exact euclideanGradientEquations.isClosed_ker

lemma schwartz_mem_euclideanWeakGradientGraph (f : 𝓢(EuclideanSpatial,ℂ)) :
    (f.toLp 2 volume,WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} f).toLp 2 volume))∈euclideanWeakGradientGraph := by
  apply (mem_euclideanWeakGradientGraph _ _).mpr
  intro j
  dsimp only [euclideanL2Distribution]
  simp only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq («μ» := volume) f _

theorem euclideanWeakGradient_dense_domain : Dense (euclideanWeakGradient.domain : Set EuclideanL2) := by
  apply (SchwartzMap.denseRange_toLpCLM (E := EuclideanSpatial) (F := ℂ) (p := 2)
    («μ» := volume) (by norm_num)).mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [euclideanWeakGradient_graph]
  exact schwartz_mem_euclideanWeakGradientGraph f


abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

/-- The weak-gradient graph with the Hilbert sum norm. -/
def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe

def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

lemma euclideanH1Embedding_eq_zero (u : EuclideanH1) (hu : euclideanH1Embedding u=0) : u=0 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (EuclideanL2 × EuclideanGradientL2)).injective
  apply Prod.ext
  · exact hu
  · exact euclideanWeakGradientGraph_unique u.1.ofLp u.2 hu

lemma euclideanH1Embedding_injective : Function.Injective euclideanH1Embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply euclideanH1Embedding_eq_zero
  rw [map_sub,huv,sub_self]

lemma euclideanH1Embedding_dense : DenseRange euclideanH1Embedding := by
  apply euclideanWeakGradient_dense_domain.mono
  intro f hf
  obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
  rw [euclideanWeakGradient_graph] at hg
  refine ⟨⟨WithLp.toLp 2 (f,g),hg⟩,?_⟩
  rfl

lemma euclideanH1_norm_sq (u : EuclideanH1) :
    ‖u‖^2=‖euclideanH1Embedding u‖^2+‖euclideanH1Gradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

#print axioms euclideanWeakGradient_closed
#print axioms euclideanH1Embedding_injective
#print axioms euclideanH1Embedding_dense
#print axioms euclideanH1_norm_sq
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
