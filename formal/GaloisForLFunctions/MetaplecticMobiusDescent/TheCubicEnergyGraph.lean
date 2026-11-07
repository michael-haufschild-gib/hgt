/-
The completed quotient energy graph is adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicDirichletForm
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The completed cubic quotient energy graph

Smooth gradients are square integrable on the measurable fundamental domain,
with squared norm equal to quotient Dirichlet energy. Complete their graph
with the Hilbert sum norm. Mass and gradient projections are continuous,
and smooth tests have dense graph range and dense mass range.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

abbrev KernelFundamentalVolume : Measure HyperbolicSpace :=
  hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)

abbrev KernelGradientL2 := Lp (EuclideanSpace ℂ (Fin 3)) 2 KernelFundamentalVolume

lemma kernelTestPartial_continuous (f : kernelSmoothTests) (j : Fin 3) :
    Continuous (fun w => kernelTestPartial f w j) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp
      hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelGradientAt_continuous (f : kernelSmoothTests) :
    Continuous (fun w => kernelGradientAt w f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
    (kernelTestPartial_continuous f j)

lemma kernelGradientAt_memLp (f : kernelSmoothTests) :
    MemLp (fun w => kernelGradientAt w f) 2 KernelFundamentalVolume := by
  apply (memLp_two_iff_integrable_sq_norm
    (kernelGradientAt_continuous f).aestronglyMeasurable).mpr
  have hh := (quotient_projection_measurePreserving globalKubotaKernel).integrable_comp_of_integrable
    (kernelQuotientEnergyDensity_integrable f)
  have he : (fun w => kernelQuotientEnergyDensity f (integralOrbitProjection globalKubotaKernel w))=
      kernelTestEnergyDensity f := rfl
  dsimp only [Function.comp_def] at hh
  rw [he] at hh
  simpa only [kernelGradientAt_norm_sq] using hh

def kernelGradientToL2 (f : kernelSmoothTests) : KernelGradientL2 :=
  (kernelGradientAt_memLp f).toLp (fun w => kernelGradientAt w f)

lemma kernelGradientToL2_coe (f : kernelSmoothTests) :
    (kernelGradientToL2 f : HyperbolicSpace → EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelGradientAt w f := (kernelGradientAt_memLp f).coeFn_toLp

lemma kernelGradientToL2_inner (f g : kernelSmoothTests) :
    inner ℂ (kernelGradientToL2 f) (kernelGradientToL2 g)=kernelDirichletForm f g := by
  rw [L2.inner_def,kernelDirichletForm,integralQuotientVolume_integral _ _
    (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f,kernelGradientToL2_coe g] with w hf hg
  rw [hf,hg,kernelDirichletPairDensity_coordinate]

lemma kernelGradientToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelGradientToL2 f‖^2=kernelDirichletEnergy f := by
  have hh := kernelGradientToL2_inner f f
  rw [inner_self_eq_norm_sq_to_K,kernelDirichletForm_self] at hh
  rw [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow] at hh
  exact Complex.ofReal_injective hh

def kernelGradientLinear : kernelSmoothTests →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelGradientToL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (f+g),kernelGradientToL2_coe f,
      kernelGradientToL2_coe g,Lp.coeFn_add (kernelGradientToL2 f) (kernelGradientToL2 g)]
      with w hfg hf hg hadd
    simp only [hfg,hadd,Pi.add_apply,hf,hg,map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (c•f),kernelGradientToL2_coe f,
      Lp.coeFn_smul c (kernelGradientToL2 f)] with w hcf hf hsmul
    simp only [RingHom.id_apply,hcf,hsmul,Pi.smul_apply,hf,map_smul]

/-- Mass and gradient pairs of compactly supported smooth quotient tests. -/
def kernelInitialGradientGraph : Submodule ℂ (KernelQuotientL2 × KernelGradientL2) :=
  LinearMap.range (kernelSmoothTestsToL2.prod kernelGradientLinear)

lemma kernelInitialGradientGraph_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradientGraph) (hz : x.1=0) : x.2=0 := by
  obtain ⟨f,hf⟩ := hx
  have hf1 : kernelSmoothTestsToL2 f=x.1 := congrArg Prod.fst hf
  have hf2 : kernelGradientLinear f=x.2 := congrArg Prod.snd hf
  have hzero : f=0 := kernelSmoothTestsToL2_injective (by
    simpa only [map_zero] using hf1.trans hz)
  rw [hzero,map_zero] at hf2
  exact hf2.symm

def kernelInitialGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 :=
  kernelInitialGradientGraph.toLinearPMap

lemma kernelInitialGradient_graph :
    kernelInitialGradient.graph=kernelInitialGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelInitialGradientGraph_unique

lemma kernelInitialGradient_dense_domain :
    Dense (kernelInitialGradient.domain : Set KernelQuotientL2) := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [kernelInitialGradient_graph]
  exact ⟨f,rfl⟩

abbrev KernelEnergyAmbient := WithLp 2 (KernelQuotientL2 × KernelGradientL2)

def kernelEnergyCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyAmbient :=
  (WithLp.linearEquiv 2 ℂ (KernelQuotientL2 × KernelGradientL2)).symm.toLinearMap.comp
    (kernelSmoothTestsToL2.prod kernelGradientLinear)

/-- Hilbert closure of the actual smooth mass-gradient pairs. -/
def kernelEnergyGraphSubmodule : Submodule ℂ KernelEnergyAmbient :=
  (LinearMap.range kernelEnergyCore).topologicalClosure

abbrev KernelEnergyGraph := kernelEnergyGraphSubmodule

instance kernelEnergyGraph_complete : CompleteSpace KernelEnergyGraph :=
  (LinearMap.range kernelEnergyCore).isClosed_topologicalClosure.completeSpace_coe


def kernelEnergyGraphCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyGraph :=
  kernelEnergyCore.codRestrict kernelEnergyGraphSubmodule
    (fun f => (LinearMap.range kernelEnergyCore).le_topologicalClosure ⟨f,rfl⟩)

lemma kernelEnergyGraphCore_dense : DenseRange kernelEnergyGraphCore := by
  rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
  change closure (Set.range kernelEnergyCore)⊆closure (Set.range kernelEnergyCore)
  rfl

def kernelEnergyMass : KernelEnergyGraph →L[ℂ] KernelQuotientL2 :=
  (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

def kernelEnergyGradient : KernelEnergyGraph →L[ℂ] KernelGradientL2 :=
  (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

lemma kernelEnergyMass_core (f : kernelSmoothTests) :
    kernelEnergyMass (kernelEnergyGraphCore f)=kernelSmoothTestsToL2 f := rfl

lemma kernelEnergyGradient_core (f : kernelSmoothTests) :
    kernelEnergyGradient (kernelEnergyGraphCore f)=kernelGradientToL2 f := rfl

lemma kernelEnergyGraph_norm_sq (u : KernelEnergyGraph) :
    ‖u‖^2=‖kernelEnergyMass u‖^2+‖kernelEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

lemma kernelEnergyGraphCore_norm_sq (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore f‖^2=‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f := by
  rw [kernelEnergyGraph_norm_sq,kernelEnergyMass_core,kernelEnergyGradient_core,
    kernelGradientToL2_norm_sq]

lemma kernelEnergyMass_dense : DenseRange kernelEnergyMass := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  exact ⟨kernelEnergyGraphCore f,rfl⟩


#print axioms kernelGradientToL2_norm_sq
#print axioms kernelEnergyGraph_complete
#print axioms kernelEnergyGraphCore_dense
#print axioms kernelEnergyGraphCore_norm_sq
#print axioms kernelEnergyMass_dense
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
