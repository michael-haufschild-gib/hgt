/-
The coordinate equation for the quotient Laplacian is adapted from OpenAI's
formalization, Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.GreenIdentityOnTheCubicQuotient
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicVariationalLaplacian

/-!
# Coordinate equations represent the variational quotient Laplacian

The chart Laplacian is the positive hyperbolic differential expression.
A finite smooth partition transports its Green identity globally, including
when the coordinate equation holds only on the test support. Density of
the smooth energy core then identifies its L² realization with the actual
self-adjoint variational Laplacian.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv Manifold
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def kernelCoordinateLaplacian (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j))+
    (p 2:ℂ)*fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector 2)

lemma kernelCoreLift_laplacian (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    upperPositiveLaplacian (kernelCoreLift χ f) p=kernelCoordinateLaplacian f p := by
  have he := kernelCoreLift_eventually_eq χ f p hp
  have hd (j : Fin 3) : (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  have hdd (j : Fin 3) :
      (∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} (kernelCoreLift χ f))) p=
        fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
          (euclideanCoordinateVector j) := by
    change fderiv ℝ (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j)=_
    rw [(hd j).fderiv_eq]
  simp only [upperPositiveLaplacian,kernelCoordinateLaplacian,hdd,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]

lemma kernelDirichletForm_sum_right {ι : Type*} (f : kernelSmoothTests)
    (t : Finset ι) (g : ι→kernelSmoothTests) :
    kernelDirichletForm f (∑i∈t,g i)=∑i∈t,kernelDirichletForm f (g i) := by
  induction t using Finset.induction_on with
  | empty =>
    have hz := kernelDirichletForm_smul_right 0 f (0 : kernelSmoothTests)
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi,kernelDirichletForm_add_right,ih]

lemma kernelTestPartitionTerm_tsupport_right {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport f.1 :=
  tsupport_smul_subset_right _ _

lemma kernelSmoothTest_finite_chart_partition_subsupport (f : kernelSmoothTests) :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 ∧
        tsupport (g i).1⊆tsupport f.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact ⟨(kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i),
    kernelTestPartitionTerm_tsupport_right ρ f i⟩

lemma kernelDirichletForm_supported_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · by_cases hgp : kernelEuclideanProjection p∈tsupport g.1
        · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp) hgp]
          rfl
        · have hz : g.1 (kernelEuclideanProjection p)=0 := image_eq_zero_of_notMem_tsupport hgp
          change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
          rw [hz,mul_zero,zero_div,mul_zero,zero_div]
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

theorem kernelDirichletForm_supported_equation (f g : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition_subsupport g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_supported_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i).1 A hA (fun p hp hgp => heq p hp ((hGsupp i).2 hgp))
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

theorem kernelDirichletForm_coordinate_equation (f : kernelSmoothTests)
    (A : KernelQuotient → ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p, 0 < p 2 → kernelCoordinateLaplacian f p = A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    kernelDirichletForm f g = ∫q, star (A q) * g.1 q ∂integralQuotientVolume globalKubotaKernel :=
  kernelDirichletForm_supported_equation f g A hA (fun p hp _ => heq p hp)

lemma kernelL2_inner_toLp_smooth (A : KernelQuotient→ℂ)
    (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (g : kernelSmoothTests) :
    inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g)=
      ∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  calc
    _ = ∫q,inner ℂ ((hA.toLp A) q) (kernelSmoothTestsToL2 g q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp,(kernelSmoothTests_memLp g).coeFn_toLp] with q hq hg
      change inner ℂ ((hA.toLp A) q) (((kernelSmoothTests_memLp g).toLp g.1) q)=_
      rw [hq,hg,RCLike.inner_apply]
      simp only [RCLike.star_def,mul_comm]

lemma kernelCoordinateLaplacian_form (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient v)=
      inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
  exact kernelEnergyGraphCore_dense.induction_on v
    (isClosed_eq (by fun_prop : Continuous (fun u : KernelEnergyGraph =>
      inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient u)))
      (by fun_prop : Continuous (fun u : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass u))))
    (fun g => by
      rw [kernelEnergyGradient_core,kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
      exact kernelDirichletForm_coordinate_equation f A hA heq g)

theorem kernelEnergyLaplacian_graph_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    (kernelSmoothTestsToL2 f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hu : kernelEnergyGraphCore f=
      kernelVariationalSolution (kernelSmoothTestsToL2 f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [kernelEnergyMass_core,kernelCoordinateLaplacian_form f A hA heq,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [kernelEnergyMass_core] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

lemma kernelEnergyLaplacian_domain_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelSmoothTestsToL2 f∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_graph_of_coordinate f A hA heq)

lemma kernelEnergyLaplacian_apply_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelEnergyLaplacian ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩=
      hA.toLp A :=
  kernelEnergyLaplacian.mem_graph_snd_inj
    (kernelEnergyLaplacian.mem_graph ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩)
    (kernelEnergyLaplacian_graph_of_coordinate f A hA heq) rfl

#print axioms kernelDirichletForm_supported_equation
#print axioms kernelEnergyLaplacian_graph_of_coordinate
#print axioms kernelEnergyLaplacian_apply_of_coordinate
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
