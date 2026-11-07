/-
The cutoff cover is adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.SmoothCutoffsOnTheCubicQuotient
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.EuclideanRellich

/-!
# Compact cutoff charts on the actual cubic quotient

The regions where a cutoff exceeds one half form an open cover. Every
compact quotient set admits a finite subcover. Each cutoff support is an
injective measure chart and has a compact Euclidean energy projection.
-/

noncomputable section
open MeasureTheory
open scoped Classical Topology ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def kernelChartCore (χ : PositiveChartCutoff) : Set EuclideanSpatial :=
  {p | (1/2 : ℝ)<χ.func p}

def kernelChartCoreImage (χ : PositiveChartCutoff) : Set KernelQuotient :=
  kernelEuclideanProjection '' kernelChartCore χ

lemma kernelChartCore_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCore χ) :=
  isOpen_lt continuous_const χ.smooth.continuous

lemma kernelChartCore_subset (χ : PositiveChartCutoff) : kernelChartCore χ⊆tsupport χ.func := by
  intro p hp
  apply subset_tsupport
  change χ.func p≠0
  have hh : (1/2 : ℝ)<χ.func p := hp
  linarith only [hh]

lemma kernelChartCoreImage_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCoreImage χ) := by
  have hp : kernelChartCore χ⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have he : kernelChartCoreImage χ=integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' kernelChartCore χ) := by
    rw [←euclideanToHyperbolic_image_positive _ hp,Set.image_image]
    rfl
  rw [he]
  exact (integralOrbitProjection_openQuotient globalKubotaKernel
    globalKubotaKernel_le_levelThree).isOpenMap _
      ((kernelChartCore_open χ).preimage hyperbolicEuclideanCoordinates_continuous)

abbrev KernelGoodCutoff := {χ : PositiveChartCutoff //
  Set.InjOn kernelEuclideanProjection (tsupport χ.func)}

lemma kernelChartCoreImage_cover : (Set.univ : Set KernelQuotient)⊆
    ⋃χ : KernelGoodCutoff,kernelChartCoreImage χ.1 := by
  intro q _
  obtain ⟨p,χ,hq,hχ,_,hinj,_⟩ := kernelQuotient_chartCutoff_exists q
  refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,p,?_,hq⟩
  change (1/2 : ℝ)<χ.func p
  rw [hχ]
  norm_num

lemma kernelCompact_finite_chart_cover (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,K⊆⋃χ∈t,kernelChartCoreImage χ.1 :=
  hK.elim_finite_subcover (fun χ : KernelGoodCutoff=>kernelChartCoreImage χ.1)
    (fun χ=>kernelChartCoreImage_open χ.1)
    ((Set.subset_univ K).trans kernelChartCoreImage_cover)

private lemma kernelCutoff_borel (χ : PositiveChartCutoff) :
    @MeasurableSet EuclideanSpatial (borel EuclideanSpatial) (tsupport χ.func) := by
  letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
  letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
  exact (isClosed_tsupport χ.func).measurableSet

/-- Every actual cutoff support has compact Euclidean energy restriction. -/
theorem kernelCutoff_rellich (χ : PositiveChartCutoff) :
    IsCompactOperator (EuclideanSobolev.h1OnToL2 (tsupport χ.func)
      (kernelCutoff_borel χ)) :=
  EuclideanSobolev.isCompactOperator_h1OnToL2 (tsupport χ.func) χ.compact
    (kernelCutoff_borel χ)

/-- Compact quotient sets admit finitely many measure charts with compact local energy projections. -/
theorem kernelCompact_finite_compactCharts (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,
      (K⊆⋃χ∈t,kernelChartCoreImage χ.1) ∧
      ∀χ∈t,
        IsCompactOperator (EuclideanSobolev.h1OnToL2 (tsupport χ.1.func)
          (kernelCutoff_borel χ.1)) ∧
        MeasurePreserving kernelEuclideanProjection
          (hyperbolicEuclideanVolume.restrict (tsupport χ.1.func))
          ((integralQuotientVolume globalKubotaKernel).restrict
            (kernelEuclideanProjection '' tsupport χ.1.func)) := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover K hK
  refine ⟨t,ht,?_⟩
  intro χ _
  exact ⟨kernelCutoff_rellich χ.1,kernelEuclideanProjection_measurePreserving_on _
    (isClosed_tsupport χ.1.func).measurableSet χ.1.positive χ.2⟩

#print axioms kernelCompact_finite_compactCharts
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
