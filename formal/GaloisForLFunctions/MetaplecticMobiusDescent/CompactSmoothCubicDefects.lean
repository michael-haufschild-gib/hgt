/-
Compact smooth incoming defects adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCompactHeightProfiles

/-!
# Compact smooth forcing on the cubic quotient

The incoming defect vanishes in every sufficiently high integral cusp.
Bianchi reduction makes its quotient support compact. Its coordinate
smoothness descends through the actual quotient atlas, giving a smooth
compact test whose L² class is the entire incoming forcing family.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma smoothCuspSeedDefect_high_zero (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hvlarge : max b a⁻¹<v) :
    smoothCuspSeedDefect a b s (integralComplexMatrix M • upperPoint z v hv)=0 := by
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  have hz : (fun r : CuspCosets => cuspCutoffTerm 1 (cuspSeedDefectProfile a b s) r
      (integralComplexMatrix M • upperPoint z v hv))=(fun _ => (0:ℂ)) := by
    funext r
    have hout : cosetHeight r (integralComplexMatrix M • upperPoint z v hv)<a ∨
        b<cosetHeight r (integralComplexMatrix M • upperPoint z v hv) := by
      induction r using Quotient.inductionOn with
      | _ N =>
        change cosetHeight (cosetOf N) _<a ∨ b<cosetHeight (cosetOf N) _
        rw [cosetHeight_cosetOf]
        change hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
          (integralComplexMatrix M • upperPoint z v hv))<a ∨
          b<hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
            (integralComplexMatrix M • upperPoint z v hv))
        simp only [←mul_smul,←map_mul]
        by_cases hc : ((N:SL(2,O))*M) 1 0=0
        · right
          rw [integral_upper_triangular_height _ hc]
          exact (le_max_left _ _).trans_lt hvlarge
        · left
          have hh := integral_hyperbolicHeight_mul_le_one ((N:SL(2,O))*M) hc (upperPoint z v hv)
          rw [hyperbolicHeight_upperPoint] at hh
          have hav : 1<a*v := by
            have hlt : a⁻¹<v := (le_max_right _ _).trans_lt hvlarge
            have hm := mul_lt_mul_of_pos_left hlt ha
            simpa only [mul_inv_cancel₀ ha.ne'] using hm
          by_contra hn
          have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hv.le
          nlinarith only [hh,hav,hmul]
    simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
  rw [hz,tsum_zero]

theorem kernelQuotientDefect_hasCompactSupport (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    HasCompactSupport (kernelQuotientDefect a b s) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max b a⁻¹)
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max b a⁻¹) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max b a⁻¹) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (smoothCuspSeedDefect_high_zero a b ha hab s r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

lemma actual_smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (smoothCuspSeedDefectField a b s) p := by
  have heq : smoothCuspSeedDefectField a b s =ᶠ[𝓝 p]
      heightPoincareField (cuspSeedDefectProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedDefectField_eq a b s ha hab q hq
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

lemma kernelQuotientDefect_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    {p : SpatialCoordinates} (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientDefect a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedDefectField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p
  rw [smoothCuspSeedDefectField,dif_pos (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernel_contMDiff_of_spatial (f : KernelQuotient→ℂ) (F : SpatialCoordinates→ℂ)
    (hF : ∀p,0<p 2→ContDiffAt ℝ ∞ F p)
    (hcoord : ∀q : KernelQuotient,∀p∈hyperbolicSpatialChart.target,
      f ((kernelQuotientChart q).symm p)=F p) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hc : ContinuousAt (kernelQuotientChart q) q :=
    (kernelQuotientChart q).continuousOn.continuousAt ((kernelQuotientChart q).open_source.mem_nhds hq)
  have heq : f=ᶠ[𝓝 q] (fun t => F (kernelQuotientChart q t)) := by
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with t ht
    rw [←hcoord q _ ((kernelQuotientChart q).map_source ht).1,
      (kernelQuotientChart q).left_inv ht]
  rw [contMDiffAt_iff]
  refine ⟨((hF _ (hyperbolicSpatialChart_target_positive hp)).continuousAt.comp hc).congr heq.symm,?_⟩
  have he : (fun p => f ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)] F := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact hcoord q p hp
  have hh := (hF _ (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma kernelQuotientDefect_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientDefect a b s) :=
  kernel_contMDiff_of_spatial _ _ (actual_smoothCuspSeedDefect_contDiffAt a b s ha hab)
    (fun q _ hp => kernelQuotientDefect_coordinate a b s q hp)

def kernelDefectSmoothTest (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) : kernelSmoothTests :=
  ⟨kernelQuotientDefect a b s,kernelQuotientDefect_contMDiff a b s ha hab,
    kernelQuotientDefect_hasCompactSupport a b (by linarith) hab s⟩

lemma kernelDefectSmoothTest_toL2 (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) :
    kernelSmoothTestsToL2 (kernelDefectSmoothTest a b ha hab s)=
      kernelL2Defect a b (by linarith) hab s := rfl

lemma kernelQuotientSeed_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientSeed a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeed a b s _=smoothCuspSeedField a b s p
  rw [smoothCuspSeedField,dif_pos (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientSeed_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientSeed a b s) :=
  kernel_contMDiff_of_spatial _ _ (actual_smoothCuspSeed_contDiffAt a b s ha hab)
    (kernelQuotientSeed_coordinate a b s)


#print axioms kernelQuotientDefect_hasCompactSupport
#print axioms kernelDefectSmoothTest_toL2
#print axioms kernelQuotientSeed_contMDiff
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
