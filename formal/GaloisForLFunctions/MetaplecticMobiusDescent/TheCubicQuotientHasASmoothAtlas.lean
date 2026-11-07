/-
Smooth quotient atlas adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.SmoothCutoffsOnTheCubicQuotient
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Smooth atlas of the cubic quotient

Upper half-space coordinates give a global chart on hyperbolic three-space.
Local inverses of the covering projection give quotient charts. On overlaps,
lifts differ locally by a fixed integral matrix, whose Möbius action is smooth.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

abbrev SpatialCoordinates := Fin 3 → ℝ

def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]

lemma hyperbolicSpatialCoordinates_continuous : Continuous hyperbolicSpatialCoordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous

lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w

lemma hyperbolicSpatialCoordinates_reconstruct (w : HyperbolicSpace) :
    upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+(hyperbolicSpatialCoordinates w 1:ℂ)*Complex.I)
      (hyperbolicSpatialCoordinates w 2) (hyperbolicSpatialCoordinates_positive w)=w := by
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+((hyperbolicHorizontal w).im:ℂ)*Complex.I)
    (hyperbolicHeight w) (hyperbolicHeight_pos w)=w
  rw [Complex.re_add_im]
  exact upperCoordinates_right_inverse w

def spatialHorizontal (p : SpatialCoordinates) : ℂ := (p 0:ℂ)+(p 1:ℂ)*Complex.I

def mobiusSpatialDenominator (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℝ :=
  Complex.normSq (g 1 0*spatialHorizontal p+g 1 1)+Complex.normSq (g 1 0)*(p 2)^2

def mobiusSpatialHorizontal (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℂ :=
  ((g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
    g 0 0*star (g 1 0)*(p 2:ℂ)^2)/(mobiusSpatialDenominator g p:ℂ)

/-- Möbius action in horizontal real, horizontal imaginary, and height coordinates. -/
def mobiusSpatial (g : SL(2,ℂ)) (p : SpatialCoordinates) : SpatialCoordinates :=
  ![(mobiusSpatialHorizontal g p).re,(mobiusSpatialHorizontal g p).im,
    p 2/mobiusSpatialDenominator g p]

lemma mobiusSpatialDenominator_pos (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<mobiusSpatialDenominator g p := by
  simpa only [mobiusSpatialDenominator,Complex.normSq_eq_norm_sq] using
    mobius_denominator_pos g (spatialHorizontal p) (p 2) hp

lemma mobiusSpatial_positive (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0<mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)

lemma mobiusSpatial_coordinates (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    hyperbolicSpatialCoordinates (g • upperPoint (spatialHorizontal p) (p 2) hp)=mobiusSpatial g p := by
  rw [mobius_upperPoint]
  simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,
    mobiusSpatial,mobiusSpatialHorizontal,mobiusSpatialDenominator,Complex.normSq_eq_norm_sq]

lemma spatialHorizontal_contDiff : ContDiff ℝ ∞ spatialHorizontal := by
  unfold spatialHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)

lemma mobiusSpatialDenominator_contDiff (g : SL(2,ℂ)) : ContDiff ℝ ∞ (mobiusSpatialDenominator g) := by
  unfold mobiusSpatialDenominator
  have hz : ContDiff ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) :=
    (contDiff_const.mul spatialHorizontal_contDiff).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hz
  have him := Complex.imCLM.contDiff.comp hz
  change ContDiff ℝ ∞ (fun p =>
    (g 1 0*spatialHorizontal p+g 1 1).re*(g 1 0*spatialHorizontal p+g 1 1).re+
    (g 1 0*spatialHorizontal p+g 1 1).im*(g 1 0*spatialHorizontal p+g 1 1).im+
    Complex.normSq (g 1 0)*(p 2)^2)
  exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 2).pow 2))

lemma mobiusSpatial_contDiffAt (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (mobiusSpatial g) p := by
  have hD := (mobiusSpatialDenominator_contDiff g).contDiffAt (x := p)
  have hDc : ContDiffAt ℝ ∞ (fun p => (mobiusSpatialDenominator g p:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hD
  have hnum : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates =>
      (g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
        g 0 0*star (g 1 0)*(p 2:ℂ)^2) p := by
    have hz := spatialHorizontal_contDiff.contDiffAt (x := p)
    have hcz : ContDiffAt ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) p :=
      (contDiffAt_const.mul hz).add contDiffAt_const
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp p hcz
    have hv : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => (p 2:ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ 2).contDiffAt
    exact (((contDiffAt_const.mul hz).add contDiffAt_const).mul hc).add
      (contDiffAt_const.mul (hv.pow 2))
  have hh : ContDiffAt ℝ ∞ (mobiusSpatialHorizontal g) p :=
    by
      unfold mobiusSpatialHorizontal
      simp only [div_eq_mul_inv]
      exact hnum.mul (hDc.inv (Complex.ofReal_ne_zero.mpr (mobiusSpatialDenominator_pos g p hp).ne'))
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact Complex.reCLM.contDiff.contDiffAt.comp p hh
  · exact Complex.imCLM.contDiff.contDiffAt.comp p hh
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => p 2) p).div hD
      (mobiusSpatialDenominator_pos g p hp).ne'

abbrev PositiveSpatial := {p : SpatialCoordinates // 0<p 2}

def positiveSpatialToUpper (p : PositiveSpatial) : UpperCoordinates :=
  ⟨(spatialHorizontal p.1,p.1 2),p.2⟩
def upperToPositiveSpatial (p : UpperCoordinates) : PositiveSpatial :=
  ⟨![p.1.1.re,p.1.1.im,p.1.2],p.2⟩

lemma positiveSpatialToUpper_continuous : Continuous positiveSpatialToUpper := by
  apply Continuous.subtype_mk
  exact (spatialHorizontal_contDiff.continuous.comp continuous_subtype_val).prodMk
    ((continuous_apply 2).comp continuous_subtype_val)
lemma upperToPositiveSpatial_continuous : Continuous upperToPositiveSpatial := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

def positiveSpatialUpperHomeomorph : PositiveSpatial ≃ₜ UpperCoordinates where
  toFun := positiveSpatialToUpper
  invFun := upperToPositiveSpatial
  left_inv p := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [upperToPositiveSpatial,positiveSpatialToUpper,spatialHorizontal]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Complex.re_add_im _
    · rfl
  continuous_toFun := positiveSpatialToUpper_continuous
  continuous_invFun := upperToPositiveSpatial_continuous

def positiveSpatialHomeomorph : PositiveSpatial ≃ₜ HyperbolicSpace :=
  positiveSpatialUpperHomeomorph.trans upperCoordinatesHomeomorph

lemma hyperbolicSpatial_isOpenEmbedding : Topology.IsOpenEmbedding hyperbolicSpatialCoordinates := by
  have ho : IsOpen {p : SpatialCoordinates | 0<p 2} := isOpen_lt continuous_const (by fun_prop)
  have he := ho.isOpenEmbedding_subtypeVal.comp positiveSpatialHomeomorph.symm.isOpenEmbedding
  exact he


def hyperbolicSpatialChart : OpenPartialHomeomorph HyperbolicSpace SpatialCoordinates :=
  hyperbolicSpatial_isOpenEmbedding.toOpenPartialHomeomorph hyperbolicSpatialCoordinates

@[simp] lemma hyperbolicSpatialChart_apply (w : HyperbolicSpace) :
    hyperbolicSpatialChart w=hyperbolicSpatialCoordinates w := rfl

@[simp] lemma hyperbolicSpatialChart_source : hyperbolicSpatialChart.source=Set.univ := rfl

lemma hyperbolicSpatialChart_target_positive {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) : 0<p 2 := by
  have he := hyperbolicSpatialChart.right_inv hp
  have hh := hyperbolicSpatialCoordinates_positive (hyperbolicSpatialChart.symm p)
  rwa [← hyperbolicSpatialChart_apply,he] at hh

def kernelLocalLift (w : HyperbolicSpace) : OpenPartialHomeomorph KernelQuotient HyperbolicSpace :=
  kernelQuotient_localHomeomorph.localInverseAt w

@[simp] lemma kernelLocalLift_symm (w : HyperbolicSpace) :
    (kernelLocalLift w).symm=integralOrbitProjection globalKubotaKernel :=
  kernelQuotient_localHomeomorph.localInverseAt_symm w

lemma kernelLocalLift_project {w : HyperbolicSpace} {q : KernelQuotient}
    (hq : q∈(kernelLocalLift w).source) :
    integralOrbitProjection globalKubotaKernel (kernelLocalLift w q)=q :=
  kernelQuotient_localHomeomorph.apply_localInverseAt_of_mem hq

/-- Local injectivity identifies two continuous lifts agreeing at the base point. -/
lemma kernel_lifts_eventually_eq {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hfg : f x=g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) : f=ᶠ[𝓝 x]g := by
  obtain ⟨U,hU,hx,hUinj⟩ := kernelQuotient_localHomeomorph.isLocallyInjective (f x)
  have hfn : ∀ᶠ y in 𝓝 x,f y∈U := hf (hU.mem_nhds hx)
  have hgn : ∀ᶠ y in 𝓝 x,g y∈U := hg (hU.mem_nhds (hfg ▸ hx))
  filter_upwards [hfn,hgn,hproj] with y hyf hyg hye
  exact hUinj hyf hyg hye

/-- Two local lifts differ near a point by one fixed deck transformation. -/
lemma kernel_lifts_eventually_deck {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) :
    ∃M : globalKubotaKernel, f=ᶠ[𝓝 x](fun y => integralComplexMatrix M • g y) := by
  have he := (integralOrbitProjection_eq_iff globalKubotaKernel (f x) (g x)).mp
    hproj.self_of_nhds
  obtain ⟨M,hM⟩ := MulAction.mem_orbit_iff.mp he
  refine ⟨M,kernel_lifts_eventually_eq hf
    ((continuous_hyperbolic_action (integralComplexMatrix M)).continuousAt.comp hg) hM.symm ?_⟩
  filter_upwards [hproj] with y hy
  simpa only [integralOrbitProjection_eq] using hy

lemma mobiusSpatial_coordinates_global (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicSpatialCoordinates (g•w)=mobiusSpatial g (hyperbolicSpatialCoordinates w) := by
  have hp := hyperbolicSpatialCoordinates_positive w
  have hr := hyperbolicSpatialCoordinates_reconstruct w
  nth_rw 1 [← hr]
  exact mobiusSpatial_coordinates g (hyperbolicSpatialCoordinates w) hp

def kernelCoordinateTransition (w : HyperbolicSpace) (p : SpatialCoordinates) : SpatialCoordinates :=
  hyperbolicSpatialCoordinates (kernelLocalLift w
    (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)))

lemma kernelCoordinateTransition_eventually (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) :
    ∃M : globalKubotaKernel,kernelCoordinateTransition w=ᶠ[𝓝 p]
      mobiusSpatial (integralComplexMatrix M) := by
  have hc : ContinuousAt hyperbolicSpatialChart.symm p :=
    hyperbolicSpatialChart.symm.continuousAt hp
  have hπ : ContinuousAt (fun y => integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)) p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp hc
  have hl : ContinuousAt (fun y => kernelLocalLift w (integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y))) p :=
    ((kernelLocalLift w).continuousAt hq).comp
      (f := fun y : SpatialCoordinates => integralOrbitProjection globalKubotaKernel
        (hyperbolicSpatialChart.symm y)) hπ
  have hqn : ∀ᶠ y in 𝓝 p,integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)∈(kernelLocalLift w).source :=
    hπ ((kernelLocalLift w).open_source.mem_nhds hq)
  have hproj : (fun y => integralOrbitProjection globalKubotaKernel (kernelLocalLift w
      (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y))))=ᶠ[𝓝 p]
      (fun y => integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y)) := by
    filter_upwards [hqn] with y hy
    exact kernelLocalLift_project hy
  obtain ⟨M,hM⟩ := kernel_lifts_eventually_deck hl hc hproj
  refine ⟨M,?_⟩
  filter_upwards [hM,hyperbolicSpatialChart.open_target.mem_nhds hp] with y hy hyt
  change hyperbolicSpatialCoordinates _=mobiusSpatial _ y
  rw [hy,mobiusSpatial_coordinates_global]
  exact congrArg _ (hyperbolicSpatialChart.right_inv hyt)

lemma kernelCoordinateTransition_contDiffAt (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) : ContDiffAt ℝ ∞ (kernelCoordinateTransition w) p := by
  obtain ⟨M,hM⟩ := kernelCoordinateTransition_eventually w p hp hq
  exact (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq hM

/-- A quotient chart obtained from a covering lift followed by upper half-space coordinates. -/
def kernelQuotientChart (q : KernelQuotient) : OpenPartialHomeomorph KernelQuotient SpatialCoordinates :=
  (kernelLocalLift q.out).trans hyperbolicSpatialChart

@[simp] lemma kernelQuotientChart_symm (q : KernelQuotient) (p : SpatialCoordinates) :
    (kernelQuotientChart q).symm p=
      integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p) := by
  change (kernelLocalLift q.out).symm (hyperbolicSpatialChart.symm p)=_
  rw [kernelLocalLift_symm]

lemma kernelQuotientChart_contDiffOn (q r : KernelQuotient) :
    ContDiffOn ℝ ∞ ((kernelQuotientChart q).symm.trans (kernelQuotientChart r))
      ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)).source := by
  intro p hp
  have hp' : p∈hyperbolicSpatialChart.target := hp.1.1
  have hq' : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift r.out).source := by
    rw [← kernelQuotientChart_symm q p]
    exact hp.2.1
  have he : (fun p => ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)) p)=
      kernelCoordinateTransition r.out := by
    funext y
    change hyperbolicSpatialChart (kernelLocalLift r.out ((kernelQuotientChart q).symm y))=_
    rw [kernelQuotientChart_symm]
    rfl
  change ((kernelQuotientChart q).symm.trans (kernelQuotientChart r) : SpatialCoordinates→SpatialCoordinates)=_ at he
  rw [he]
  exact (kernelCoordinateTransition_contDiffAt r.out p hp' hq').contDiffWithinAt
instance hyperbolicSpatialChartedSpace : ChartedSpace SpatialCoordinates HyperbolicSpace :=
  hyperbolicSpatialChart.singletonChartedSpace hyperbolicSpatialChart_source

instance hyperbolicSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ HyperbolicSpace :=
  hyperbolicSpatialChart.isManifold_singleton hyperbolicSpatialChart_source

lemma kernelLocalLift_source_out (q : KernelQuotient) : q∈(kernelLocalLift q.out).source := by
  have h := kernelQuotient_localHomeomorph.apply_self_mem_localInverseAt_source (x := q.out)
  change integralOrbitProjection globalKubotaKernel q.out∈(kernelLocalLift q.out).source at h
  rwa [show integralOrbitProjection globalKubotaKernel q.out=q from Quotient.out_eq q] at h

instance kernelSpatialChartedSpace : ChartedSpace SpatialCoordinates KernelQuotient where
  atlas := Set.range kernelQuotientChart
  chartAt := kernelQuotientChart
  mem_chart_source q := ⟨kernelLocalLift_source_out q,Set.mem_univ _⟩
  chart_mem_atlas q := ⟨q,rfl⟩

/-- The actual cubic quotient carries the smooth atlas of its covering charts. -/
instance kernelSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ KernelQuotient := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨q,rfl⟩ ⟨r,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    kernelQuotientChart_contDiffOn q r

@[simp] lemma hyperbolicSpatial_chartAt (w : HyperbolicSpace) :
    chartAt SpatialCoordinates w=hyperbolicSpatialChart := rfl

@[simp] lemma kernelSpatial_chartAt (q : KernelQuotient) :
    chartAt SpatialCoordinates q=kernelQuotientChart q := rfl

lemma kernelProjection_contMDiff : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
    (integralOrbitProjection globalKubotaKernel) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_integralOrbitProjection globalKubotaKernel).continuousAt,?_⟩
  have hp : hyperbolicSpatialCoordinates w∈hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hq : integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w))∈
      (kernelLocalLift (integralOrbitProjection globalKubotaKernel w).out).source := by
    have hleft := hyperbolicSpatialChart.left_inv (Set.mem_univ w)
    change hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w)=w at hleft
    rw [hleft]
    exact kernelLocalLift_source_out _
  have h : ContDiffWithinAt ℝ ∞
      (kernelCoordinateTransition (integralOrbitProjection globalKubotaKernel w).out) Set.univ
      (hyperbolicSpatialCoordinates w) :=
    (kernelCoordinateTransition_contDiffAt _ _ hp hq).contDiffWithinAt
  unfold kernelCoordinateTransition at h
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    kernelSpatial_chartAt,hyperbolicSpatial_chartAt,kernelCoordinateTransition,
    kernelQuotientChart,OpenPartialHomeomorph.trans_apply,Function.comp_def,
    hyperbolicSpatialChart_apply,id_eq] using h

#print axioms kernelSpatialIsManifold
#print axioms kernelProjection_contMDiff
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
