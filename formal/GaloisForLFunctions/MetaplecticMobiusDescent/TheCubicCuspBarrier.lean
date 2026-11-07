/-
Invariant cusp barrier adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.HighCubicCuspsAreLocallyFinite
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicDirichletForm
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A smooth invariant barrier equal to cusp height

Integral cusp height functions are identified modulo the upper triangular
stabilizer. At most one exceeds one at any point. Their high regions are
locally finite, so a smooth transition gives an invariant smooth positive
barrier. Bianchi reduction confines its height-profile defect to a compact
subset of the actual cubic quotient.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

section
lemma kernelCompact_smooth_cutoff (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃χ : KernelQuotient→ℝ,ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ (∀q∈K,χ=ᶠ[𝓝 q](fun _ => 1)) ∧ ∀q,χ q∈Set.Icc 0 1 := by
  obtain ⟨J,hJ,hKJ⟩ := exists_compact_superset hK
  obtain ⟨χ,hχone,hχzero,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,SpatialCoordinates) hK.isClosed hKJ (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hχrange⟩
  · apply HasCompactSupport.of_support_subset_isCompact hJ
    intro q hq
    by_contra hn
    exact hq (hχzero q hn)
  · intro q hq
    exact hχone.filter_mono (nhds_le_nhdsSet hq)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

lemma integral_upper_triangular_height_all (M : SL(2,O))
    (hc : M 1 0=0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w)=hyperbolicHeight w := by
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  rw [integral_upper_triangular_height M hc,hyperbolicHeight_upperPoint]

def fullMatrixHeight (M : SL(2,O)) (w : HyperbolicSpace) : ℝ :=
  hyperbolicHeight (integralComplexMatrix M • w)

def fullCuspHeightRelation : Setoid (SL(2,O)) := Setoid.ker fullMatrixHeight
abbrev FullCuspClasses := Quotient fullCuspHeightRelation

def fullCuspOf (M : SL(2,O)) : FullCuspClasses := Quotient.mk _ M

def fullCuspHeight : FullCuspClasses→HyperbolicSpace→ℝ :=
  Quotient.lift fullMatrixHeight (fun _ _ h => h)

lemma fullCuspHeight_of (M : SL(2,O)) (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspOf M) w=fullMatrixHeight M w := rfl

lemma fullCuspHeight_continuous (x : FullCuspClasses) : Continuous (fullCuspHeight x) := by
  induction x using Quotient.inductionOn with
  | _ M => exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action (integralComplexMatrix M))

lemma fullMatrixHeight_eq_of_lower_zero (M N : SL(2,O))
    (h : (M*N⁻¹) 1 0=0) : fullMatrixHeight M=fullMatrixHeight N := by
  funext w
  have hh := integral_upper_triangular_height_all (M*N⁻¹) h (integralComplexMatrix N • w)
  simpa only [fullMatrixHeight,map_mul,map_inv,mul_smul,inv_smul_smul] using hh

lemma fullCuspOf_eq_iff (M N : SL(2,O)) :
    fullCuspOf M=fullCuspOf N ↔ (M*N⁻¹) 1 0=0 := by
  constructor
  · intro h
    by_contra hc
    have he : fullMatrixHeight M=fullMatrixHeight N := Quotient.exact h
    let w := upperPoint 0 2 (by norm_num : (0:ℝ)<2)
    have hh := congrFun he (integralComplexMatrix N⁻¹ • w)
    have hp := integral_hyperbolicHeight_mul_le_one (M*N⁻¹) hc w
    have hN : hyperbolicHeight w=2 := hyperbolicHeight_upperPoint _ _ _
    change hyperbolicHeight (integralComplexMatrix M • (integralComplexMatrix N⁻¹ • w))=
      hyperbolicHeight (integralComplexMatrix N • (integralComplexMatrix N⁻¹ • w)) at hh
    simp only [map_inv,smul_inv_smul] at hh
    simp only [map_mul,map_inv,mul_smul] at hp
    rw [hh,hN] at hp
    norm_num at hp
  · intro h
    exact Quotient.sound (fullMatrixHeight_eq_of_lower_zero M N h)

def fullCuspTranslate (M : SL(2,O)) : FullCuspClasses→FullCuspClasses :=
  Quotient.map (fun N => N*M) (by
    intro N P h
    change fullMatrixHeight (N*M)=fullMatrixHeight (P*M)
    funext w
    have hh := congrFun h (integralComplexMatrix M • w)
    simpa only [fullMatrixHeight,map_mul,mul_smul] using hh)

lemma fullCuspTranslate_mul (M N : SL(2,O)) (x : FullCuspClasses) :
    fullCuspTranslate N (fullCuspTranslate M x)=fullCuspTranslate (M*N) x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf ((P*M)*N)=fullCuspOf (P*(M*N)); rw [mul_assoc]

lemma fullCuspTranslate_one (x : FullCuspClasses) : fullCuspTranslate 1 x=x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf (P*1)=fullCuspOf P; rw [mul_one]

def fullCuspRightEquiv (M : SL(2,O)) : FullCuspClasses≃FullCuspClasses where
  toFun := fullCuspTranslate M
  invFun := fullCuspTranslate M⁻¹
  left_inv x := by rw [fullCuspTranslate_mul,mul_inv_cancel,fullCuspTranslate_one]
  right_inv x := by rw [fullCuspTranslate_mul,inv_mul_cancel,fullCuspTranslate_one]

lemma fullCuspHeight_translate (M : SL(2,O)) (x : FullCuspClasses)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspRightEquiv M x) w=fullCuspHeight x (integralComplexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N => change fullMatrixHeight (N*M) w=fullMatrixHeight N (integralComplexMatrix M • w)
           simp only [fullMatrixHeight,map_mul,mul_smul]

lemma fullCuspHeight_high_unique (w : HyperbolicSpace) (x y : FullCuspClasses)
    (hx : 1<fullCuspHeight x w) (hy : 1<fullCuspHeight y w) : x=y := by
  induction x using Quotient.inductionOn with
  | _ M =>
    induction y using Quotient.inductionOn with
    | _ N =>
      apply (fullCuspOf_eq_iff M N).mpr
      by_contra hc
      have hp := integral_hyperbolicHeight_mul_le_one (M*N⁻¹) hc (integralComplexMatrix N • w)
      simp only [map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change 1<fullMatrixHeight M w at hx
      change 1<fullMatrixHeight N w at hy
      change fullMatrixHeight M w*fullMatrixHeight N w≤1 at hp
      nlinarith [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]

lemma fullCusp_profile_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x : FullCuspClasses => F (fullCuspHeight x w)) := by
  have hs : Set.Subsingleton {x : FullCuspClasses | 1<fullCuspHeight x w} :=
    fun x hx y hy => fullCuspHeight_high_unique w x y hx hy
  apply hs.finite.subset
  intro x hx
  by_contra hn
  exact hx (hF _ (le_of_not_gt hn))

def fullCuspProfileSum (F : ℝ→ℝ) (w : HyperbolicSpace) : ℝ :=
  ∑'x : FullCuspClasses,F (fullCuspHeight x w)

lemma fullCuspProfileSum_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    Summable (fun x : FullCuspClasses => F (fullCuspHeight x w)) :=
  summable_of_hasFiniteSupport (fullCusp_profile_finite F hF w)

lemma fullCuspProfileSum_invariant (F : ℝ→ℝ) (M : SL(2,O)) (w : HyperbolicSpace) :
    fullCuspProfileSum F (integralComplexMatrix M • w)=fullCuspProfileSum F w := by
  unfold fullCuspProfileSum
  simp only [←fullCuspHeight_translate M]
  exact (fullCuspRightEquiv M).tsum_eq (fun x : FullCuspClasses => F (fullCuspHeight x w))

lemma fullCuspProfileSum_eq_single (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (w : HyperbolicSpace) (x : FullCuspClasses) (hx : 1<fullCuspHeight x w) :
    fullCuspProfileSum F w=F (fullCuspHeight x w) := by
  apply tsum_eq_single x
  intro y hy
  apply hF
  by_contra hn
  exact hy (fullCuspHeight_high_unique w y x (lt_of_not_ge hn) hx)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def cuspTransition (a b v : ℝ) : ℝ := Real.smoothTransition ((v-a)/(b-a))

lemma cuspTransition_contDiff (a b : ℝ) : ContDiff ℝ ∞ (cuspTransition a b) := by
  unfold cuspTransition
  fun_prop

lemma cuspTransition_zero (a b v : ℝ) (hab : a<b) (hv : v≤a) : cuspTransition a b v=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (sub_pos.mpr hab).le)
lemma cuspTransition_one (a b v : ℝ) (hab : a<b) (hv : b≤v) : cuspTransition a b v=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

lemma cuspTransition_derivatives (a b v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    deriv (cuspTransition a b) v=0 ∧ deriv (deriv (cuspTransition a b)) v=0 := by
  rcases hv with hv | hv
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspTransition_zero a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx
      exact cuspTransition_one a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩

def cuspBarrierProfile (a b v : ℝ) : ℝ := cuspTransition a b v*(v-1)

lemma cuspBarrierProfile_smooth (a b : ℝ) : ContDiff ℝ ∞ (cuspBarrierProfile a b) :=
  (cuspTransition_contDiff a b).mul (contDiff_id.sub contDiff_const)

lemma cuspBarrierProfile_zero (a b : ℝ) (hab : a<b) (v : ℝ) (hv : v≤a) :
    cuspBarrierProfile a b v=0 := by
  rw [cuspBarrierProfile,cuspTransition_zero a b v hab hv,zero_mul]

lemma cuspBarrierProfile_nonneg (a b : ℝ) (ha : 1≤a) (hab : a<b) (v : ℝ) :
    0≤cuspBarrierProfile a b v := by
  by_cases hv : v≤a
  · rw [cuspBarrierProfile_zero a b hab v hv]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (ha.trans (le_of_not_ge hv)))

def cuspBarrier (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  1+fullCuspProfileSum (cuspBarrierProfile a b) w

lemma cuspBarrier_summable (a b : ℝ) (ha : 1≤a) (hab : a<b) (w : HyperbolicSpace) :
    Summable (fun x : FullCuspClasses => cuspBarrierProfile a b (fullCuspHeight x w)) :=
  fullCuspProfileSum_summable _ (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha)) w

lemma cuspBarrier_one_le (a b : ℝ) (ha : 1≤a) (hab : a<b) (w : HyperbolicSpace) :
    1≤cuspBarrier a b w := by
  exact le_add_of_nonneg_right (tsum_nonneg (fun x => cuspBarrierProfile_nonneg a b ha hab _))

lemma cuspBarrier_invariant (a b : ℝ) (M : SL(2,O)) (w : HyperbolicSpace) :
    cuspBarrier a b (integralComplexMatrix M • w)=cuspBarrier a b w := by
  rw [cuspBarrier,cuspBarrier,fullCuspProfileSum_invariant]

theorem cuspBarrier_high (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b<v) :
    cuspBarrier a b (integralComplexMatrix M • upperPoint z v hv)=v := by
  rw [cuspBarrier_invariant]
  have hx : fullCuspHeight (fullCuspOf 1) (upperPoint z v hv)=v := by
    simp only [fullCuspHeight_of,fullMatrixHeight,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspBarrier,fullCuspProfileSum_eq_single _
    (fun y hy => cuspBarrierProfile_zero a b hab y (hy.trans ha)) _ (fullCuspOf 1)
      (by rw [hx]; linarith),hx,cuspBarrierProfile,cuspTransition_one a b v hab hbv.le,one_mul]
  ring

def kernelQuotientBarrier (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrier a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrier_invariant a b (M:SL(2,O)) w).symm)

lemma kernelQuotientBarrier_one_le (a b : ℝ) (ha : 1≤a) (hab : a<b) (q : KernelQuotient) :
    1≤kernelQuotientBarrier a b q := by
  induction q using Quotient.inductionOn with
  | _ w => exact cuspBarrier_one_le a b ha hab w

lemma kernelQuotientBarrier_fordCusp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,O)) (p : UpperCoordinates) (hp : b<p.1.2) :
    kernelQuotientBarrier a b (fordOrbitChart globalKubotaKernel M p)=p.1.2 :=
  cuspBarrier_high a b ha hab M⁻¹ p.1.1 p.1.2 p.2 hp

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

def fullCuspFromPrincipal (r : SL(2,O)) : CuspCosets→FullCuspClasses :=
  Quotient.lift (fun N : CubicKubota.levelThree => fullCuspOf ((N:SL(2,O))*r⁻¹)) (by
    intro N P h
    apply Quotient.sound
    funext w
    have he : cosetOf N=cosetOf P := Quotient.sound h
    have hh := congrArg (fun x => cosetHeight x (integralComplexMatrix r⁻¹ • w)) he
    simpa only [cosetHeight_cosetOf,fullMatrixHeight,map_mul,mul_smul,integralComplexMatrix_levelThree] using hh)

lemma fullCuspFromPrincipal_height (r : SL(2,O)) (x : CuspCosets)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspFromPrincipal r x) w=cosetHeight x (integralComplexMatrix r⁻¹ • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change fullMatrixHeight ((N:SL(2,O))*r⁻¹) w=cosetHeight (cosetOf N) _
    simp only [fullMatrixHeight,cosetHeight_cosetOf,map_mul,mul_smul,integralComplexMatrix_levelThree]

lemma fullCusp_finite_principal_cover :
    ∃S : Finset (SL(2,O)),∀x : FullCuspClasses,
      ∃r∈S,∃y : CuspCosets,fullCuspFromPrincipal r y=x := by
  let : CubicKubota.levelThree.FiniteIndex := levelThree_finiteIndex
  obtain ⟨S,hS⟩ := finite_right_representatives CubicKubota.levelThree
  refine ⟨S,fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ M =>
    obtain ⟨r,hr,hM⟩ := hS M⁻¹
    have hm : M*r∈CubicKubota.levelThree := by
      simpa only [mul_inv_rev,inv_inv] using CubicKubota.levelThree.inv_mem hM
    refine ⟨r,hr,cosetOf ⟨M*r,hm⟩,?_⟩
    change fullCuspOf ((M*r)*r⁻¹)=fullCuspOf M
    rw [mul_inv_cancel_right]

lemma full_high_locally_finite (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset FullCuspClasses,
      ∀z∈U,∀x∉T,fullCuspHeight x z<1 := by
  obtain ⟨S,hS⟩ := fullCusp_finite_principal_cover
  choose U hU hw T hT using fun r : S => principal_high_locally_finite (integralComplexMatrix r.1⁻¹ • w)
  let V : Set HyperbolicSpace := ⋂r : S,(fun z => integralComplexMatrix r.1⁻¹ • z) ⁻¹' U r
  let B : Finset FullCuspClasses := Finset.univ.biUnion (fun r : S => (T r).image (fullCuspFromPrincipal r.1))
  refine ⟨V,isOpen_iInter_of_finite (fun r => (hU r).preimage (continuous_hyperbolic_action _)),?_,B,?_⟩
  · exact Set.mem_iInter.mpr hw
  · intro z hz x hx
    obtain ⟨r,hr,y,hxy⟩ := hS x
    let i : S := ⟨r,hr⟩
    have hy : y∉T i := by
      intro hy
      apply hx
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,hy,hxy⟩⟩
    rw [←hxy,fullCuspFromPrincipal_height]
    exact hT i _ (Set.mem_iInter.mp hz i) y hy

lemma fullCuspProfileSum_locally_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    ∃T : Finset FullCuspClasses,fullCuspProfileSum F =ᶠ[𝓝 w]
      (fun z => ∑x∈T,F (fullCuspHeight x z)) := by
  obtain ⟨U,hU,hw,T,hT⟩ := full_high_locally_finite w
  refine ⟨T,?_⟩
  filter_upwards [hU.mem_nhds hw] with z hz
  apply tsum_eq_sum
  intro x hx
  exact hF _ (hT z hz x hx).le

lemma fullCuspProfileSum_continuous (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hFc : Continuous F) :
    Continuous (fullCuspProfileSum F) := by
  rw [continuous_iff_continuousAt]
  intro w
  obtain ⟨T,hT⟩ := fullCuspProfileSum_locally_finite F hF w
  apply ContinuousAt.congr _ hT.symm
  exact (continuous_finsetSum T (fun x hx => hFc.comp (fullCuspHeight_continuous x))).continuousAt

lemma cuspBarrier_continuous (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    Continuous (cuspBarrier a b) :=
  continuous_const.add (fullCuspProfileSum_continuous _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha)) (cuspBarrierProfile_smooth a b).continuous)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups

lemma hyperbolicSpatialChart_symm_eq {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) :
    hyperbolicSpatialChart.symm p=upperPoint (spatialHorizontal p) (p 2)
      (hyperbolicSpatialChart_target_positive hp) := by
  have h := hyperbolicSpatialCoordinates_reconstruct (hyperbolicSpatialChart.symm p)
  have he : hyperbolicSpatialCoordinates (hyperbolicSpatialChart.symm p)=p :=
    hyperbolicSpatialChart.right_inv hp
  simpa only [he,spatialHorizontal] using h.symm

lemma fullCuspHeight_chart_contDiffAt (x : FullCuspClasses) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => fullCuspHeight x (hyperbolicSpatialChart.symm q)) p := by
  induction x using Quotient.inductionOn with
  | _ M =>
    have hh : ContDiffAt ℝ ∞ (fun q => mobiusSpatial (integralComplexMatrix M) q 2) p :=
      (contDiff_apply ℝ ℝ 2).contDiffAt.comp p
        (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp))
    apply hh.congr_of_eventuallyEq
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with q hq
    rw [hyperbolicSpatialChart_symm_eq hq]
    exact congrArg (fun r : SpatialCoordinates => r 2)
      (mobiusSpatial_coordinates (integralComplexMatrix M) q
        (hyperbolicSpatialChart_target_positive hq))

lemma fullCuspProfileSum_chart_contDiffAt (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (hFc : ContDiff ℝ ∞ F) (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => fullCuspProfileSum F (hyperbolicSpatialChart.symm q)) p := by
  obtain ⟨T,hT⟩ := fullCuspProfileSum_locally_finite F hF (hyperbolicSpatialChart.symm p)
  have hc := hyperbolicSpatialChart.continuousAt_symm hp
  have he := hT.comp_tendsto hc
  apply ContDiffAt.congr_of_eventuallyEq _ he
  exact ContDiffAt.sum (fun x hx => hFc.contDiffAt.comp p
    (fullCuspHeight_chart_contDiffAt x p hp))

lemma cuspBarrier_chart_contDiffAt (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (hyperbolicSpatialChart.symm q)) p :=
  contDiffAt_const.add (fullCuspProfileSum_chart_contDiffAt _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha))
    (cuspBarrierProfile_smooth a b) p hp)

lemma kernelQuotientBarrier_continuous (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    Continuous (kernelQuotientBarrier a b) :=
  (cuspBarrier_continuous a b ha hab).quotient_lift _

lemma kernelQuotientBarrier_contMDiff (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelQuotientBarrier a b) := by
  intro q
  rw [contMDiffAt_iff]
  refine ⟨(kernelQuotientBarrier_continuous a b ha hab).continuousAt,?_⟩
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hh := cuspBarrier_chart_contDiffAt a b ha hab _ hp
  have he : (fun p => kernelQuotientBarrier a b ((kernelQuotientChart q).symm p))=
      (fun p => cuspBarrier a b (hyperbolicSpatialChart.symm p)) := by
    funext p
    rw [kernelQuotientChart_symm]
    rfl
  have hh' := (he.symm ▸ hh).contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma cuspBarrier_euclidean_contDiffAt (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (euclideanToHyperbolic q)) p :=
  (((kernelQuotientBarrier_contMDiff a b ha hab).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p) |>.comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def positiveHeightLaplacian (F : ℝ→ℝ) (v : ℝ) : ℝ :=
  v*deriv F v-v^2*deriv (deriv F) v

def cuspBarrierDefectProfile (a b v : ℝ) : ℝ :=
  positiveHeightLaplacian (cuspBarrierProfile a b) v-cuspBarrierProfile a b v

lemma positiveHeightLaplacian_smooth (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (positiveHeightLaplacian F) := by
  have hD : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  exact (contDiff_id.mul hD).sub ((contDiff_id.pow 2).mul ((contDiff_infty_iff_deriv.mp hD).2))

lemma cuspBarrierDefectProfile_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (cuspBarrierDefectProfile a b) :=
  (positiveHeightLaplacian_smooth _ (cuspBarrierProfile_smooth a b)).sub
    (cuspBarrierProfile_smooth a b)

lemma cuspBarrierDefectProfile_zero (a b v : ℝ) (hab : a<b) (hv : v<a) :
    cuspBarrierDefectProfile a b v=0 := by
  have he : cuspBarrierProfile a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hv] with x hx
    exact cuspBarrierProfile_zero a b hab x hx.le
  have hd := he.deriv_eq
  have hdd : deriv (deriv (cuspBarrierProfile a b)) v=0 := by
    simpa only [show deriv (fun _ : ℝ => (0:ℝ))=(fun _ => 0) from funext (fun x => deriv_const x 0),deriv_const] using he.deriv.deriv_eq
  simp only [deriv_const] at hd
  simp only [cuspBarrierDefectProfile,positiveHeightLaplacian,he.eq_of_nhds,hd,hdd,mul_zero,sub_zero]

lemma cuspBarrierDefectProfile_one (a b v : ℝ) (hab : a<b) (hv : b<v) :
    cuspBarrierDefectProfile a b v=1 := by
  have he : cuspBarrierProfile a b =ᶠ[𝓝 v] (fun x => x-1) := by
    filter_upwards [Ioi_mem_nhds hv] with x hx
    rw [cuspBarrierProfile,cuspTransition_one a b x hab hx.le,one_mul]
  have hd := he.deriv_eq
  have hlin : deriv (fun x : ℝ => x-1)=(fun _ => 1) := by ext x; simp
  have hdd : deriv (deriv (cuspBarrierProfile a b)) v=0 := by
    simpa only [hlin,deriv_const] using he.deriv.deriv_eq
  simp only [deriv_sub_const,deriv_id''] at hd
  simp only [cuspBarrierDefectProfile,positiveHeightLaplacian,he.eq_of_nhds,hd,hdd]
  ring

def cuspBarrierDefect (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  -1+fullCuspProfileSum (cuspBarrierDefectProfile a b) w

lemma cuspBarrierDefect_invariant (a b : ℝ) (M : SL(2,O))
    (w : HyperbolicSpace) :
    cuspBarrierDefect a b (integralComplexMatrix M • w)=cuspBarrierDefect a b w := by
  rw [cuspBarrierDefect,cuspBarrierDefect,fullCuspProfileSum_invariant]

lemma cuspBarrierDefect_high (a b : ℝ) (ha : 1<a) (hab : a<b)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b<v) :
    cuspBarrierDefect a b (integralComplexMatrix M • upperPoint z v hv)=0 := by
  rw [cuspBarrierDefect_invariant]
  have hx : fullCuspHeight (fullCuspOf 1) (upperPoint z v hv)=v := by
    simp only [fullCuspHeight_of,fullMatrixHeight,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspBarrierDefect,fullCuspProfileSum_eq_single _
    (fun y hy => cuspBarrierDefectProfile_zero a b y hab (hy.trans_lt ha)) _ (fullCuspOf 1)
      (by rw [hx]; linarith),hx,cuspBarrierDefectProfile_one a b v hab hbv]
  ring

def kernelQuotientBarrierDefect (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrierDefect a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrierDefect_invariant a b (M:SL(2,O)) w).symm)

lemma kernelQuotientBarrierDefect_hasCompactSupport (a b : ℝ) (ha : 1<a) (hab : a<b) :
    HasCompactSupport (kernelQuotientBarrierDefect a b) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS b
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S b ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r b := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (cuspBarrierDefect_high a b ha hab r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

lemma kernelQuotientBarrierDefect_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientBarrierDefect a b) := by
  apply Continuous.quotient_lift
  exact continuous_const.add (fullCuspProfileSum_continuous _
    (fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha))
    (cuspBarrierDefectProfile_smooth a b).continuous)

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

#print axioms fullCuspHeight_high_unique
#print axioms kernelQuotientBarrier_contMDiff
#print axioms kernelQuotientBarrierDefect_hasCompactSupport
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
