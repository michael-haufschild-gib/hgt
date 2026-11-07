/-
Remainder gradient bounds adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinEquation
import GaloisForLFunctions.MetaplecticMobiusDescent.BoundedCubicEisensteinRemainder
import GaloisForLFunctions.MetaplecticMobiusDescent.SmoothCubicExhaustion

/-!
# Bounded hyperbolic gradient of the incoming remainder

For `Re s>4`, the absolute remainder sum is uniformly bounded by an
integrable lattice majorant after Bianchi reduction. The logarithmic height
gradient bounds each differentiated row by an auxiliary remainder profile.
Exact termwise differentiation then bounds the actual remainder gradient.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma cuspRemainderProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspRemainderProfile a b s) v :=
  (positiveHeightPower_contDiffAt s v hv.ne').sub (cuspSeedProfile_contDiffAt a b s v hv)

lemma cuspRemainderProfile_euler (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    (v:ℂ)*deriv (cuspRemainderProfile a b s) v=
      positiveHeightPower s v *
        (((1-cuspTransition a b v:ℝ):ℂ)*s-((v*deriv (cuspTransition a b) v:ℝ):ℂ)) := by
  have h := (positiveHeightPower_hasDerivAt s v hv.ne').sub
    (cuspSeedProfile_hasDerivAt a b s v hv.ne')
  change HasDerivAt (cuspRemainderProfile a b s) _ v at h
  rw [h.deriv]
  simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  ; ring

lemma cuspRemainderProfile_euler_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C) (v : ℝ) (hv : 0<v) :
    ‖(v:ℂ)*deriv (cuspRemainderProfile a b s) v‖≤(‖s‖+C)*v^s.re := by
  rw [cuspRemainderProfile_euler a b s v hv,norm_mul,
    positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]
  have hχ0 : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hχ1 : 1-cuspTransition a b v≤1 := by
    have h := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤cuspTransition a b v at h
    linarith
  have hfactor : ‖((1-cuspTransition a b v:ℝ):ℂ)*s-
      ((v*deriv (cuspTransition a b) v:ℝ):ℂ)‖≤‖s‖+C := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul,Complex.norm_of_nonneg hχ0,Complex.norm_real,Real.norm_eq_abs]
    have hm := mul_le_mul_of_nonneg_right hχ1 (norm_nonneg s)
    linarith [hC v]
  have hh := mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hv.le s.re)
  simpa only [mul_comm (v^s.re)] using hh

lemma cuspRemainderProfile_deriv_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b<v) : deriv (cuspRemainderProfile a b s) v=0 := by
  have he : cuspRemainderProfile a b s =ᶠ[𝓝 v] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hv,Ioi_mem_nhds hbv] with y hy hyb
    exact cuspRemainderProfile_zero a b s y hab hy hyb.le
  exact he.deriv_eq.trans (deriv_const v 0)

lemma cuspRemainder_row_scaled_deriv_bound (a b : ℝ) (s : ℂ) (C : ℝ)
    (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*(rowHeight u p)^s.re := by
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
  rw [hd.deriv]
  have he : (p 2:ℂ)*(deriv (cuspRemainderProfile a b s) (rowHeight u p)*
      (rowHeight u p:ℂ)*(rowLogD u p j:ℂ))=
      (((p 2*rowLogD u p j):ℝ):ℂ)*
        ((rowHeight u p:ℂ)*deriv (cuspRemainderProfile a b s) (rowHeight u p)) := by
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_of_le_one_left (norm_nonneg _) (rowLogD_hyperbolic_bound u hu p hp j)).trans
  exact cuspRemainderProfile_euler_bound a b s C hC _ (rowHeight_pos u hu p hp)

lemma positive_axis_hasDerivAt (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice f p j) (deriv (axisSlice f p j) (p j)) (p j) := by
  have hd : DifferentiableAt ℝ f (spatialAxisPath p j (p j)) := by
    simpa only [spatialAxisPath_self] using (hf p hp).differentiableAt (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt (p j)
    (spatialAxisPath_hasDerivAt p j (p j))).differentiableAt.hasDerivAt

lemma cuspRemainder_absolute_chart (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,O)) (z : ℂ) (hz : ‖z‖≤1)
    (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖)≤eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℝ := fun r => ‖cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,R r≤G (f r) := by
    intro r
    simpa only [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul] using
      translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0 r
  have hr : Summable R := (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hr,?_⟩
  have hsum : (∑'r,R r)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem cuspRemainder_absolute_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s (cosetHeight r w)‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s (cosetHeight r w)‖)≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith only [hz,norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith only [hh,hh0,hfloor]
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact cuspRemainder_absolute_chart a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainder_aux_norm (b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) (hvb : v≤b) :
    ‖cuspRemainderProfile (b+1) (b+2) s v‖=v^s.re := by
  rw [cuspRemainderProfile,cuspSeedProfile_zero (b+1) (b+2) s v (by linarith) (by linarith),
    sub_zero,positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]

lemma cuspRemainder_row_scaled_deriv_aux_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight u p)‖ := by
  have hh := rowHeight_pos u hu p hp
  by_cases hb : rowHeight u p≤b
  · rw [cuspRemainder_aux_norm b s _ hh hb]
    exact cuspRemainder_row_scaled_deriv_bound a b s C hC u hu p hp j
  · have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
      (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
    rw [hd.deriv,cuspRemainderProfile_deriv_zero a b s _ hab hh (lt_of_not_ge hb)]
    simp only [zero_mul,mul_zero,norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg s) hC0) (norm_nonneg _)

open Filter
open scoped BigOperators Classical Topology ContDiff

def weightedHeightProfile (F : ℝ→ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma weightedHeightProfile_axis_differentiable (F : ℝ→ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (weightedHeightProfile F r) p j) (p j) :=
  ((rowProfile_axis_derivatives F hF (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1.const_mul _).differentiableAt

lemma heightPoincare_axis_termwise (F : ℝ→ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) ∧
    HasDerivAt (axisSlice (heightPoincareField F) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) (p j) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [ContinuousAt,Function.update_eq_self] using
      ((continuous_axis_update p j).continuousAt (x := p j))
  have hn : ∀ᶠt in 𝓝 (p j),Function.update p j t∈U := ht (hU.mem_nhds hpU)
  have hz (r : CuspCosets) (hr : r∉S) :
      deriv (axisSlice (weightedHeightProfile F r) p j) (p j)=0 := by
    have he : axisSlice (weightedHeightProfile F r) p j=ᶠ[𝓝 (p j)] (fun _ => 0) := by
      filter_upwards [hn] with t ht
      change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
      rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]
    exact he.deriv_eq.trans (deriv_const _ _)
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have hd := HasDerivAt.sum (u := S) (fun r hr =>
    (weightedHeightProfile_axis_differentiable F hF r p hp j).hasDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  simp only [Finset.sum_apply]
  change (∑'r,weightedHeightProfile F r (Function.update p j t))=
    ∑r∈S,weightedHeightProfile F r (Function.update p j t)
  apply tsum_eq_sum
  intro r hr
  change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
  rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]

lemma weightedRemainder_axis_deriv (a b : ℝ) (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      deriv (axisSlice (smoothSummand s r) p j) (p j)-
        deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  have he : axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j=ᶠ[𝓝 (p j)]
      (fun t => axisSlice (smoothSummand s r) p j t-
        axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j t) := by
    filter_upwards [hn] with t ht
    simp only [axisSlice,weightedHeightProfile,cuspRemainderProfile,smoothSummand]
    rw [rowSmoothPower_eq_profile s _ (embeddedRow_ne_zero r) _ ht]
    ring
  rw [he.deriv_eq]
  exact deriv_sub (positive_axis_hasDerivAt _ (smoothSummand_contDiffAt s r) p hp j).differentiableAt
    (weightedHeightProfile_axis_differentiable _ (cuspSeedProfile_contDiffAt a b s) r p hp j)

def eisensteinRemainderField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  smoothEisenstein s p-smoothCuspSeedField a b s p

theorem eisensteinRemainder_axis_termwise (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) ∧
    HasDerivAt (axisSlice (eisensteinRemainderField a b s) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) (p j) := by
  have hE := eisenstein_first_axis_sum s hs p hp j
  have hEd := positive_axis_hasDerivAt _ (smoothEisenstein_contDiffAt s hs) p hp j
  rw [hE.2] at hEd
  have hS := heightPoincare_axis_termwise (cuspSeedProfile a b s)
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp j
  have hcoeff : (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))=
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j))-
        ∑'r,deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
    simp_rw [weightedRemainder_axis_deriv a b s _ p hp j]
    exact hE.1.tsum_sub hS.1
  refine ⟨(hE.1.sub hS.1).congr (fun r => (weightedRemainder_axis_deriv a b s r p hp j).symm),?_⟩
  rw [hcoeff]
  apply (hEd.sub hS.2).congr_of_eventuallyEq
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  filter_upwards [hn] with t ht
  change smoothEisenstein s _-smoothCuspSeedField a b s _=
    smoothEisenstein s _-heightPoincareField (cuspSeedProfile a b s) _
  rw [smoothCuspSeedField_eq a b s ha hab _ ht]

lemma weightedRemainder_scaled_deriv_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖ := by
  let g : SpatialCoordinates→ℂ:=fun q => cuspRemainderProfile a b s (rowHeight (embeddedRow r) q)
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1
  have hw := hd.const_mul (cosetCharacter r)⁻¹
  have he : deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      (cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j) := by
    change deriv (fun t => (cosetCharacter r)⁻¹*axisSlice g p j t) (p j)=_
    rw [hw.deriv,hd.deriv]
  rw [he]
  calc
    ‖(p 2:ℂ)*((cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j))‖
      = ‖(cosetCharacter r)⁻¹*((p 2:ℂ)*deriv (axisSlice g p j) (p j))‖ := by congr 1; ring
    _ = ‖(p 2:ℂ)*deriv (axisSlice g p j) (p j)‖ := by
      rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul]
    _ ≤ _ := cuspRemainder_row_scaled_deriv_aux_bound a b hab s C hC0 hC _ (embeddedRow_ne_zero r) p hp j

theorem eisensteinRemainder_scaled_axis_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (eisensteinRemainderField a b s) p j) (p j)‖≤B := by
  obtain ⟨C,hC0,hC⟩ := cuspTransition_euler_bounded a b hab
  refine ⟨(‖s‖+C)*eisensteinRemainderBound (b+2) s,
    mul_nonneg (add_nonneg (norm_nonneg s) hC0) (eisensteinRemainderBound_nonneg _ _),?_⟩
  intro p hp j
  have hA : Summable (fun r : CuspCosets =>
      ‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖) ∧
      (∑'r : CuspCosets,‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖)≤
        eisensteinRemainderBound (b+2) s := by
    simpa only [cosetHeight_upperPoint_rowHeight] using
      cuspRemainder_absolute_bound (b+1) (b+2) (by linarith) (by linarith) s hs
        (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)
  have hB := hA.1.mul_left (‖s‖+C)
  have hb (r : CuspCosets) := weightedRemainder_scaled_deriv_bound a b hab s C hC0 hC r p hp j
  have hnorm := hB.of_nonneg_of_le (fun r => norm_nonneg
    ((p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))) hb
  have ht := eisensteinRemainder_axis_termwise a b ha hab s (by linarith) p hp j
  rw [ht.2.deriv,←tsum_mul_left]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (Summable.tsum_le_tsum hb hnorm hB).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hA.2 (add_nonneg (norm_nonneg s) hC0)

def kernelEisensteinRemainder (a b : ℝ) (s : ℂ) (hs : 2<s.re) : KernelQuotient→ℂ :=
  fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q

lemma kernelEisensteinRemainder_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelEisensteinRemainder a b s hs) :=
  (kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)

lemma kernelEisensteinRemainder_euclidean_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => kernelEisensteinRemainder a b s hs (kernelEuclideanProjection q)) p :=
  ((((kernelEisensteinRemainder_smooth a b ha hab s hs).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelEisensteinRemainder_euclidean_eq (a b : ℝ) (s : ℂ) (hs : 2<s.re)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p)=eisensteinRemainderField a b s p.ofLp := by
  unfold kernelEisensteinRemainder kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp,kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint]
  unfold eisensteinRemainderField
  rw [smoothEisenstein_eq_actual s p.ofLp hp,smoothCuspSeedField,dif_pos hp]
  simp only [mul_comm Complex.I]
  rfl

theorem kernelEisensteinRemainder_scaled_fderiv_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => kernelEisensteinRemainder a b s (by linarith)
        (kernelEuclideanProjection q)) p (euclideanCoordinateVector j)‖≤B := by
  obtain ⟨B,hB,hbound⟩ := eisensteinRemainder_scaled_axis_bound a b ha hab s hs
  refine ⟨B,hB,?_⟩
  intro p hp j
  let f : EuclideanSpatial→ℂ:=fun q => kernelEisensteinRemainder a b s (by linarith) (kernelEuclideanProjection q)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s (by linarith)
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s (by linarith) (WithLp.toLp 2 q) hq
  have heq := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤B
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,heq.deriv_eq]
  exact hbound p.ofLp hp j


#print axioms cuspRemainder_absolute_bound
#print axioms kernelEisensteinRemainder_scaled_fderiv_bound
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
