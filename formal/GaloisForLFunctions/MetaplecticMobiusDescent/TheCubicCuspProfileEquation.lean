/-
Cusp barrier Laplacian adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicCuspBarrier
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicHeightProfiles

/-!
# The height-profile equation for the invariant cusp sum

Local finiteness reduces the sum to finitely many smooth height profiles.
The explicit row-height Laplacian therefore applies term by term.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma rowHeight_eq_transformedHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) :
    rowHeight u p=transformedHeight ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) u := by
  rw [transformedHeight,heightDenominator_eq_quadratic]
  rfl

def fullCuspRow (x : FullCuspClasses) : Fin 2→ℂ :=
  complexBottomRow (integralComplexMatrix x.out)

lemma fullCuspRow_ne_zero (x : FullCuspClasses) : fullCuspRow x≠0 :=
  complexBottomRow_ne_zero _

lemma fullCuspRow_height (x : FullCuspClasses) (p : SpatialCoordinates) (hp : 0<p 2) :
    rowHeight (fullCuspRow x) p=fullCuspHeight x (upperPoint (spatialHorizontal p) (p 2) hp) := by
  have hx : fullCuspOf x.out=x := Quotient.out_eq x
  conv_rhs => rw [←hx]
  rw [fullCuspHeight_of,fullMatrixHeight,hyperbolicHeight_action_upperPoint]
  rw [rowHeight_eq_transformedHeight]
  simp only [transformedHeight,heightDenominator,fullCuspRow,complexBottomRow,spatialHorizontal]

def fullCuspProfileField (F : ℝ→ℝ) (p : SpatialCoordinates) : ℝ :=
  ∑'x : FullCuspClasses,F (rowHeight (fullCuspRow x) p)

lemma fullCuspProfileField_eq (F : ℝ→ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField F p=fullCuspProfileSum F (upperPoint (spatialHorizontal p) (p 2) hp) := by
  simp only [fullCuspProfileField,fullCuspProfileSum,fullCuspRow_height _ p hp]

lemma fullCuspRows_locally_finite (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃T : Finset FullCuspClasses,∀ᶠq in 𝓝 p,∀x∉T,rowHeight (fullCuspRow x) q<1 := by
  let w := upperPoint (spatialHorizontal p) (p 2) hp
  obtain ⟨U,hU,hw,T,hT⟩ := full_high_locally_finite w
  have ht : p∈hyperbolicSpatialChart.target := by
    have he : hyperbolicSpatialChart w=p := by
      simp only [w,hyperbolicSpatialChart_apply,hyperbolicSpatialCoordinates,spatialHorizontal,
        hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
      ext j
      fin_cases j <;> simp
    rw [←he]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : hyperbolicSpatialChart.symm p=w := by
    rw [hyperbolicSpatialChart_symm_eq ht]
  have hnear := (hyperbolicSpatialChart.continuousAt_symm ht) (by simpa only [he] using hU.mem_nhds hw)
  refine ⟨T,?_⟩
  filter_upwards [hnear,hyperbolicSpatialChart.open_target.mem_nhds ht] with q hq hqt
  have hpos := hyperbolicSpatialChart_target_positive hqt
  intro x hx
  rw [fullCuspRow_height x q hpos,←hyperbolicSpatialChart_symm_eq hqt]
  exact hT _ hq x hx

lemma fullCuspProfileField_locally_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃T : Finset FullCuspClasses,fullCuspProfileField F =ᶠ[𝓝 p]
      (fun q => ∑x∈T,F (rowHeight (fullCuspRow x) q)) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  refine ⟨T,?_⟩
  filter_upwards [hT] with q hq
  apply tsum_eq_sum
  intro x hx
  exact hF _ (hq x hx).le

lemma cast_profile_deriv (F : ℝ→ℝ) (hF : Differentiable ℝ F) (v : ℝ) :
    deriv (fun y => (F y:ℂ)) v=((deriv F v:ℝ):ℂ) :=
  (hF v).hasDerivAt.ofReal_comp.deriv

lemma cast_profile_deriv2 (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) (v : ℝ) :
    deriv (deriv (fun y => (F y:ℂ))) v=((deriv (deriv F) v:ℝ):ℂ) := by
  have he : deriv (fun y => (F y:ℂ))=(fun y => ((deriv F y:ℝ):ℂ)) :=
    funext (cast_profile_deriv F (hF.differentiable (by simp)))
  rw [he]
  exact cast_profile_deriv (deriv F) (((contDiff_infty_iff_deriv.mp hF).2).differentiable (by simp)) v

lemma fullCuspProfile_row_laplacian (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (x : FullCuspClasses) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (F (rowHeight (fullCuspRow x) q):ℂ)) p=
      (positiveHeightLaplacian F (rowHeight (fullCuspRow x) p):ℂ) := by
  rw [rowProfile_laplacian (fun y => (F y:ℂ)) (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
    _ (fullCuspRow_ne_zero x) p hp,cast_profile_deriv F (hF.differentiable (by simp)),cast_profile_deriv2 F hF]
  simp only [positiveHeightLaplacian,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

lemma fullCuspProfileField_laplacian (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (hzero : ∀v≤1,F v=0) (hLzero : ∀v≤1,positiveHeightLaplacian F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (fullCuspProfileField F q:ℂ)) p=
      (fullCuspProfileField (positiveHeightLaplacian F) p:ℂ) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  have he : (fun q => (fullCuspProfileField F q:ℂ)) =ᶠ[𝓝 p]
      (fun q => ∑x∈T,(F (rowHeight (fullCuspRow x) q):ℂ)) := by
    filter_upwards [hT] with q hq
    have hh : fullCuspProfileField F q=∑x∈T,F (rowHeight (fullCuspRow x) q) :=
      tsum_eq_sum (fun x hx => hzero _ (hq x hx).le)
    rw [hh]
    push_cast
    rfl
  have hval : fullCuspProfileField (positiveHeightLaplacian F) p=
      ∑x∈T,positiveHeightLaplacian F (rowHeight (fullCuspRow x) p) :=
    tsum_eq_sum (fun x hx => hLzero _ (hT.self_of_nhds x hx).le)
  have hreg : ∀x∈T,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j)) (q j) := by
    intro x hx q hq j
    have hd := rowProfile_axis_derivatives (fun v => (F v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) q hq j
    exact ⟨hd.1.differentiableAt,hd.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p he,axisLaplacian_finset_sum T _ hreg p hp,hval]
  rw [←Finset.sum_neg_distrib]
  push_cast
  exact Finset.sum_congr rfl (fun x hx => fullCuspProfile_row_laplacian F hF x p hp)

#print axioms fullCuspProfileField_laplacian
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
