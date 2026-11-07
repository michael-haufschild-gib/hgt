/-
Axis differentiation and summation follow the local coordinate calculus
adapted from OpenAI's formalization, Apache-2.0. See LICENSE and NOTICE.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisensteinDerivatives
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactSmoothCubicDefects

/-!
# The actual cubic Eisenstein series satisfies its Laplace equation

Affine coordinate axes identify first and second derivatives with fixed
multilinear jets. The actual summable jet families commute with evaluation
and the finite coordinate sum. Each height-power summand has eigenvalue
`s(s−2)` for the negative Laplacian, hence so does the Eisenstein series.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def spatialCoordinateVector (j : Fin 3) : SpatialCoordinates := Pi.single j 1

def spatialAxisPath (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) : SpatialCoordinates :=
  Function.update p j t

lemma spatialAxisPath_affine (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    spatialAxisPath p j t=p+(t-p j)•spatialCoordinateVector j := by
  funext k
  by_cases hk : k=j
  · subst k
    simp [spatialAxisPath,spatialCoordinateVector]
  · simp [spatialAxisPath,spatialCoordinateVector,Function.update,hk]

lemma spatialAxisPath_self (p : SpatialCoordinates) (j : Fin 3) :
    spatialAxisPath p j (p j)=p := by
  rw [spatialAxisPath_affine,sub_self,zero_smul,add_zero]

lemma spatialAxisPath_hasDerivAt (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    HasDerivAt (spatialAxisPath p j) (spatialCoordinateVector j) t := by
  have he : spatialAxisPath p j=(fun t => p+(t-p j)•spatialCoordinateVector j) :=
    funext (spatialAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (spatialCoordinateVector j))

lemma spatialAxisSlice_deriv (f : SpatialCoordinates→ℂ) (p : SpatialCoordinates)
    (j : Fin 3) (t : ℝ) (hf : DifferentiableAt ℝ f (spatialAxisPath p j t)) :
    deriv (axisSlice f p j) t=
      fderiv ℝ f (spatialAxisPath p j t) (spatialCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (spatialAxisPath_hasDerivAt p j t)).deriv

lemma spatialAxisSlice_derivatives (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice f p j) (p j)=
      fderiv ℝ f p (spatialCoordinateVector j) ∧
    deriv (deriv (axisSlice f p j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (spatialCoordinateVector j)) p (spatialCoordinateVector j) := by
  constructor
  · simpa only [spatialAxisPath_self] using spatialAxisSlice_deriv f p j (p j)
      (by simpa only [spatialAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => spatialAxisPath p j t 2) (p j) :=
      (by fun_prop : Continuous (fun q : SpatialCoordinates => q 2)).continuousAt.comp
        (spatialAxisPath_hasDerivAt p j (p j)).continuousAt
    have hpos : 0<spatialAxisPath p j (p j) 2 := by rw [spatialAxisPath_self]; exact hp
    have he : deriv (axisSlice f p j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (spatialAxisPath p j t) (spatialCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact spatialAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (spatialCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (spatialCoordinateVector j))
        (spatialAxisPath p j (p j)) := by rwa [spatialAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (spatialAxisPath_hasDerivAt p j (p j))
    simpa only [spatialAxisPath_self,Function.comp_def] using! hh.deriv

lemma axis_first_jet (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    iteratedFDeriv ℝ 1 f p (fun _ => spatialCoordinateVector j)=
      deriv (axisSlice f p j) (p j) := by
  rw [iteratedFDeriv_one_apply]
  exact (spatialAxisSlice_derivatives f hf p hp j).1.symm

lemma axis_second_jet (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    iteratedFDeriv ℝ 2 f p (fun _ => spatialCoordinateVector j)=
      deriv (deriv (axisSlice f p j)) (p j) := by
  rw [(spatialAxisSlice_derivatives f hf p hp j).2,iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf p hp).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]

lemma smoothSummand_contDiffAt (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContDiffAt ℝ ∞ (smoothSummand s r) p := by
  have hh : ContDiffAt ℝ ∞ (fun q => positiveHeightPower s (rowHeight (embeddedRow r) q)) p :=
    (positiveHeightPower_contDiffAt s _ (rowHeight_pos _ (embeddedRow_ne_zero r) p hp).ne').comp p
      (rowHeight_contDiffAt _ (embeddedRow_ne_zero r) p hp)
  apply (contDiffAt_const.mul hh).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 2)).mem_nhds hp] with q hq
  exact congrArg (fun z => (cosetCharacter r)⁻¹*z)
    (rowSmoothPower_eq_profile s _ (embeddedRow_ne_zero r) q hq)

lemma eisenstein_first_axis_sum (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (smoothSummand s r) p j) (p j)) ∧
    deriv (axisSlice (smoothEisenstein s) p j) (p j)=
      ∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  have hh := smoothEisenstein_iteratedFDeriv_tsum s hs p hp 1
  let m : Fin 1 → SpatialCoordinates := fun _ => spatialCoordinateVector j
  have heq (r : CuspCosets) : iteratedFDeriv ℝ 1 (smoothSummand s r) p m=
      deriv (axisSlice (smoothSummand s r) p j) (p j) :=
    axis_first_jet _ (smoothSummand_contDiffAt s r) p hp j
  refine ⟨(ContinuousMultilinearMap.hasSum_eval hh.1.hasSum m).summable.congr heq,?_⟩
  calc
    _ = iteratedFDeriv ℝ 1 (smoothEisenstein s) p m :=
      (axis_first_jet _ (smoothEisenstein_contDiffAt s hs) p hp j).symm
    _ = ∑'r,iteratedFDeriv ℝ 1 (smoothSummand s r) p m := by
      rw [hh.2,ContinuousMultilinearMap.tsum_eval hh.1]
    _ = _ := tsum_congr heq

lemma eisenstein_second_axis_sum (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)) ∧
    deriv (deriv (axisSlice (smoothEisenstein s) p j)) (p j)=
      ∑'r,deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  have hh := smoothEisenstein_iteratedFDeriv_tsum s hs p hp 2
  let m : Fin 2 → SpatialCoordinates := fun _ => spatialCoordinateVector j
  have heq (r : CuspCosets) : iteratedFDeriv ℝ 2 (smoothSummand s r) p m=
      deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) :=
    axis_second_jet _ (smoothSummand_contDiffAt s r) p hp j
  refine ⟨(ContinuousMultilinearMap.hasSum_eval hh.1.hasSum m).summable.congr heq,?_⟩
  calc
    _ = iteratedFDeriv ℝ 2 (smoothEisenstein s) p m :=
      (axis_second_jet _ (smoothEisenstein_contDiffAt s hs) p hp j).symm
    _ = ∑'r,iteratedFDeriv ℝ 2 (smoothSummand s r) p m := by
      rw [hh.2,ContinuousMultilinearMap.tsum_eval hh.1]
    _ = _ := tsum_congr heq

theorem smoothEisenstein_eigenfunction (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothEisenstein s) p=s*(s-2)*smoothEisenstein s p := by
  let second := fun (j : Fin 3) (r : CuspCosets) =>
    deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)
  let first := fun r : CuspCosets => deriv (axisSlice (smoothSummand s r) p 2) (p 2)
  have hsecond (j : Fin 3) : Summable (second j) := (eisenstein_second_axis_sum s hs p hp j).1
  have hfirst : Summable first := (eisenstein_first_axis_sum s hs p hp 2).1
  have hsum : Summable (fun r => ∑j : Fin 3,second j r) := by
    simpa only [Fin.sum_univ_three] using ((hsecond 0).add (hsecond 1)).add (hsecond 2)
  have hcomm : (∑j : Fin 3,∑'r,second j r)=∑'r,∑j : Fin 3,second j r :=
    (Summable.tsum_finsetSum (fun j _ => hsecond j)).symm
  unfold axisLaplacian
  simp_rw [(eisenstein_second_axis_sum s hs p hp _).2]
  rw [(eisenstein_first_axis_sum s hs p hp 2).2]
  change (p 2:ℂ)^2*(∑j : Fin 3,∑'r,second j r)-(p 2:ℂ)*(∑'r,first r)=_
  rw [hcomm,←tsum_mul_left,←tsum_mul_left,←(hsum.mul_left _).tsum_sub (hfirst.mul_left _)]
  change (∑'r,axisLaplacian (smoothSummand s r) p)=_
  simp_rw [smoothSummand_axisLaplacian s _ p hp]
  rw [tsum_mul_left]
  rfl

lemma kernelQuotientEisenstein_coordinate (s : ℂ) (hs : 2<s.re) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientEisenstein s hs ((kernelQuotientChart q).symm p)=smoothEisenstein s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp,
    kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint,
    smoothEisenstein_eq_actual s p (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientEisenstein_contMDiff (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientEisenstein s hs) :=
  kernel_contMDiff_of_spatial _ _ (smoothEisenstein_contDiffAt s hs)
    (kernelQuotientEisenstein_coordinate s hs)

#print axioms smoothEisenstein_eigenfunction
#print axioms kernelQuotientEisenstein_contMDiff
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
