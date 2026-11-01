import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerNegativeUnitNonvanishing
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPositivePoleCoefficient
import Mathlib.Analysis.Analytic.Constructions

/-!
# The negative-unit Mayer inverse has a genuine source pole

The successor response gives an explicit square-zero shear. Every constant-mode
perturbation factors through this shear, preserving invertibility and giving its
exact inverse. Positive real-source nonvanishing supplies the required units.

Near source parameter one, the pole-free inverse is holomorphic, but the actual
source inverse has a nonzero rank-one Laurent residue. Its determinant is
holomorphic and nonzero there. The product of the two signed source determinants
retains the positive-unit factor's simple pole.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCancellation
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerResolvent

/-- The actual successor response coupled to evaluation at zero. -/
def responseShear (w : ℂ) : DiscSpace →L[ℂ] DiscSpace :=
  (evaluation zeroPoint).smulRight (response w)

theorem responseShear_apply (w : ℂ) (f : DiscSpace) :
    responseShear w f = f.1 zeroPoint • response w := rfl

private theorem response_zero (w : ℂ) : (response w).1 zeroPoint = 0 := by
  rw [response_apply]
  change 1-(1+0 : ℂ)^(-w) = 0
  simp only [add_zero,Complex.one_cpow,sub_self]

/-- The exact vanishing of the response at zero makes its shear square zero. -/
theorem responseShear_twice (w : ℂ) (f : DiscSpace) :
    responseShear w (responseShear w f) = 0 := by
  change responseShear w (f.1 zeroPoint • response w) = 0
  rw [map_smul,responseShear_apply,response_zero,zero_smul,smul_zero]

/-- Every complex shear parameter gives a bounded unit with an explicit inverse. -/
def responseShearUnit (w t : ℂ) : (DiscSpace →L[ℂ] DiscSpace)ˣ where
  val := 1+t • responseShear w
  inv := 1-t • responseShear w
  val_inv := by
    apply ContinuousLinearMap.ext
    intro f
    change (f-t • responseShear w f)+t • responseShear w (f-t • responseShear w f) = f
    rw [map_sub,map_smul,responseShear_twice,smul_zero,sub_zero]
    abel
  inv_val := by
    apply ContinuousLinearMap.ext
    intro f
    change (f+t • responseShear w f)-t • responseShear w (f+t • responseShear w f) = f
    rw [map_add,map_smul,responseShear_twice,smul_zero,add_zero]
    abel

private theorem remainder_responseShear {w : ℂ} (hw : 0 < w.re) :
    responseShear w+remainder w*responseShear w = constantProjection := by
  apply ContinuousLinearMap.ext
  intro f
  change f.1 zeroPoint • response w+remainder w (f.1 zeroPoint • response w) =
    constant (f.1 zeroPoint)
  rw [map_smul,← smul_add,remainder_response hw]
  have hu : response w+(constant 1-response w) = constant 1 := by abel
  rw [hu]
  apply Subtype.ext
  ext z
  change f.1 zeroPoint*1 = f.1 zeroPoint
  exact mul_one _

/-- Every scalar constant-mode perturbation has an exact right unipotent factorization. -/
theorem perturbed_factorization {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    (1+remainder w)*(1+t • responseShear w) = 1+remainder w+t • constantProjection := by
  rw [mul_add,mul_one,mul_smul_comm,add_mul,one_mul,remainder_responseShear hw]

/-- Source pole subtraction is an actual bounded-operator factorization through the successor shear. -/
theorem source_factorization {w : ℂ} (hw : 0 < w.re) :
    1+source w = (1+remainder w)*(1+riemannZeta w • responseShear w) := by
  rw [perturbed_factorization hw,source]
  abel

/-- Scalar constant-mode perturbation preserves invertibility throughout the complex source half-plane. -/
theorem perturbed_isUnit_iff {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    IsUnit (1+remainder w+t • constantProjection) ↔ IsUnit (1+remainder w) := by
  have hu : IsUnit (1+t • responseShear w) := ⟨responseShearUnit w t,rfl⟩
  have hi : IsUnit (1-t • responseShear w) := ⟨(responseShearUnit w t)⁻¹,rfl⟩
  constructor
  · intro h
    have hh := h.mul hi
    have he : (1+remainder w+t • constantProjection)*(1-t • responseShear w) =
        1+remainder w := by
      have hinv : (1+t • responseShear w)*(1-t • responseShear w) = 1 :=
        (responseShearUnit w t).val_inv
      rw [← perturbed_factorization hw t,mul_assoc,hinv,mul_one]
    rwa [he] at hh
  · intro h
    rw [← perturbed_factorization hw t]
    exact h.mul hu

#print axioms responseShear_twice
#print axioms perturbed_factorization
#print axioms source_factorization
#print axioms perturbed_isUnit_iff
/-- The actual remainder is invertible at the negative unit for every positive real source. -/
theorem remainder_isUnit_real {w : ℝ} (hw : 0 < w) : IsUnit (1+remainder (w : ℂ)) := by
  have hwc : 0 < (w : ℂ).re := hw
  have hd := MayerNegativePole.sourceDeterminant_negative_one_ne_zero hw
  rw [sourceDeterminant_eq hwc] at hd
  have hs : IsUnit (1+source (w : ℂ)) := by
    by_contra hn
    apply hd
    apply (MayerFredholm.determinant_eq_zero_iff_not_isUnit hwc (-1)).mpr
    simpa only [neg_smul,one_smul,sub_neg_eq_add,← source_eq hwc] using hn
  have he : 1+source (w : ℂ) =
      1+remainder (w : ℂ)+riemannZeta (w : ℂ) • constantProjection := by
    rw [source]
    abel
  rw [he] at hs
  exact (perturbed_isUnit_iff hwc (riemannZeta (w : ℂ))).mp hs

/-- Ring inversion of the pole-free remainder family. -/
def remainderInverse (w : ℂ) : DiscSpace →L[ℂ] DiscSpace := Ring.inverse (1+remainder w)

/-- Ring inversion of the actual source family at the negative unit. -/
def sourceInverse (w : ℂ) : DiscSpace →L[ℂ] DiscSpace := Ring.inverse (1+source w)

private theorem perturbed_inverse_of_isUnit {w : ℂ} (hw : 0 < w.re)
    (hu : IsUnit (1+remainder w)) (t : ℂ) :
    Ring.inverse (1+remainder w+t • constantProjection) =
      (1-t • responseShear w)*remainderInverse w := by
  obtain ⟨u,hu⟩ := hu
  unfold remainderInverse
  rw [← perturbed_factorization hw t,← hu]
  change Ring.inverse ((u*responseShearUnit w t : (DiscSpace →L[ℂ] DiscSpace)ˣ) :
    DiscSpace →L[ℂ] DiscSpace) =
      (((responseShearUnit w t)⁻¹ : (DiscSpace →L[ℂ] DiscSpace)ˣ) :
        DiscSpace →L[ℂ] DiscSpace)*Ring.inverse (u : DiscSpace →L[ℂ] DiscSpace)
  rw [Ring.inverse_unit,Ring.inverse_unit]
  rfl

/-- Exact inverse for every scalar constant-mode perturbation of a positive real source. -/
theorem perturbed_inverse_real {w : ℝ} (hw : 0 < w) (t : ℂ) :
    Ring.inverse (1+remainder (w : ℂ)+t • constantProjection) =
      (1-t • responseShear (w : ℂ))*remainderInverse (w : ℂ) :=
  perturbed_inverse_of_isUnit (w := (w : ℂ)) hw (remainder_isUnit_real hw) t

private theorem remainderInverse_mul_of_isUnit {w : ℂ} (hu : IsUnit (1+remainder w)) :
    remainderInverse w*(1+remainder w) = 1 := by
  obtain ⟨u,hu⟩ := hu
  unfold remainderInverse
  rw [← hu,Ring.inverse_unit]
  exact u.inv_val

private theorem entireBranch_one_constant (w : ℂ) :
    entireBranch w 1 le_rfl (constant 1) = constant 1-response w := by
  apply Subtype.ext
  ext z
  rw [entireBranch_apply]
  simp only [Nat.cast_one]
  have hu : (1+z.1)⁻¹ ∈ outer := by
    have hi : (1+z.1)⁻¹ ∈ closedBall (1 : ℂ) 1 := by
      simpa only [Nat.cast_one] using inverse_branch_inner (n := 1) le_rfl z.property
    exact closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hi
  have hp : plane (constant 1) ((1+z.1)⁻¹) = 1 :=
    plane_eq (constant 1) ⟨(1+z.1)⁻¹,hu⟩
  rw [hp]
  change (1+z.1)^(-w)*1 = 1-(response w).1 z
  rw [response_apply]
  ring

/-- The actual response is an entire branch remainder applied to the constant function. -/
theorem response_eq_entireRemainder (w : ℂ) : response w = -(entireRemainder 0 w (constant 1)) := by
  have he : entireRemainder 0 w = entireBranch w 1 le_rfl-constantProjection := by
    simp only [entireRemainder,zero_add,Nat.cast_one,Complex.one_cpow,one_smul]
  rw [he,sub_apply,entireBranch_one_constant]
  change response w = -((constant 1-response w)-constant 1)
  abel

/-- Entire dependence of the actual successor response on its source parameter. -/
theorem differentiable_response : Differentiable ℂ response := by
  have h := (ContinuousLinearMap.apply ℂ DiscSpace (constant 1)).differentiable.comp
    (differentiable_entireRemainder 0)
  have he : response = fun w => -(entireRemainder 0 w (constant 1)) :=
    funext response_eq_entireRemainder
  rw [he]
  exact h.neg

/-- The nilpotent response shear varies holomorphically in the full source plane. -/
theorem differentiable_responseShear : Differentiable ℂ responseShear := by
  have h := (ContinuousLinearMap.smulRightL ℂ DiscSpace DiscSpace (evaluation zeroPoint)).differentiable.comp
    differentiable_response
  exact h

private theorem analyticAt_remainderSum_one :
    AnalyticAt ℂ (fun w => (1 : DiscSpace →L[ℂ] DiscSpace)+remainder w) 1 := by
  have hr : AnalyticAt ℂ remainder (1 : ℂ) := differentiableOn_remainder.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
  exact analyticAt_const.add hr

/-- The pole-free inverse is holomorphic near the actual source pole. -/
theorem analyticAt_remainderInverse_one : AnalyticAt ℂ remainderInverse 1 := by
  have hu : IsUnit (1+remainder (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using remainder_isUnit_real (w := 1) (by norm_num)
  exact (analyticOnNhd_inverse (𝕜 := ℂ) (1+remainder (1 : ℂ)) hu).comp
    (f := fun w : ℂ => (1 : DiscSpace →L[ℂ] DiscSpace)+remainder w) (x := 1)
    analyticAt_remainderSum_one

private theorem eventually_remainder_unit :
    ∀ᶠ w : ℂ in 𝓝 1, IsUnit (1+remainder w) := by
  have hu : IsUnit (1+remainder (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using remainder_isUnit_real (w := 1) (by norm_num)
  exact analyticAt_remainderSum_one.continuousAt (Units.isOpen.mem_nhds hu)

/-- The actual inverse splits into a holomorphic part and one explicit zeta rank-one term near one. -/
theorem sourceInverse_eventually_eq :
    ∀ᶠ w : ℂ in 𝓝 1,
      sourceInverse w = remainderInverse w-
        riemannZeta w • (responseShear w*remainderInverse w) := by
  have hhalf : ∀ᶠ w : ℂ in 𝓝 1, 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [eventually_remainder_unit,hhalf] with w hu hw
  have he : 1+source w = 1+remainder w+riemannZeta w • constantProjection := by
    rw [source]
    abel
  rw [sourceInverse,he,perturbed_inverse_of_isUnit hw hu,sub_mul,one_mul,smul_mul_assoc]

/-- The signed product retains a genuine simple source pole. -/
theorem signed_source_product_simple_pole :
    meromorphicOrderAt (fun w => sourceDeterminant w (-1)*sourceDeterminant w 1) 1 = -1 := by
  have hn : sourceDeterminant 1 (-1) ≠ 0 := by
    simpa only [Complex.ofReal_one] using
      MayerNegativePole.sourceDeterminant_negative_one_ne_zero (w := 1) (by norm_num)
  have he : meromorphicOrderAt ((fun w => sourceDeterminant w (-1))*(fun w => sourceDeterminant w 1)) 1 =
      meromorphicOrderAt (fun w => sourceDeterminant w 1) 1 :=
    meromorphicOrderAt_mul_of_ne_zero analyticAt_sourceDeterminant_negative_one hn
  exact he.trans MayerPositivePole.sourceDeterminant_one_simple_pole

#print axioms remainder_isUnit_real
#print axioms perturbed_inverse_real
#print axioms response_eq_entireRemainder
#print axioms differentiable_responseShear
#print axioms analyticAt_remainderInverse_one
#print axioms sourceInverse_eventually_eq
#print axioms signed_source_product_simple_pole

private theorem response_ne_zero {w : ℂ} (hw : 0 < w.re) : response w ≠ 0 := by
  intro hz
  have h := remainder_response hw
  rw [hz,map_zero,sub_zero] at h
  have h0 := congrArg (fun f : DiscSpace => f.1 zeroPoint) h
  change (0 : ℂ) = 1 at h0
  exact zero_ne_one h0

private theorem responseShear_inverse_ne_zero {w : ℂ} (hw : 0 < w.re)
    (hu : IsUnit (1+remainder w)) : responseShear w*remainderInverse w ≠ 0 := by
  intro hz
  have h := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T ((1+remainder w) (constant 1))) hz
  change responseShear w (remainderInverse w ((1+remainder w) (constant 1))) = 0 at h
  have hg := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (constant 1))
    (remainderInverse_mul_of_isUnit hu)
  change remainderInverse w ((1+remainder w) (constant 1)) = constant 1 at hg
  rw [hg,responseShear_apply] at h
  change (1 : ℂ) • response w = 0 at h
  rw [one_smul] at h
  exact response_ne_zero hw h

/-- The explicit rank-one residue of the actual inverse at the source pole. -/
def inversePoleResidue : DiscSpace →L[ℂ] DiscSpace :=
  -(responseShear 1*remainderInverse 1)

/-- The inverse residue is exactly one response vector times one transported evaluation functional. -/
theorem inversePoleResidue_rank_one : inversePoleResidue =
    ((evaluation zeroPoint).comp (remainderInverse 1)).smulRight (-(response 1)) := by
  apply ContinuousLinearMap.ext
  intro f
  change -((remainderInverse 1 f).1 zeroPoint • response 1) =
    (remainderInverse 1 f).1 zeroPoint • (-(response 1))
  exact (smul_neg _ _).symm

/-- The source inverse residue is genuinely nonzero. -/
theorem inversePoleResidue_ne_zero : inversePoleResidue ≠ 0 := by
  have hu : IsUnit (1+remainder (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using remainder_isUnit_real (w := 1) (by norm_num)
  exact neg_ne_zero.mpr (responseShear_inverse_ne_zero (w := 1) (by norm_num) hu)

/-- A holomorphic numerator for the actual inverse near the source pole. -/
def clearedSourceInverse (w : ℂ) : DiscSpace →L[ℂ] DiscSpace :=
  (w-1) • remainderInverse w-
    _root_.RHTower.zetaResidueUnit w • (responseShear w*remainderInverse w)

/-- Removing the scalar source pole makes the inverse holomorphic across one. -/
theorem analyticAt_clearedSourceInverse_one : AnalyticAt ℂ clearedSourceInverse 1 := by
  have hg := analyticAt_remainderInverse_one
  have hf : AnalyticAt ℂ responseShear (1 : ℂ) := differentiable_responseShear.analyticAt 1
  exact ((analyticAt_id.sub analyticAt_const).smul hg).sub
    ((_root_.RHTower.analyticAt_zetaResidueUnit 1).smul (hf.mul hg))

theorem clearedSourceInverse_one : clearedSourceInverse 1 = inversePoleResidue := by
  simp only [clearedSourceInverse,sub_self,zero_smul,_root_.RHTower.zetaResidueUnit_one,
    one_smul,zero_sub,inversePoleResidue]

private theorem clearedSourceInverse_eventually_eq :
    ∀ᶠ w : ℂ in 𝓝[≠] 1, clearedSourceInverse w = (w-1) • sourceInverse w := by
  have he : ∀ᶠ w : ℂ in 𝓝[≠] 1, sourceInverse w = remainderInverse w-
      riemannZeta w • (responseShear w*remainderInverse w) :=
    nhdsWithin_le_nhds sourceInverse_eventually_eq
  filter_upwards [he,self_mem_nhdsWithin] with w hw hw1
  rw [clearedSourceInverse,hw,_root_.RHTower.zetaResidueUnit,Function.update_of_ne hw1,
    smul_sub,smul_smul]

/-- The actual negative-unit inverse has the displayed nonzero rank-one Laurent residue. -/
theorem sourceInverse_residue :
    Tendsto (fun w : ℂ => (w-1) • sourceInverse w) (𝓝[≠] 1) (𝓝 inversePoleResidue) := by
  have h : Tendsto clearedSourceInverse (𝓝[≠] 1) (𝓝 (clearedSourceInverse 1)) :=
    analyticAt_clearedSourceInverse_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [clearedSourceInverse_one] at h
  exact h.congr' clearedSourceInverse_eventually_eq

/-- Holomorphy and nonvanishing of the determinant do not remove the actual inverse's source pole. -/
theorem not_continuousAt_sourceInverse_one : ¬ ContinuousAt sourceInverse (1 : ℂ) := by
  intro hc
  have hz : Tendsto (fun w : ℂ => w-1) (𝓝[≠] 1) (𝓝 0) := by
    have h : Continuous (fun w : ℂ => w-1) := continuous_id.sub continuous_const
    simpa only [sub_self] using (h.tendsto 1).mono_left nhdsWithin_le_nhds
  have hs := hz.smul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hs' : Tendsto (fun w : ℂ => (w-1) • sourceInverse w) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [zero_smul] using hs
  exact inversePoleResidue_ne_zero (tendsto_nhds_unique sourceInverse_residue hs')

#print axioms inversePoleResidue_rank_one
#print axioms inversePoleResidue_ne_zero
#print axioms analyticAt_clearedSourceInverse_one
#print axioms sourceInverse_residue
#print axioms not_continuousAt_sourceInverse_one

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerResolvent
