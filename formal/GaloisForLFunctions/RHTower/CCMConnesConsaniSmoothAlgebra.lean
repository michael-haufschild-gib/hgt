import GaloisForLFunctions.RHTower.CCMConnesConsaniSmoothCommutator
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import Mathlib.Algebra.Star.StarAlgHom

/-!
# The represented smooth circle algebra in Connes--Consani's spectral triple

This file closes the algebra-action layer of Connes--Consani's Proposition propDpert.
Smooth periodic functions form an exact star subalgebra; multiplication on L2 is transported
through the Fourier unitary as a faithful unital star-algebra representation. Faithfulness follows
from positivity of Haar measure on nonempty open sets, rather than an assumption.
-/

open Module Topology Filter
open MeasureTheory
open scoped InnerProductSpace

namespace RHTower

open HilbertSchmidt GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance (L : CCMCircleLength) : Fact (0 < (L : ℝ)) := ⟨L.property⟩

def CCMSmoothPeriodicAlgebra (T : ℝ) : StarSubalgebra ℂ (ℝ → ℂ) where
  toSubalgebra := {
    carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ Function.Periodic f T}
    zero_mem' := ⟨contDiff_const, fun _ => rfl⟩
    add_mem' := by
      rintro f g ⟨hfd, hfp⟩ ⟨hgd, hgp⟩
      exact ⟨hfd.add hgd, hfp.add hgp⟩
    one_mem' := ⟨contDiff_const, fun _ => rfl⟩
    mul_mem' := by
      rintro f g ⟨hfd, hfp⟩ ⟨hgd, hgp⟩
      exact ⟨hfd.mul hgd, hfp.mul hgp⟩
    algebraMap_mem' := by
      intro c
      exact ⟨contDiff_const, fun _ => rfl⟩ }
  star_mem' := by
    rintro f ⟨hfd, hfp⟩
    have hconj : ContDiff ℝ (⊤ : ℕ∞) (starRingEnd ℂ : ℂ → ℂ) := by
      have heq : (starRingEnd ℂ : ℂ → ℂ) = (Complex.conjCLE : ℂ → ℂ) := by
        funext z
        rfl
      rw [heq]
      exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff
    refine ⟨hconj.comp hfd, fun x => ?_⟩
    change (starRingEnd ℂ) (f (x + T)) = (starRingEnd ℂ) (f x)
    rw [hfp x]

def ccmSmoothPeriodicAlgebraToDeninger {T : ℝ}
    (a : CCMSmoothPeriodicAlgebra T) : DeningerSmoothPeriodic T :=
  ⟨(a : ℝ → ℂ), a.property⟩

@[simp] theorem ccmSmoothPeriodicAlgebraToDeninger_coe {T : ℝ}
    (a : CCMSmoothPeriodicAlgebra T) :
    (ccmSmoothPeriodicAlgebraToDeninger a : ℝ → ℂ) = a := rfl

theorem ccmSmoothCircleFunction_mul (L : CCMCircleLength)
    (a b : CCMSmoothPeriodicAlgebra (L : ℝ)) (x : AddCircle (L : ℝ)) :
    ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger (a * b)) x =
      ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) x *
        ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger b) x := by
  rfl

theorem ccmSmoothCircleFunction_add (L : CCMCircleLength)
    (a b : CCMSmoothPeriodicAlgebra (L : ℝ)) (x : AddCircle (L : ℝ)) :
    ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger (a + b)) x =
      ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) x +
        ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger b) x := by
  rfl

theorem ccmSmoothCircleFunction_smul (L : CCMCircleLength) (c : ℂ)
    (a : CCMSmoothPeriodicAlgebra (L : ℝ)) (x : AddCircle (L : ℝ)) :
    ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger (c • a)) x =
      c * ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) x := by
  rfl

theorem ccmSmoothCircleFunction_star (L : CCMCircleLength)
    (a : CCMSmoothPeriodicAlgebra (L : ℝ)) (x : AddCircle (L : ℝ)) :
    ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger (star a)) x =
      (starRingEnd ℂ)
        (ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) x) := by
  rfl

theorem ccmSmoothCirclePhysicalMultiplier_mul (L : CCMCircleLength)
    (a b : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a)).comp
        (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger b)) =
      ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (a * b)) := by
  apply lpBoundedMulCLM_comp
  exact Filter.Eventually.of_forall fun x =>
    (ccmSmoothCircleFunction_mul L a b x).symm

theorem ccmSmoothCirclePhysicalMultiplier_one (L : CCMCircleLength) :
    ccmSmoothCirclePhysicalMultiplier L
        (ccmSmoothPeriodicAlgebraToDeninger (1 : CCMSmoothPeriodicAlgebra (L : ℝ))) =
      ContinuousLinearMap.id ℂ (CCMCirclePhysicalL2 L) := by
  apply lpBoundedMulCLM_eq_id
  exact Filter.Eventually.of_forall fun _ => rfl

theorem ccmSmoothCirclePhysicalMultiplier_zero (L : CCMCircleLength) :
    ccmSmoothCirclePhysicalMultiplier L
        (ccmSmoothPeriodicAlgebraToDeninger (0 : CCMSmoothPeriodicAlgebra (L : ℝ))) = 0 := by
  apply lpBoundedMulCLM_eq_zero
  exact Filter.Eventually.of_forall fun _ => rfl

theorem ccmSmoothCirclePhysicalMultiplier_add (L : CCMCircleLength)
    (a b : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (a + b)) =
      ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) +
        ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger b) := by
  apply lpBoundedMulCLM_add
  exact Filter.Eventually.of_forall fun x => ccmSmoothCircleFunction_add L a b x

theorem ccmSmoothCirclePhysicalMultiplier_smul (L : CCMCircleLength) (c : ℂ)
    (a : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (c • a)) =
      c • ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) := by
  apply lpBoundedMulCLM_smul
  exact Filter.Eventually.of_forall fun x => ccmSmoothCircleFunction_smul L c a x

theorem ccmSmoothCirclePhysicalMultiplier_star (L : CCMCircleLength)
    (a : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (star a)) =
      ContinuousLinearMap.adjoint
        (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a)) := by
  apply lpBoundedMulCLM_eq_adjoint_conj_general
  exact ccmSmoothCircleFunction_star L a

theorem ccmSmoothCircleMultiplier_zero (L : CCMCircleLength) :
    ccmSmoothCircleMultiplier L
        (ccmSmoothPeriodicAlgebraToDeninger (0 : CCMSmoothPeriodicAlgebra (L : ℝ))) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv
      (ccmSmoothCirclePhysicalMultiplier L
        (ccmSmoothPeriodicAlgebraToDeninger (0 : CCMSmoothPeriodicAlgebra (L : ℝ)))
          ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm x)) = 0
  rw [ccmSmoothCirclePhysicalMultiplier_zero]
  simp

theorem ccmSmoothCircleMultiplier_one (L : CCMCircleLength) :
    ccmSmoothCircleMultiplier L
        (ccmSmoothPeriodicAlgebraToDeninger (1 : CCMSmoothPeriodicAlgebra (L : ℝ))) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv
      (ccmSmoothCirclePhysicalMultiplier L
        (ccmSmoothPeriodicAlgebraToDeninger (1 : CCMSmoothPeriodicAlgebra (L : ℝ)))
          ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm x)) = x
  rw [ccmSmoothCirclePhysicalMultiplier_one]
  simp

theorem ccmSmoothCircleMultiplier_add (L : CCMCircleLength)
    (a b : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (a + b)) =
      ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) +
        ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger b) := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv
      (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (a + b))
        ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm x)) = _
  rw [ccmSmoothCirclePhysicalMultiplier_add]
  simp [ccmSmoothCircleMultiplier]

theorem ccmSmoothCircleMultiplier_smul (L : CCMCircleLength) (c : ℂ)
    (a : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (c • a)) =
      c • ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv
      (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (c • a))
        ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm x)) = _
  rw [ccmSmoothCirclePhysicalMultiplier_smul]
  simp [ccmSmoothCircleMultiplier]

theorem ccmSmoothCircleMultiplier_mul (L : CCMCircleLength)
    (a b : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (a * b)) =
      ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) *
        ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger b) := by
  apply ContinuousLinearMap.ext
  intro x
  change (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv
      (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (a * b))
        ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.symm x)) = _
  rw [← ccmSmoothCirclePhysicalMultiplier_mul]
  simp [ccmSmoothCircleMultiplier, mul_apply_eq_comp]

theorem ccmSmoothCircleMultiplier_star (L : CCMCircleLength)
    (a : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger (star a)) =
      star (ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let U := (fourierBasis (T := (L : ℝ))).repr
  let Mstar := ccmSmoothCirclePhysicalMultiplier L
    (ccmSmoothPeriodicAlgebraToDeninger (star a))
  let M := ccmSmoothCirclePhysicalMultiplier L
    (ccmSmoothPeriodicAlgebraToDeninger a)
  change inner ℂ (U (Mstar (U.symm x))) y =
    inner ℂ x (U (M (U.symm y)))
  calc
    inner ℂ (U (Mstar (U.symm x))) y =
        inner ℂ (Mstar (U.symm x)) (U.symm y) :=
      U.inner_map_eq_flip _ _
    _ = inner ℂ (U.symm x) (M (U.symm y)) := by
      dsimp only [Mstar, M]
      rw [ccmSmoothCirclePhysicalMultiplier_star,
        ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ x (U (M (U.symm y))) := by
      simpa using U.symm.inner_map_eq_flip x (M (U.symm y))

noncomputable def ccmSmoothPeriodicAlgebraRepresentation (L : CCMCircleLength) :
    CCMSmoothPeriodicAlgebra (L : ℝ) →⋆ₐ[ℂ]
      (DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ) where
  toFun a := ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a)
  map_one' := ccmSmoothCircleMultiplier_one L
  map_mul' := ccmSmoothCircleMultiplier_mul L
  map_zero' := ccmSmoothCircleMultiplier_zero L
  map_add' := ccmSmoothCircleMultiplier_add L
  commutes' c := by
    have hscalar : (algebraMap ℂ (CCMSmoothPeriodicAlgebra (L : ℝ)) c) =
        c • (1 : CCMSmoothPeriodicAlgebra (L : ℝ)) := by
      simpa using
        (Algebra.smul_def c (1 : CCMSmoothPeriodicAlgebra (L : ℝ))).symm
    rw [hscalar, ccmSmoothCircleMultiplier_smul,
      ccmSmoothCircleMultiplier_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm
  map_star' := ccmSmoothCircleMultiplier_star L

private theorem ccmSmoothCirclePhysicalMultiplier_eq_zero_of_multiplier_eq_zero
    (L : CCMCircleLength) (a : CCMSmoothPeriodicAlgebra (L : ℝ))
    (h : ccmSmoothCircleMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) = 0) :
    ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  have hy := congrArg
    (fun T : DiagonalL2 ℤ →L[ℂ] DiagonalL2 ℤ =>
      T ((fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv y)) h
  have hy' :
    (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv
        (ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) y) = 0 := by
    simpa [ccmSmoothCircleMultiplier] using hy
  exact (fourierBasis (T := (L : ℝ))).repr.toContinuousLinearEquiv.injective
    (by simpa using hy')

private theorem ccmSmoothCirclePhysicalMultiplier_apply_oneLp
    (L : CCMCircleLength) (a : CCMSmoothPeriodicAlgebra (L : ℝ)) :
    ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a)
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
          (1 : C(AddCircle (L : ℝ), ℂ))) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (ccmSmoothCircleContinuous L (ccmSmoothPeriodicAlgebraToDeninger a)) := by
  apply Lp.ext
  filter_upwards [lpBoundedMulCLM_coeFn
      (continuous_ccmSmoothCircleFunction L
        (ccmSmoothPeriodicAlgebraToDeninger a)).measurable
      (norm_nonneg (ccmSmoothCircleContinuous L
        (ccmSmoothPeriodicAlgebraToDeninger a)))
      (fun x => ContinuousMap.norm_coe_le_norm
        (ccmSmoothCircleContinuous L (ccmSmoothPeriodicAlgebraToDeninger a)) x)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (1 : C(AddCircle (L : ℝ), ℂ))),
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2)
      (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
      (1 : C(AddCircle (L : ℝ), ℂ)),
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2)
      (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
      (ccmSmoothCircleContinuous L (ccmSmoothPeriodicAlgebraToDeninger a))]
      with x hmul hone ha
  rw [show ccmSmoothCirclePhysicalMultiplier L (ccmSmoothPeriodicAlgebraToDeninger a) =
      lpBoundedMulCLM
        (continuous_ccmSmoothCircleFunction L
          (ccmSmoothPeriodicAlgebraToDeninger a)).measurable
        (norm_nonneg (ccmSmoothCircleContinuous L
          (ccmSmoothPeriodicAlgebraToDeninger a)))
        (fun x => ContinuousMap.norm_coe_le_norm
          (ccmSmoothCircleContinuous L (ccmSmoothPeriodicAlgebraToDeninger a)) x) by rfl]
  rw [hmul, hone, ha]
  change ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) x * 1 =
    ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) x
  simp

private theorem ccmSmoothPeriodicAlgebra_eq_zero_of_circleFunction_eq_zero
    (L : CCMCircleLength) (a : CCMSmoothPeriodicAlgebra (L : ℝ))
    (h : ccmSmoothCircleFunction L (ccmSmoothPeriodicAlgebraToDeninger a) = 0) :
    a = 0 := by
  apply Subtype.ext
  funext x
  obtain ⟨y, hy, hxy⟩ := a.property.2.exists_mem_Ioc L.property x 0
  rw [hxy]
  have hz := congrFun h (y : AddCircle (L : ℝ))
  change AddCircle.liftIoc (L : ℝ) 0 (a : ℝ → ℂ) (y : AddCircle (L : ℝ)) = 0 at hz
  have hy' : y ∈ Set.Ioc 0 (L : ℝ) := by simpa using hy
  rw [AddCircle.liftIoc_zero_coe_apply hy'] at hz
  simpa using hz

theorem ccmSmoothPeriodicAlgebraRepresentation_injective (L : CCMCircleLength) :
    Function.Injective (ccmSmoothPeriodicAlgebraRepresentation L) := by
  intro a b hab
  have hsub : ccmSmoothPeriodicAlgebraRepresentation L (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hphys := ccmSmoothCirclePhysicalMultiplier_eq_zero_of_multiplier_eq_zero L (a - b) hsub
  have hLp : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
      (ccmSmoothCircleContinuous L (ccmSmoothPeriodicAlgebraToDeninger (a - b))) = 0 := by
    rw [← ccmSmoothCirclePhysicalMultiplier_apply_oneLp]
    rw [hphys]
    rfl
  have hcont : ccmSmoothCircleContinuous L
      (ccmSmoothPeriodicAlgebraToDeninger (a - b)) = 0 := by
    apply ContinuousMap.toLp_injective (E := ℂ) (p := 2)
      (𝕜 := ℂ) AddCircle.haarAddCircle
    simpa using hLp
  have hcircle : ccmSmoothCircleFunction L
      (ccmSmoothPeriodicAlgebraToDeninger (a - b)) = 0 := by
    exact congrArg DFunLike.coe hcont
  have hz := ccmSmoothPeriodicAlgebra_eq_zero_of_circleFunction_eq_zero L (a - b) hcircle
  exact sub_eq_zero.mp hz

end
end RHTower
