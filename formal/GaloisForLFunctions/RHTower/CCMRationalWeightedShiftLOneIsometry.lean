import GaloisForLFunctions.RHTower.CCMRationalWeightedShiftTraceNormBound
import GaloisForLFunctions.RHTower.CCMRationalMoritaTraceNormAlgebra

/-!
# The rational weighted-shift `ℓ1` isometry

For every fixed rational scaling label `k`, the weighted-shift representation identifies
`ℓ1(ℚˣ)` linearly and isometrically with a closed subspace of the genuine Schatten-`1`
Morita ideal on `ℓ2(ℚˣ)`.  Thus trace-norm continuity of a fixed-label CCM monomial is
*equivalent* to ordinary `ℓ1` continuity of its orbit coefficient.

This is the reusable analytic interface for the full class-space source landing.  It contains no
choice of topology on the adelic source and no continuity hypothesis hidden in the operator
construction.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev H := CCMRationalMoritaHilbert
private abbrev Op := H →L[ℂ] H

/-- Genuine `ℓ1(ℚˣ)` coefficient space for rational CCM weighted shifts. -/
abbrev CCMRationalMoritaLOneCoefficient :=
  lp (fun _ : CCMRationalUnit => ℂ) 1

theorem ccmRationalMoritaLOneCoefficient_summable
    (a : CCMRationalMoritaLOneCoefficient) :
    Summable (fun q => ‖a q‖) := by
  simpa using (lp.memℓp a).summable (by norm_num)

/-- The native `lp` norm at exponent one is the literal sum of coefficient norms. -/
theorem ccmRationalMoritaLOneCoefficient_norm_eq_tsum
    (a : CCMRationalMoritaLOneCoefficient) :
    ‖a‖ = ∑' q, ‖a q‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := (1 : ENNReal)) (by norm_num) a

/-- Underlying bounded weighted shift of an `ℓ1` coefficient. -/
def ccmRationalMoritaLOneWeightedShiftOperator
    (k : CCMRationalUnit) (a : CCMRationalMoritaLOneCoefficient) : Op :=
  ccmRationalMoritaWeightedShift (fun q => a q) k
    ‖a‖ (norm_nonneg a)
    (fun q => lp.norm_apply_le_norm (by norm_num) a q)

theorem ccmRationalMoritaLOneWeightedShiftOperator_isTraceClass
    (k : CCMRationalUnit) (a : CCMRationalMoritaLOneCoefficient) :
    (ccmRationalMoritaLOneWeightedShiftOperator k a).IsTraceClass := by
  exact ccmRationalMoritaWeightedShift_isTraceClass_of_summable
    (fun q => a q) k ‖a‖ (norm_nonneg a)
    (fun q => lp.norm_apply_le_norm (by norm_num) a q)
    (ccmRationalMoritaLOneCoefficient_summable a)

/-- Trace-norm operator represented by an `ℓ1` coefficient at fixed shift label. -/
def ccmRationalMoritaLOneWeightedShift
    (k : CCMRationalUnit) (a : CCMRationalMoritaLOneCoefficient) :
    CCMRationalMoritaTraceNormOperator :=
  ⟨⟨ccmRationalMoritaLOneWeightedShiftOperator k a,
    ccmRationalMoritaLOneWeightedShiftOperator_isTraceClass k a⟩⟩

@[simp]
theorem ccmRationalMoritaLOneWeightedShift_toOperator
    (k : CCMRationalUnit) (a : CCMRationalMoritaLOneCoefficient) :
    ((ccmRationalMoritaLOneWeightedShift k a).toTraceClass : Op) =
      ccmRationalMoritaLOneWeightedShiftOperator k a :=
  rfl

@[simp]
theorem ccmRationalMoritaLOneWeightedShift_zero (k : CCMRationalUnit) :
    ccmRationalMoritaLOneWeightedShift k 0 = 0 := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  ext q
  simp [ccmRationalMoritaLOneWeightedShift,
    ccmRationalMoritaLOneWeightedShiftOperator,
    ccmRationalMoritaWeightedShift_apply]

@[simp]
theorem ccmRationalMoritaLOneWeightedShift_add
    (k : CCMRationalUnit)
    (a d : CCMRationalMoritaLOneCoefficient) :
    ccmRationalMoritaLOneWeightedShift k (a + d) =
      ccmRationalMoritaLOneWeightedShift k a +
        ccmRationalMoritaLOneWeightedShift k d := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  ext q
  change (a q + d q) * f (k⁻¹ * q) =
    a q * f (k⁻¹ * q) + d q * f (k⁻¹ * q)
  ring

@[simp]
theorem ccmRationalMoritaLOneWeightedShift_smul
    (k : CCMRationalUnit) (z : ℂ)
    (a : CCMRationalMoritaLOneCoefficient) :
    ccmRationalMoritaLOneWeightedShift k (z • a) =
      z • ccmRationalMoritaLOneWeightedShift k a := by
  apply CCMRationalMoritaTraceNormOperator.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  ext q
  change (z * a q) * f (k⁻¹ * q) =
    z * (a q * f (k⁻¹ * q))
  ring

/-- Linear weighted-shift representation on genuine `ℓ1` coefficients. -/
def ccmRationalMoritaLOneWeightedShiftLinear
    (k : CCMRationalUnit) :
    CCMRationalMoritaLOneCoefficient →ₗ[ℂ]
      CCMRationalMoritaTraceNormOperator where
  toFun := ccmRationalMoritaLOneWeightedShift k
  map_add' := ccmRationalMoritaLOneWeightedShift_add k
  map_smul' := ccmRationalMoritaLOneWeightedShift_smul k

/-- **Exact `ℓ1`--Schatten-`1` conservation law.** -/
@[simp]
theorem ccmRationalMoritaLOneWeightedShift_norm
    (k : CCMRationalUnit) (a : CCMRationalMoritaLOneCoefficient) :
    ‖ccmRationalMoritaLOneWeightedShift k a‖ = ‖a‖ := by
  change _root_.RHTower.traceNorm H
      (ccmRationalMoritaLOneWeightedShiftOperator k a) = ‖a‖
  rw [ccmRationalMoritaLOneWeightedShiftOperator,
    ccmRationalMoritaWeightedShift_traceNorm_eq_lOne
      (fun q => a q) k ‖a‖ (norm_nonneg a)
      (fun q => lp.norm_apply_le_norm (by norm_num) a q)
      (ccmRationalMoritaLOneCoefficient_summable a),
    ← ccmRationalMoritaLOneCoefficient_norm_eq_tsum]

/-- Fixed-label rational weighted shifts form a linear isometric copy of `ℓ1(ℚˣ)` in the
actual trace-norm Morita ideal. -/
def ccmRationalMoritaLOneWeightedShiftLinearIsometry
    (k : CCMRationalUnit) :
    CCMRationalMoritaLOneCoefficient →ₗᵢ[ℂ]
      CCMRationalMoritaTraceNormOperator where
  toLinearMap := ccmRationalMoritaLOneWeightedShiftLinear k
  norm_map' := ccmRationalMoritaLOneWeightedShift_norm k

/-- Exact metric form of the fixed-label transport law. -/
theorem ccmRationalMoritaLOneWeightedShift_dist
    (k : CCMRationalUnit)
    (a d : CCMRationalMoritaLOneCoefficient) :
    dist (ccmRationalMoritaLOneWeightedShift k a)
        (ccmRationalMoritaLOneWeightedShift k d) = dist a d := by
  rw [dist_eq_norm, dist_eq_norm,
    show ccmRationalMoritaLOneWeightedShift k a -
        ccmRationalMoritaLOneWeightedShift k d =
      ccmRationalMoritaLOneWeightedShift k (a - d) by
        exact ((ccmRationalMoritaLOneWeightedShiftLinear k).map_sub a d).symm]
  exact ccmRationalMoritaLOneWeightedShift_norm k (a - d)

end RHTower
end GaloisForLFunctions
