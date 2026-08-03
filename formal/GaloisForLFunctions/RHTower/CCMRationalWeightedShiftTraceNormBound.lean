import GaloisForLFunctions.RHTower.CCMRationalWeightedShiftTraceClass
import GaloisForLFunctions.RHTower.TraceNormBound

/-!
# Sharp trace-norm bound for rational CCM weighted shifts

An `l1` coefficient `a` defines the rational Morita weighted shift `W_{a,k}`.  The existing
trace-class proof factors it into two Hilbert--Schmidt shifts built from square-root modulus and
phase.  Here we compute the Hilbert--Schmidt norms of those factors exactly and apply the sharp
Schatten Holder inequality.  This gives

`traceNorm(W_{a,k}) <= sum_q ||a q||`

and, for a fixed shift label,

`traceNorm(W_{a,k} - W_{d,k}) <= sum_q ||a q - d q||`.

The second estimate is the analytic bridge from `l1` orbit continuity to genuine Schatten-`1`
continuity of the CCM Morita field.  No compactness surrogate or operator-norm replacement is used.
-/

noncomputable section

open ContinuousLinearMap

namespace GaloisForLFunctions
namespace RHTower

private abbrev H := CCMRationalMoritaHilbert

/-- Exact Hilbert--Schmidt square norm of a rational weighted shift. -/
theorem ccmRationalMoritaWeightedShift_hsNormSq
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (hsq : Summable (fun q => ‖a q‖ ^ (2 : ℕ))) :
    ContinuousLinearMap.hsNormSq
        (ccmRationalMoritaWeightedShift a k C hC ha) =
      ∑' q, ‖a q‖ ^ (2 : ℕ) := by
  have hHS := ccmRationalMoritaWeightedShift_isHilbertSchmidt
    a k C hC ha hsq
  rw [ContinuousLinearMap.hsNormSq_eq hHS
    ccmRationalMoritaHilbertBasis]
  calc
    (∑' q, ‖ccmRationalMoritaWeightedShift a k C hC ha
        (ccmRationalMoritaHilbertBasis q)‖ ^ (2 : ℕ)) =
      ∑' q, ‖a (k * q)‖ ^ (2 : ℕ) := by
        apply tsum_congr
        intro q
        rw [ccmRationalMoritaWeightedShift_basis_norm]
    _ = ∑' q, ‖a q‖ ^ (2 : ℕ) := by
      simpa only [Function.comp_apply, mul_comm] using
        (Equiv.mulLeft k).tsum_eq (fun q => ‖a q‖ ^ (2 : ℕ))

/-- Exact Hilbert--Schmidt norm of a rational weighted shift. -/
theorem ccmRationalMoritaWeightedShift_hsNorm
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (hsq : Summable (fun q => ‖a q‖ ^ (2 : ℕ))) :
    ContinuousLinearMap.hsNorm
        (ccmRationalMoritaWeightedShift a k C hC ha) =
      Real.sqrt (∑' q, ‖a q‖ ^ (2 : ℕ)) := by
  rw [ContinuousLinearMap.hsNorm,
    ccmRationalMoritaWeightedShift_hsNormSq a k C hC ha hsq]

/-- **Sharp nuclear budget.**  The trace norm of a rational weighted shift is bounded by the
`l1` norm of its coefficient. -/
theorem ccmRationalMoritaWeightedShift_traceNorm_le_lOne
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (hsum : Summable (fun q => ‖a q‖)) :
    _root_.RHTower.traceNorm H
        (ccmRationalMoritaWeightedShift a k C hC ha) ≤
      ∑' q, ‖a q‖ := by
  let L := ccmRationalMoritaCoefficientLOneBound a
  let D := Real.sqrt L
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  let r := ccmRationalMoritaCoefficientSqrtNorm a
  let s := ccmRationalMoritaCoefficientSqrtPhase a
  have hr : ∀ q, ‖r q‖ ≤ D :=
    ccmRationalMoritaCoefficientSqrtNorm_bound hsum
  have hs : ∀ q, ‖s q‖ ≤ D :=
    ccmRationalMoritaCoefficientSqrtPhase_bound hsum
  let A := ccmRationalMoritaWeightedShift s 1 D hD hs
  let B := ccmRationalMoritaWeightedShift r k D hD hr
  have hsqR : Summable (fun q => ‖r q‖ ^ (2 : ℕ)) :=
    ccmRationalMoritaCoefficientSqrtNorm_summable_sq hsum
  have hsqS : Summable (fun q => ‖s q‖ ^ (2 : ℕ)) :=
    ccmRationalMoritaCoefficientSqrtPhase_summable_sq hsum
  have hA : A.IsHilbertSchmidt :=
    ccmRationalMoritaWeightedShift_isHilbertSchmidt s 1 D hD hs hsqS
  have hB : B.IsHilbertSchmidt :=
    ccmRationalMoritaWeightedShift_isHilbertSchmidt r k D hD hr hsqR
  have hfac :
      ccmRationalMoritaWeightedShift a k C hC ha = A ∘L B := by
    apply ContinuousLinearMap.ext
    intro f
    ext q
    simp only [ContinuousLinearMap.comp_apply, A, B,
      ccmRationalMoritaWeightedShift_apply]
    simp only [inv_one, one_mul]
    change a q * f (k⁻¹ * q) = s q * (r q * f (k⁻¹ * q))
    rw [← mul_assoc,
      ccmRationalMoritaCoefficientSqrtPhase_mul_sqrtNorm]
  have hsumR : (∑' q, ‖r q‖ ^ (2 : ℕ)) = L := by
    apply tsum_congr
    intro q
    exact ccmRationalMoritaCoefficientSqrtNorm_sq a q
  have hsumS : (∑' q, ‖s q‖ ^ (2 : ℕ)) = L := by
    apply tsum_congr
    intro q
    exact ccmRationalMoritaCoefficientSqrtPhase_sq a q
  have hnormA : ContinuousLinearMap.hsNorm A = Real.sqrt L := by
    change ContinuousLinearMap.hsNorm
        (ccmRationalMoritaWeightedShift s 1 D hD hs) = Real.sqrt L
    rw [ccmRationalMoritaWeightedShift_hsNorm s 1 D hD hs hsqS,
      hsumS]
  have hnormB : ContinuousLinearMap.hsNorm B = Real.sqrt L := by
    change ContinuousLinearMap.hsNorm
        (ccmRationalMoritaWeightedShift r k D hD hr) = Real.sqrt L
    rw [ccmRationalMoritaWeightedShift_hsNorm r k D hD hr hsqR,
      hsumR]
  rw [hfac]
  calc
    _root_.RHTower.traceNorm H (A ∘L B) ≤
        ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B :=
      _root_.RHTower.tsum_approxNumber_comp_le hA hB
    _ = Real.sqrt L * Real.sqrt L := by rw [hnormA, hnormB]
    _ = L := Real.mul_self_sqrt
      (ccmRationalMoritaCoefficientLOneBound_nonneg a)
    _ = ∑' q, ‖a q‖ := rfl

/-- A weighted shift is independent of the chosen certified uniform bound. -/
theorem ccmRationalMoritaWeightedShift_congr_bound
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ q, ‖a q‖ ≤ C) (hd : ∀ q, ‖a q‖ ≤ D) :
    ccmRationalMoritaWeightedShift a k C hC ha =
      ccmRationalMoritaWeightedShift a k D hD hd := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  rfl

/-- Difference of two same-label shifts is the shift of the coefficient difference. -/
theorem ccmRationalMoritaWeightedShift_sub
    (a d : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ q, ‖a q‖ ≤ C) (hd : ∀ q, ‖d q‖ ≤ D) :
    ccmRationalMoritaWeightedShift a k C hC ha -
        ccmRationalMoritaWeightedShift d k D hD hd =
      ccmRationalMoritaWeightedShift (fun q => a q - d q) k
        (C + D) (add_nonneg hC hD) (fun q => by
          exact (norm_sub_le (a q) (d q)).trans (add_le_add (ha q) (hd q))) := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  simp only [sub_apply, ccmRationalMoritaWeightedShift_apply]
  change
    a q * f (k⁻¹ * q) - d q * f (k⁻¹ * q) =
      (a q - d q) * f (k⁻¹ * q)
  ring

/-- **Trace-norm Lipschitz law for fixed shift label.** -/
theorem ccmRationalMoritaWeightedShift_traceNorm_sub_le_lOne
    (a d : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ q, ‖a q‖ ≤ C) (hd : ∀ q, ‖d q‖ ≤ D)
    (hsumA : Summable (fun q => ‖a q‖))
    (hsumD : Summable (fun q => ‖d q‖)) :
    _root_.RHTower.traceNorm H
        (ccmRationalMoritaWeightedShift a k C hC ha -
          ccmRationalMoritaWeightedShift d k D hD hd) ≤
      ∑' q, ‖a q - d q‖ := by
  have hsumSub : Summable (fun q => ‖a q - d q‖) :=
    summable_norm_iff.mpr
      ((summable_norm_iff.mp hsumA).sub (summable_norm_iff.mp hsumD))
  rw [ccmRationalMoritaWeightedShift_sub]
  exact ccmRationalMoritaWeightedShift_traceNorm_le_lOne
    (fun q => a q - d q) k (C + D) (add_nonneg hC hD)
    (fun q => (norm_sub_le (a q) (d q)).trans
      (add_le_add (ha q) (hd q))) hsumSub

end RHTower
end GaloisForLFunctions
