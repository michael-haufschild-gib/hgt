import GaloisForLFunctions.RHTower.CCM.CCMRationalWeightedShiftReal

/-!
# Trace class from an absolutely summable rational CCM orbit

An `ℓ¹` coefficient is split pointwise into square-root norm and phase factors. Their weighted
shifts are Hilbert--Schmidt, so the original weighted shift is trace class.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

open ContinuousLinearMap

theorem ccmRationalMoritaWeightedShift_basis
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (q : CCMRationalUnit) :
    ccmRationalMoritaWeightedShift a k C hC ha
        (ccmRationalMoritaHilbertBasis q) =
      a (k * q) • ccmRationalMoritaHilbertBasis (k * q) := by
  ext r
  rw [ccmRationalMoritaWeightedShift_apply,
    ccmRationalMoritaHilbertBasis_apply,
    ccmRationalMoritaHilbertBasis_apply]
  change a r *
      (lp.single 2 q (1 : ℂ) : CCMRationalMoritaHilbert) (k⁻¹ * r) =
    a (k * q) *
      (lp.single 2 (k * q) (1 : ℂ) : CCMRationalMoritaHilbert) r
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : k * q = r
  · subst r
    simp
  · have h' : k⁻¹ * r ≠ q := by
      intro hkr
      apply h
      calc
        k * q = k * (k⁻¹ * r) := by rw [hkr]
        _ = r := by simp
    have hr : r ≠ k * q := by simpa [eq_comm] using h
    simp [h', hr]

theorem ccmRationalMoritaWeightedShift_basis_norm
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (q : CCMRationalUnit) :
    ‖ccmRationalMoritaWeightedShift a k C hC ha
        (ccmRationalMoritaHilbertBasis q)‖ =
      ‖a (k * q)‖ := by
  rw [ccmRationalMoritaWeightedShift_basis, norm_smul]
  simp [ccmRationalMoritaHilbertBasis_apply]

theorem ccmRationalMoritaWeightedShift_isHilbertSchmidt
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (hsq : Summable (fun q => ‖a q‖ ^ (2 : ℕ))) :
    (ccmRationalMoritaWeightedShift a k C hC ha).IsHilbertSchmidt := by
  apply ContinuousLinearMap.isHilbertSchmidt_of_summable
    ccmRationalMoritaHilbertBasis
  have ht :=
    (Equiv.mulLeft k).summable_iff.mpr hsq
  exact ht.congr (fun q => by
    dsimp only [Function.comp_apply]
    change ‖a (k * q)‖ ^ (2 : ℕ) =
      ‖ccmRationalMoritaWeightedShift a k C hC ha
        (ccmRationalMoritaHilbertBasis q)‖ ^ (2 : ℕ)
    rw [ccmRationalMoritaWeightedShift_basis_norm])

def ccmRationalMoritaCoefficientSqrtNorm
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) : ℂ :=
  (Real.sqrt ‖a q‖ : ℝ)

def ccmRationalMoritaCoefficientSqrtPhase
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) : ℂ :=
  if a q = 0 then 0 else a q / ccmRationalMoritaCoefficientSqrtNorm a q

theorem ccmRationalMoritaCoefficientSqrtNorm_norm
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) :
    ‖ccmRationalMoritaCoefficientSqrtNorm a q‖ =
      Real.sqrt ‖a q‖ := by
  simp [ccmRationalMoritaCoefficientSqrtNorm]

theorem ccmRationalMoritaCoefficientSqrtNorm_sq
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) :
    ‖ccmRationalMoritaCoefficientSqrtNorm a q‖ ^ (2 : ℕ) =
      ‖a q‖ := by
  rw [ccmRationalMoritaCoefficientSqrtNorm_norm,
    Real.sq_sqrt (norm_nonneg _)]

theorem ccmRationalMoritaCoefficientSqrtNorm_ne_zero
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit)
    (hq : a q ≠ 0) :
    ccmRationalMoritaCoefficientSqrtNorm a q ≠ 0 := by
  rw [ne_eq, ← norm_eq_zero]
  rw [ccmRationalMoritaCoefficientSqrtNorm_norm]
  exact (Real.sqrt_pos.2 (norm_pos_iff.mpr hq)).ne'

theorem ccmRationalMoritaCoefficientSqrtPhase_mul_sqrtNorm
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) :
    ccmRationalMoritaCoefficientSqrtPhase a q *
      ccmRationalMoritaCoefficientSqrtNorm a q = a q := by
  by_cases hq : a q = 0
  · simp [ccmRationalMoritaCoefficientSqrtPhase, hq]
  · rw [ccmRationalMoritaCoefficientSqrtPhase, if_neg hq]
    exact div_mul_cancel₀ (a q)
      (ccmRationalMoritaCoefficientSqrtNorm_ne_zero a q hq)

theorem ccmRationalMoritaCoefficientSqrtPhase_norm
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) :
    ‖ccmRationalMoritaCoefficientSqrtPhase a q‖ =
      Real.sqrt ‖a q‖ := by
  by_cases hq : a q = 0
  · simp [ccmRationalMoritaCoefficientSqrtPhase, hq]
  · rw [ccmRationalMoritaCoefficientSqrtPhase, if_neg hq, norm_div,
      ccmRationalMoritaCoefficientSqrtNorm_norm]
    have hsqrt : Real.sqrt ‖a q‖ ≠ 0 :=
      (Real.sqrt_pos.2 (norm_pos_iff.mpr hq)).ne'
    apply (div_eq_iff hsqrt).2
    nlinarith [Real.sq_sqrt (norm_nonneg (a q))]

theorem ccmRationalMoritaCoefficientSqrtPhase_sq
    (a : CCMRationalUnit → ℂ) (q : CCMRationalUnit) :
    ‖ccmRationalMoritaCoefficientSqrtPhase a q‖ ^ (2 : ℕ) =
      ‖a q‖ := by
  rw [ccmRationalMoritaCoefficientSqrtPhase_norm,
    Real.sq_sqrt (norm_nonneg _)]

def ccmRationalMoritaCoefficientLOneBound
    (a : CCMRationalUnit → ℂ) : ℝ :=
  ∑' q, ‖a q‖

theorem ccmRationalMoritaCoefficientLOneBound_nonneg
    (a : CCMRationalUnit → ℂ) :
    0 ≤ ccmRationalMoritaCoefficientLOneBound a :=
  tsum_nonneg fun _ => norm_nonneg _

theorem ccmRationalMoritaCoefficient_norm_le_lOneBound
    {a : CCMRationalUnit → ℂ}
    (hsum : Summable (fun q => ‖a q‖)) (q : CCMRationalUnit) :
    ‖a q‖ ≤ ccmRationalMoritaCoefficientLOneBound a :=
  hsum.le_tsum q fun _ _ => norm_nonneg _

theorem ccmRationalMoritaCoefficientSqrtNorm_bound
    {a : CCMRationalUnit → ℂ}
    (hsum : Summable (fun q => ‖a q‖)) :
    ∀ q, ‖ccmRationalMoritaCoefficientSqrtNorm a q‖ ≤
      Real.sqrt (ccmRationalMoritaCoefficientLOneBound a) := by
  intro q
  rw [ccmRationalMoritaCoefficientSqrtNorm_norm]
  exact Real.sqrt_le_sqrt
    (ccmRationalMoritaCoefficient_norm_le_lOneBound hsum q)

theorem ccmRationalMoritaCoefficientSqrtPhase_bound
    {a : CCMRationalUnit → ℂ}
    (hsum : Summable (fun q => ‖a q‖)) :
    ∀ q, ‖ccmRationalMoritaCoefficientSqrtPhase a q‖ ≤
      Real.sqrt (ccmRationalMoritaCoefficientLOneBound a) := by
  intro q
  rw [ccmRationalMoritaCoefficientSqrtPhase_norm]
  exact Real.sqrt_le_sqrt
    (ccmRationalMoritaCoefficient_norm_le_lOneBound hsum q)

theorem ccmRationalMoritaCoefficientSqrtNorm_summable_sq
    {a : CCMRationalUnit → ℂ}
    (hsum : Summable (fun q => ‖a q‖)) :
    Summable (fun q =>
      ‖ccmRationalMoritaCoefficientSqrtNorm a q‖ ^ (2 : ℕ)) :=
  hsum.congr fun q =>
    (ccmRationalMoritaCoefficientSqrtNorm_sq a q).symm

theorem ccmRationalMoritaCoefficientSqrtPhase_summable_sq
    {a : CCMRationalUnit → ℂ}
    (hsum : Summable (fun q => ‖a q‖)) :
    Summable (fun q =>
      ‖ccmRationalMoritaCoefficientSqrtPhase a q‖ ^ (2 : ℕ)) :=
  hsum.congr fun q =>
    (ccmRationalMoritaCoefficientSqrtPhase_sq a q).symm

theorem ccmRationalMoritaWeightedShift_isTraceClass_of_summable
    (a : CCMRationalUnit → ℂ) (k : CCMRationalUnit)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ q, ‖a q‖ ≤ C)
    (hsum : Summable (fun q => ‖a q‖)) :
    (ccmRationalMoritaWeightedShift a k C hC ha).IsTraceClass := by
  let D := Real.sqrt (ccmRationalMoritaCoefficientLOneBound a)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  let r := ccmRationalMoritaCoefficientSqrtNorm a
  let s := ccmRationalMoritaCoefficientSqrtPhase a
  have hr : ∀ q, ‖r q‖ ≤ D :=
    ccmRationalMoritaCoefficientSqrtNorm_bound hsum
  have hs : ∀ q, ‖s q‖ ≤ D :=
    ccmRationalMoritaCoefficientSqrtPhase_bound hsum
  let A := ccmRationalMoritaWeightedShift s 1 D hD hs
  let B := ccmRationalMoritaWeightedShift r k D hD hr
  have hA : A.IsHilbertSchmidt := by
    apply ccmRationalMoritaWeightedShift_isHilbertSchmidt
    exact ccmRationalMoritaCoefficientSqrtPhase_summable_sq hsum
  have hB : B.IsHilbertSchmidt := by
    apply ccmRationalMoritaWeightedShift_isHilbertSchmidt
    exact ccmRationalMoritaCoefficientSqrtNorm_summable_sq hsum
  have hfac :
      ccmRationalMoritaWeightedShift a k C hC ha = A ∘L B := by
    apply ContinuousLinearMap.ext
    intro f
    ext q
    simp only [ContinuousLinearMap.comp_apply, A, B,
      ccmRationalMoritaWeightedShift_apply]
    simp only [inv_one, one_mul]
    change a q * f (k⁻¹ * q) =
      s q * (r q * f (k⁻¹ * q))
    rw [← mul_assoc,
      ccmRationalMoritaCoefficientSqrtPhase_mul_sqrtNorm]
  rw [hfac]
  exact hA.comp_isTraceClass hB

end RHTower
end GaloisForLFunctions
