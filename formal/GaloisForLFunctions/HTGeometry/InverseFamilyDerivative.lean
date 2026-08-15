import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of the inverse of a family of units

Inverting a differentiable family of invertible elements is differentiable, and each differentiation
costs one more copy of the inverse:

`(C⁻¹)' = −C⁻¹C'C⁻¹`,   `(C⁻¹)'' = 2 C⁻¹C'C⁻¹C'C⁻¹ − C⁻¹C''C⁻¹`.

So on a region where `‖C⁻¹‖` is small, each derivative of the inverse is smaller than the last by a
full power of `‖C⁻¹‖`.  That is the gain behind repeated integration by parts against a phase whose
symbol is invertible with a growing floor: the boundary terms accumulate powers of the resolvent
while only the amplitude's own derivatives are spent.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- The pointwise inverse of a family. -/
def invFamily (C : ℝ → R) (s : ℝ) : R := Ring.inverse (C s)

/-- The derivative of the inverse family. -/
def invFamilyDeriv (C C₁ : ℝ → R) (s : ℝ) : R := -(invFamily C s * C₁ s * invFamily C s)

/-- The second derivative of the inverse family. -/
def invFamilyDeriv2 (C C₁ C₂ : ℝ → R) (s : ℝ) : R :=
  invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s
    + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s
    - invFamily C s * C₂ s * invFamily C s

/-- **The inverse of a differentiable family of units is differentiable.** -/
theorem hasDerivAt_invFamily {C C₁ : ℝ → R} {t : ℝ} (hC : HasDerivAt C (C₁ t) t)
    (hu : IsUnit (C t)) :
    HasDerivAt (invFamily C) (invFamilyDeriv C C₁ t) t := by
  obtain ⟨x, hx⟩ := hu
  have hxC : C t = (x : R) := hx.symm
  have hinv : invFamily C t = ((x⁻¹ : Rˣ) : R) := by
    rw [invFamily, hxC, Ring.inverse_unit]
  have hpt : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ R ((x⁻¹ : Rˣ) : R) ((x⁻¹ : Rˣ) : R))) (C t) := by
    rw [hxC]
    exact hasFDerivAt_ringInverse x
  have h := hpt.comp_hasDerivAt t hC
  refine h.congr_deriv ?_
  rw [invFamilyDeriv, hinv]
  simp [ContinuousLinearMap.mulLeftRight_apply]

/-- **The second derivative of the inverse family.** -/
theorem hasDerivAt_invFamilyDeriv {C C₁ C₂ : ℝ → R}
    (hC : ∀ s, HasDerivAt C (C₁ s) s) (hu : ∀ s, IsUnit (C s))
    (hC₁ : ∀ s, HasDerivAt C₁ (C₂ s) s) (t : ℝ) :
    HasDerivAt (invFamilyDeriv C C₁) (invFamilyDeriv2 C C₁ C₂ t) t := by
  have hD : ∀ s, HasDerivAt (invFamily C) (invFamilyDeriv C C₁ s) s :=
    fun s => hasDerivAt_invFamily (hC s) (hu s)
  have hprod : HasDerivAt (fun s => invFamily C s * C₁ s * invFamily C s)
      ((invFamilyDeriv C C₁ t * C₁ t + invFamily C t * C₂ t) * invFamily C t
        + invFamily C t * C₁ t * invFamilyDeriv C C₁ t) t :=
    ((hD t).mul (hC₁ t)).mul (hD t)
  have hneg := hprod.neg
  refine hneg.congr_deriv ?_
  rw [invFamilyDeriv2, invFamilyDeriv]
  simp only [neg_mul, mul_neg, neg_add_rev, neg_neg]
  noncomm_ring

/-! ## The norm bounds -/

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
theorem norm_invFamilyDeriv_le (C C₁ : ℝ → R) (t : ℝ) :
    ‖invFamilyDeriv C C₁ t‖ ≤ ‖invFamily C t‖ ^ 2 * ‖C₁ t‖ := by
  rw [invFamilyDeriv, norm_neg]
  calc ‖invFamily C t * C₁ t * invFamily C t‖
      ≤ ‖invFamily C t * C₁ t‖ * ‖invFamily C t‖ := norm_mul_le _ _
    _ ≤ (‖invFamily C t‖ * ‖C₁ t‖) * ‖invFamily C t‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖invFamily C t‖ ^ 2 * ‖C₁ t‖ := by ring

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
theorem norm_invFamilyDeriv2_le (C C₁ C₂ : ℝ → R) (t : ℝ) :
    ‖invFamilyDeriv2 C C₁ C₂ t‖
      ≤ 2 * ‖invFamily C t‖ ^ 3 * ‖C₁ t‖ ^ 2 + ‖invFamily C t‖ ^ 2 * ‖C₂ t‖ := by
  set D := ‖invFamily C t‖ with hD
  have hDnn : 0 ≤ D := norm_nonneg _
  have h1 : ‖invFamily C t * C₁ t * invFamily C t * C₁ t * invFamily C t‖
      ≤ D ^ 3 * ‖C₁ t‖ ^ 2 := by
    calc ‖invFamily C t * C₁ t * invFamily C t * C₁ t * invFamily C t‖
        ≤ ‖invFamily C t * C₁ t * invFamily C t * C₁ t‖ * D := norm_mul_le _ _
      _ ≤ (‖invFamily C t * C₁ t * invFamily C t‖ * ‖C₁ t‖) * D :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) hDnn
      _ ≤ ((‖invFamily C t * C₁ t‖ * D) * ‖C₁ t‖) * D := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) hDnn
          exact norm_mul_le _ _
      _ ≤ (((D * ‖C₁ t‖) * D) * ‖C₁ t‖) * D := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ?_ hDnn) (norm_nonneg _)) hDnn
          exact norm_mul_le _ _
      _ = D ^ 3 * ‖C₁ t‖ ^ 2 := by ring
  have h2 : ‖invFamily C t * C₂ t * invFamily C t‖ ≤ D ^ 2 * ‖C₂ t‖ := by
    calc ‖invFamily C t * C₂ t * invFamily C t‖
        ≤ ‖invFamily C t * C₂ t‖ * D := norm_mul_le _ _
      _ ≤ (D * ‖C₂ t‖) * D := mul_le_mul_of_nonneg_right (norm_mul_le _ _) hDnn
      _ = D ^ 2 * ‖C₂ t‖ := by ring
  rw [invFamilyDeriv2]
  set P := invFamily C t * C₁ t * invFamily C t * C₁ t * invFamily C t with hP
  calc ‖P + P - invFamily C t * C₂ t * invFamily C t‖
      ≤ ‖P + P‖ + ‖invFamily C t * C₂ t * invFamily C t‖ := norm_sub_le _ _
    _ ≤ (‖P‖ + ‖P‖) + D ^ 2 * ‖C₂ t‖ := add_le_add (norm_add_le _ _) h2
    _ ≤ (D ^ 3 * ‖C₁ t‖ ^ 2 + D ^ 3 * ‖C₁ t‖ ^ 2) + D ^ 2 * ‖C₂ t‖ :=
        add_le_add (add_le_add h1 h1) le_rfl
    _ = 2 * D ^ 3 * ‖C₁ t‖ ^ 2 + D ^ 2 * ‖C₂ t‖ := by ring

/-! ## The second boundary term of the two-fold integration by parts -/

/-- The product `C⁻¹(C⁻¹)'` appearing as the second boundary term. -/
def invFamilyProduct (C C₁ : ℝ → R) (s : ℝ) : R := invFamily C s * invFamilyDeriv C C₁ s

/-- Its derivative, the amplitude of the remaining integral. -/
def invFamilyProductDeriv (C C₁ C₂ : ℝ → R) (s : ℝ) : R :=
  invFamilyDeriv C C₁ s * invFamilyDeriv C C₁ s + invFamily C s * invFamilyDeriv2 C C₁ C₂ s

theorem hasDerivAt_invFamilyProduct {C C₁ C₂ : ℝ → R}
    (hC : ∀ s, HasDerivAt C (C₁ s) s) (hu : ∀ s, IsUnit (C s))
    (hC₁ : ∀ s, HasDerivAt C₁ (C₂ s) s) (t : ℝ) :
    HasDerivAt (invFamilyProduct C C₁) (invFamilyProductDeriv C C₁ C₂ t) t :=
  (hasDerivAt_invFamily (hC t) (hu t)).mul (hasDerivAt_invFamilyDeriv hC hu hC₁ t)

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
theorem norm_invFamilyProduct_le (C C₁ : ℝ → R) (t : ℝ) :
    ‖invFamilyProduct C C₁ t‖ ≤ ‖invFamily C t‖ ^ 3 * ‖C₁ t‖ := by
  rw [invFamilyProduct]
  calc ‖invFamily C t * invFamilyDeriv C C₁ t‖
      ≤ ‖invFamily C t‖ * ‖invFamilyDeriv C C₁ t‖ := norm_mul_le _ _
    _ ≤ ‖invFamily C t‖ * (‖invFamily C t‖ ^ 2 * ‖C₁ t‖) :=
        mul_le_mul_of_nonneg_left (norm_invFamilyDeriv_le C C₁ t) (norm_nonneg _)
    _ = ‖invFamily C t‖ ^ 3 * ‖C₁ t‖ := by ring

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The remaining amplitude is two resolvent powers smaller.** -/
theorem norm_invFamilyProductDeriv_le (C C₁ C₂ : ℝ → R) (t : ℝ) :
    ‖invFamilyProductDeriv C C₁ C₂ t‖
      ≤ 3 * ‖invFamily C t‖ ^ 4 * ‖C₁ t‖ ^ 2 + ‖invFamily C t‖ ^ 3 * ‖C₂ t‖ := by
  set D := ‖invFamily C t‖ with hD
  have hDnn : 0 ≤ D := norm_nonneg _
  have h1 : ‖invFamilyDeriv C C₁ t * invFamilyDeriv C C₁ t‖ ≤ D ^ 4 * ‖C₁ t‖ ^ 2 := by
    have hbase := norm_invFamilyDeriv_le C C₁ t
    calc ‖invFamilyDeriv C C₁ t * invFamilyDeriv C C₁ t‖
        ≤ ‖invFamilyDeriv C C₁ t‖ * ‖invFamilyDeriv C C₁ t‖ := norm_mul_le _ _
      _ ≤ (D ^ 2 * ‖C₁ t‖) * (D ^ 2 * ‖C₁ t‖) :=
          mul_le_mul hbase hbase (norm_nonneg _) (by positivity)
      _ = D ^ 4 * ‖C₁ t‖ ^ 2 := by ring
  have h2 : ‖invFamily C t * invFamilyDeriv2 C C₁ C₂ t‖
      ≤ D * (2 * D ^ 3 * ‖C₁ t‖ ^ 2 + D ^ 2 * ‖C₂ t‖) := by
    calc ‖invFamily C t * invFamilyDeriv2 C C₁ C₂ t‖
        ≤ D * ‖invFamilyDeriv2 C C₁ C₂ t‖ := norm_mul_le _ _
      _ ≤ D * (2 * D ^ 3 * ‖C₁ t‖ ^ 2 + D ^ 2 * ‖C₂ t‖) :=
          mul_le_mul_of_nonneg_left (norm_invFamilyDeriv2_le C C₁ C₂ t) hDnn
  rw [invFamilyProductDeriv]
  calc ‖invFamilyDeriv C C₁ t * invFamilyDeriv C C₁ t
        + invFamily C t * invFamilyDeriv2 C C₁ C₂ t‖
      ≤ ‖invFamilyDeriv C C₁ t * invFamilyDeriv C C₁ t‖
        + ‖invFamily C t * invFamilyDeriv2 C C₁ C₂ t‖ := norm_add_le _ _
    _ ≤ D ^ 4 * ‖C₁ t‖ ^ 2 + D * (2 * D ^ 3 * ‖C₁ t‖ ^ 2 + D ^ 2 * ‖C₂ t‖) := add_le_add h1 h2
    _ = 3 * D ^ 4 * ‖C₁ t‖ ^ 2 + D ^ 3 * ‖C₂ t‖ := by ring

end GaloisForLFunctions.HTGeometry
