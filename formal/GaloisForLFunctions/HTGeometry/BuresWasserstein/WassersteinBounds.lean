/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinEquation

/-!
# Loewner bounds for the Wasserstein barycentre

Kim–Mer–Pálfia (arXiv:2607.29142) bound the Bures–Wasserstein barycentre `X` of a weighted family
`(wᵢ, Aᵢ)` of strictly positive operators between a harmonic-type lower bound and the arithmetic
mean:

`2 - ∑ wᵢ Aᵢ⁻¹ ≤ X ≤ ∑ wᵢ Aᵢ`   (Theorem 6.2),

with the companion bound `2 - ∑ wᵢ Aᵢ ≤ X⁻¹`, and the Jensen-type comparisons of Theorem 6.7
against the quasi-arithmetic mean of order `1/2`.

The two supporting operator-convexity facts proved here are of independent interest:
`sq_sum_smul_le_sum_smul_sq` (operator convexity of `t ↦ t²`, via the exact remainder
`∑ wᵢ (Tᵢ - L)²`) and `ringInverse_sum_le_sum_ringInverse` (the harmonic–arithmetic mean
inequality, a special case of joint convexity of `(x,a) ↦ x a⁻¹ x`).
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {X : A}

/-! ### Two operator convexity facts -/

/-- **Operator convexity of the square**: `(∑ wᵢ Tᵢ)² ≤ ∑ wᵢ Tᵢ²` for self-adjoint `Tᵢ` and a
probability weight vector.  The proof is the exact remainder identity
`∑ wᵢ (Tᵢ - L)² = ∑ wᵢ Tᵢ² - L²` with `L = ∑ wᵢ Tᵢ`. -/
theorem sq_sum_smul_le_sum_smul_sq {T : ι → A} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) (hT : ∀ i ∈ s, IsSelfAdjoint (T i)) :
    (∑ i ∈ s, w i • T i) * (∑ i ∈ s, w i • T i) ≤ ∑ i ∈ s, w i • (T i * T i) := by
  set L := ∑ i ∈ s, w i • T i with hL
  have hLsa : IsSelfAdjoint L :=
    isSelfAdjoint_sum s fun i hi => IsSelfAdjoint.smul (star_trivial (w i)) (hT i hi)
  have hexpand : ∀ i : ι, (T i - L) * (T i - L)
      = T i * T i - T i * L - L * T i + L * L := fun i => by noncomm_ring
  have e1 : ∑ i ∈ s, w i • (T i * L) = L * L := by
    rw [hL, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
  have e2 : ∑ i ∈ s, w i • (L * T i) = L * L := by
    nth_rewrite 2 [hL]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_smul_comm _ _ _).symm
  have e3 : ∑ i ∈ s, w i • (L * L) = L * L := by rw [← Finset.sum_smul, hsum, one_smul]
  have key : ∑ i ∈ s, w i • ((T i - L) * (T i - L))
      = (∑ i ∈ s, w i • (T i * T i)) - L * L := by
    simp only [hexpand, smul_sub, smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      e1, e2, e3]
    abel
  have hnn : (0 : A) ≤ ∑ i ∈ s, w i • ((T i - L) * (T i - L)) := by
    refine Finset.sum_nonneg fun i hi => smul_nonneg (hw i hi) ?_
    have hsa : IsSelfAdjoint (T i - L) := (hT i hi).sub hLsa
    nth_rewrite 1 [← hsa.star_eq]
    exact star_mul_self_nonneg _
  rw [key] at hnn
  exact sub_nonneg.mp hnn

/-- **Harmonic–arithmetic mean inequality**: `(∑ wᵢ Hᵢ)⁻¹ ≤ ∑ wᵢ Hᵢ⁻¹`. -/
theorem ringInverse_sum_le_sum_ringInverse (hs : s.Nonempty) {H : ι → A}
    (hw : ∀ i ∈ s, 0 < w i) (hsum : ∑ i ∈ s, w i = 1)
    (hH : ∀ i ∈ s, IsStrictlyPositive (H i)) :
    (∑ i ∈ s, w i • H i)⁻¹ʳ ≤ ∑ i ∈ s, w i • (H i)⁻¹ʳ := by
  have h := conj_ringInverse_convex (x := fun _ => (1 : A)) hs hw
    (fun _ _ => IsSelfAdjoint.one A) hH
  rw [show ∑ i ∈ s, w i • (1 : A) = 1 by rw [← Finset.sum_smul, hsum, one_smul]] at h
  simpa using h

/-! ### Sandwich identities -/

lemma rpow_neg_half_mul_self (hX : IsStrictlyPositive X) :
    X ^ (-(1/2) : ℝ) * X = X ^ (1/2 : ℝ) := by
  nth_rewrite 2 [← rpow_half_mul_rpow_half hX]
  rw [← mul_assoc, rpow_neg_half_mul_rpow_half hX, one_mul]

lemma mul_rpow_neg_half (hX : IsStrictlyPositive X) :
    X * X ^ (-(1/2) : ℝ) = X ^ (1/2 : ℝ) := by
  nth_rewrite 1 [← rpow_half_mul_rpow_half hX]
  rw [mul_assoc, rpow_half_mul_rpow_neg_half hX, mul_one]

lemma conj_sq_rpow_neg_half (hX : IsStrictlyPositive X) :
    X ^ (-(1/2) : ℝ) * (X * X) * X ^ (-(1/2) : ℝ) = X := by
  rw [← mul_assoc, mul_assoc _ X X, mul_assoc (X ^ (-(1/2) : ℝ)),
    mul_rpow_neg_half hX, rpow_neg_half_mul_self hX, rpow_half_mul_rpow_half hX]

/-! ### Theorem 6.2: the Loewner bounds -/

/-- **Upper Loewner bound**: the Wasserstein barycentre is dominated by the arithmetic mean. -/
theorem IsWassersteinPoint.le_arithMean (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsWassersteinPoint s w Av X) :
    X ≤ ∑ i ∈ s, w i • Av i := by
  obtain ⟨hX, -⟩ := h
  have hprimal := (isWassersteinPoint_iff_sqrt hX hA).mp h
  set S : ι → A := fun i => CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)) with hS
  have hSsa : ∀ i ∈ s, IsSelfAdjoint (S i) := fun i _ => (CFC.sqrt_nonneg _).isSelfAdjoint
  have hSsq : ∀ i ∈ s, S i * S i = X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ) := fun i hi =>
    CFC.sqrt_mul_sqrt_self _
      (nonneg_conjugate (isSelfAdjoint_rpow X _) (hA i hi).nonneg)
  have hconv := sq_sum_smul_le_sum_smul_sq (T := S) hw hsum hSsa
  rw [hprimal] at hconv
  have hrhs : ∑ i ∈ s, w i • (S i * S i)
      = X ^ (1/2 : ℝ) * (∑ i ∈ s, w i • Av i) * X ^ (1/2 : ℝ) := by
    rw [← sum_smul_conjugate]
    exact Finset.sum_congr rfl fun i hi => by rw [hSsq i hi]
  rw [hrhs] at hconv
  have := (isSelfAdjoint_rpow X (-(1/2) : ℝ)).conjugate_le_conjugate hconv
  rwa [conj_sq_rpow_neg_half hX, sandwich_peel' hX] at this

/-- **Lower Loewner bound** for the inverse: `2 - ∑ wᵢ Aᵢ ≤ X⁻¹`. -/
theorem IsWassersteinPoint.two_sub_arithMean_le_ringInverse (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (h : IsWassersteinPoint s w Av X) :
    (2 : ℝ) • (1 : A) - ∑ i ∈ s, w i • Av i ≤ X⁻¹ʳ := by
  obtain ⟨hX, heq⟩ := h
  have hstep : (1 : A) ≤ (2 : ℝ)⁻¹ • (X⁻¹ʳ + ∑ i ∈ s, w i • Av i) := by
    rw [← heq]
    have hbound : ∀ i ∈ s, w i • gm (Av i) X⁻¹ʳ
        ≤ w i • ((2 : ℝ)⁻¹ • (X⁻¹ʳ + Av i)) := fun i hi =>
      smul_le_smul_of_nonneg_left
        (by rw [gm_comm (hA i hi) hX.ringInverse]; exact gm_le_arith hX.ringInverse (hA i hi))
        (hw i hi)
    refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
    rw [smul_add, Finset.smul_sum]
    simp only [smul_add, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_smul, hsum, one_smul]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have h2 := smul_le_smul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 2)
  rw [smul_smul, show (2:ℝ) * (2:ℝ)⁻¹ = 1 by norm_num, one_smul] at h2
  exact sub_le_iff_le_add.mpr (by rw [add_comm]; exact h2)

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
