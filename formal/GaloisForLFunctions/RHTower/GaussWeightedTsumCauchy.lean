import GaloisForLFunctions.RHTower.GaussDoubleDefect

/-!
# Weighted Cauchy--Schwarz for nonnegative extended-real sums

This form does not require prior finiteness of either side.  It is the square-collapse step for
Gauss defect chains and prevents introduction of a duplicate lattice variable.
-/

namespace RHTower

open scoped ENNReal

noncomputable section

theorem ennreal_tsum_ofReal_mul_sq_le {ι : Type*} (a x : ι → ℝ)
    (ha : ∀ s, 0 ≤ a s) (hx : ∀ s, 0 ≤ x s) :
    (∑' s, ENNReal.ofReal (a s * x s)) * (∑' s, ENNReal.ofReal (a s * x s)) ≤
      (∑' s, ENNReal.ofReal (a s)) *
        ∑' s, ENNReal.ofReal (a s * x s ^ 2) := by
  set A : ℝ≥0∞ := ∑' s, ENNReal.ofReal (a s) with hA
  set B : ℝ≥0∞ := ∑' s, ENNReal.ofReal (a s * x s ^ 2) with hB
  have hexpand :
      (∑' s, ENNReal.ofReal (a s * x s)) * (∑' s, ENNReal.ofReal (a s * x s)) =
        ∑' s, ∑' t, ENNReal.ofReal (a s * x s) * ENNReal.ofReal (a t * x t) := by
    have hinner : ∀ s,
        (∑' t, ENNReal.ofReal (a s * x s) * ENNReal.ofReal (a t * x t)) =
          ENNReal.ofReal (a s * x s) * ∑' t, ENNReal.ofReal (a t * x t) :=
      fun s => ENNReal.tsum_mul_left
    rw [tsum_congr hinner, ENNReal.tsum_mul_right]
  rw [hexpand]
  have hBA : (∑' s, ∑' t,
      ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t)) = B * A := by
    have hinner : ∀ s,
        (∑' t, ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t)) =
          ENNReal.ofReal (a s * x s ^ 2) * A := fun s => ENNReal.tsum_mul_left
    rw [tsum_congr hinner, ENNReal.tsum_mul_right]
  have hAB : (∑' s, ∑' t,
      ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s)) = A * B := by
    have hinner : ∀ s,
        (∑' t, ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s)) =
          B * ENNReal.ofReal (a s) := fun s => ENNReal.tsum_mul_right
    rw [tsum_congr hinner, ENNReal.tsum_mul_left, mul_comm]
  have hhalf : ∀ s t,
      ENNReal.ofReal (a s * x s) * ENNReal.ofReal (a t * x t) ≤
        ENNReal.ofReal (2⁻¹) *
          (ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t) +
            ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s)) := by
    intro s t
    rw [← ENNReal.ofReal_mul (mul_nonneg (ha s) (hx s)),
      ← ENNReal.ofReal_mul (mul_nonneg (ha s) (sq_nonneg _)),
      ← ENNReal.ofReal_mul (mul_nonneg (ha t) (sq_nonneg _)),
      ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (ha s) (sq_nonneg _)) (ha t))
        (mul_nonneg (mul_nonneg (ha t) (sq_nonneg _)) (ha s)),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hamgm : x s * x t ≤ (x s ^ 2 + x t ^ 2) / 2 := by
      nlinarith [sq_nonneg (x s - x t)]
    have hat : 0 ≤ a s * a t := mul_nonneg (ha s) (ha t)
    nlinarith [mul_le_mul_of_nonneg_left hamgm hat]
  calc
    (∑' s, ∑' t, ENNReal.ofReal (a s * x s) * ENNReal.ofReal (a t * x t))
        ≤ ∑' s, ∑' t, ENNReal.ofReal (2⁻¹) *
          (ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t) +
            ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s)) := by
      exact ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum fun t => hhalf s t
    _ = ENNReal.ofReal (2⁻¹) *
        ((∑' s, ∑' t, ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t)) +
          ∑' s, ∑' t, ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s)) := by
      have hpull : ∀ s,
          (∑' t, ENNReal.ofReal (2⁻¹) *
            (ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t) +
              ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s))) =
            ENNReal.ofReal (2⁻¹) *
              ((∑' t, ENNReal.ofReal (a s * x s ^ 2) * ENNReal.ofReal (a t)) +
                ∑' t, ENNReal.ofReal (a t * x t ^ 2) * ENNReal.ofReal (a s)) := by
        intro s
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      rw [tsum_congr hpull, ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ = ENNReal.ofReal (2⁻¹) * (B * A + A * B) := by rw [hBA, hAB]
    _ = A * B := by
      have hcomm : B * A + A * B = 2 * (A * B) := by rw [mul_comm B A, two_mul]
      rw [hcomm, ← mul_assoc]
      have h12 : ENNReal.ofReal (2⁻¹) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [h12, one_mul]
    _ = (∑' s, ENNReal.ofReal (a s)) *
        ∑' s, ENNReal.ofReal (a s * x s ^ 2) := by rw [hA, hB]

end

end RHTower
