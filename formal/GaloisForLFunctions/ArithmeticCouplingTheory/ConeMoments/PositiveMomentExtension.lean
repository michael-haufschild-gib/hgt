import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveFiniteCorrection

/-!
# Positive correction by moving to a larger real part

A finite positive exponential sum supported to the left of `d` has normalized
residual at real level `D` bounded by its mass times `exp(-(D-d)u)`.
Previously cancelled moments contribute nothing. A small tail of this exponential
bound therefore permits an exact positive correction at the new real level,
with prescribed total mass and arbitrarily large imaginary parts.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- The exponential moments of a finite weighted cloud of complex points. -/
def finiteLaplaceSum {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ) (u : ℝ) : ℂ :=
  ∑ j, (w j : ℂ) * Complex.exp ((u : ℂ) * z j)

lemma finiteLaplaceSum_norm_le {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ)
    {d u : ℝ} (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, (z j).re ≤ d) (hu : 0 ≤ u) :
    ‖finiteLaplaceSum z w u‖ ≤ (∑ j, w j) * Real.exp (u * d) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine sum_le_sum fun j _ => ?_
  have he : ‖Complex.exp ((u : ℂ) * z j)‖ = Real.exp (u * (z j).re) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j), he]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hz j) hu)) (hw j)

/-- Divide an old moment by the exponential growth at the proposed real level. -/
def normalizedResidual {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ) (D u : ℝ) : ℂ :=
  (Real.exp (-D * u) : ℂ) * finiteLaplaceSum z w u

lemma normalizedResidual_norm_le {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ)
    {d D M u : ℝ} (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, (z j).re ≤ d)
    (hM : ∑ j, w j ≤ M) (hu : 0 ≤ u) :
    ‖normalizedResidual z w D u‖ ≤ M * Real.exp (-(D - d) * u) := by
  rw [normalizedResidual, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-D * u) * ‖finiteLaplaceSum z w u‖
      ≤ Real.exp (-D * u) * ((∑ j, w j) * Real.exp (u * d)) :=
        mul_le_mul_of_nonneg_left (finiteLaplaceSum_norm_le z w hw hz hu) (Real.exp_pos _).le
    _ ≤ Real.exp (-D * u) * (M * Real.exp (u * d)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = M * Real.exp (-(D - d) * u) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- Only frequencies outside the already cancelled set contribute to the correction size. -/
lemma normalizedResidual_sum_le {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ)
    (S T : Finset ℝ) {d D M : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, (z j).re ≤ d) (hM : ∑ j, w j ≤ M)
    (hS : ∀ u ∈ S, 0 ≤ u) (hzero : ∀ u ∈ T, finiteLaplaceSum z w u = 0) :
    ∑ u ∈ S, ‖normalizedResidual z w D u‖ ≤
      M * ∑ u ∈ S \ T, Real.exp (-(D - d) * u) := by
  classical
  have hs : ∑ u ∈ S, ‖normalizedResidual z w D u‖ =
      ∑ u ∈ S \ T, ‖normalizedResidual z w D u‖ := by
    symm
    refine sum_subset sdiff_subset fun u hu hnot => ?_
    have huT : u ∈ T := by
      by_contra h
      exact hnot (mem_sdiff.mpr ⟨hu, h⟩)
    simp only [normalizedResidual, hzero u huT, mul_zero, norm_zero]
  rw [hs, Finset.mul_sum]
  exact sum_le_sum fun u hu => normalizedResidual_norm_le z w hw hz hM
    (hS u (mem_sdiff.mp hu).1)

lemma exp_level_eq (D u t : ℝ) :
    Complex.exp ((u : ℂ) * ((D : ℂ) + (t : ℂ) * Complex.I)) =
      (Real.exp (D * u) : ℂ) * phase u t := by
  have he : (u : ℂ) * ((D : ℂ) + (t : ℂ) * Complex.I) =
      ((D * u : ℝ) : ℂ) + ((u * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.ofReal_exp]
  rfl

/-- A new real level cancels a larger finite moment set with a prescribed positive mass. -/
theorem exists_positive_level_extension {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ)
    (S T : Finset ℝ) {d D M A : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hz : ∀ j, (z j).re ≤ d) (hM : ∑ j, w j ≤ M)
    (hS : ∀ u ∈ S, 0 < u) (hzero : ∀ u ∈ T, finiteLaplaceSum z w u = 0)
    (hA : 0 < A) (htail : M * ∑ u ∈ S \ T, Real.exp (-(D - d) * u) ≤ A / 4) :
    ∃ n : ℕ, 0 < n ∧ ∀ H : ℝ, ∃ x v : Fin n → ℝ,
      (∀ j, H ≤ x j) ∧
      (∀ j, 0 < v j ∧ A / (2 * n) ≤ v j ∧ v j ≤ 3 * A / (2 * n)) ∧
      (∑ j, v j = A) ∧
      (∀ u ∈ S, finiteLaplaceSum z w u +
        finiteLaplaceSum (fun j => (D : ℂ) + (x j : ℂ) * Complex.I) v u = 0) := by
  have hr := (normalizedResidual_sum_le z w S T hw hz hM
    (fun u hu => (hS u hu).le) hzero).trans htail
  obtain ⟨n, hn, hc⟩ := exists_positive_correction S hS
    (normalizedResidual z w D) hA hr
  refine ⟨n, hn, fun H => ?_⟩
  obtain ⟨x, v, hx, hv, hmass, hmoment⟩ := hc H
  refine ⟨x, v, hx, hv, hmass, fun u hu => ?_⟩
  have he : finiteLaplaceSum (fun j => (D : ℂ) + (x j : ℂ) * Complex.I) v u =
      (Real.exp (D * u) : ℂ) * ∑ j, (v j : ℂ) * phase u (x j) := by
    simp only [finiteLaplaceSum, exp_level_eq, Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [he, hmoment u hu, normalizedResidual, mul_neg, ← mul_assoc]
  have hcancel : (Real.exp (D * u) : ℂ) * (Real.exp (-D * u) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  rw [hcancel, one_mul, add_neg_cancel]

#print axioms exists_positive_level_extension
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
