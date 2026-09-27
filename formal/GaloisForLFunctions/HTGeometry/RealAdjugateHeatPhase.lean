import GaloisForLFunctions.HTGeometry.WeightedVandermondeSamplingEnergy

/-!
# Phase interpolation before coefficient norms are separated

The adjugate acts on the complete real phase vector before a weighted
Cauchy--Schwarz bound is taken. The resulting column envelope is no larger
than the product of the two separate trace envelopes.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

theorem real_adjugate_phase_reconstruction {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (a h : Fin n → ℝ) :
    M.det * (∑ j, a j * h j) =
      ∑ i, M.mulVec a i * (∑ j, M.adjugate j i * h j) := by
  have hc : M.adjugate.mulVec (M.mulVec a) = M.det • a := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hj (j : Fin n) : M.det * a j = ∑ i, M.adjugate j i * M.mulVec a i := by
    have h := congrArg (fun v : Fin n → ℝ => v j) hc
    exact (by simpa only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] using h.symm)
  calc
    _ = ∑ j, (M.det * a j) * h j := by rw [Finset.mul_sum]; congr 1; funext j; ring
    _ = ∑ j, (∑ i, M.adjugate j i * M.mulVec a i) * h j := by simp only [hj]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The whole phase is compared directly with weighted nodal energy. -/
theorem real_adjugate_heat_phase_bound {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (a h rate : Fin n → ℝ) (t : ℝ) :
    M.det ^ 2 * (∑ j, a j * h j) ^ 2 ≤
      (∑ i, M.mulVec a i ^ 2 * Real.exp (-(t * rate i))) *
        ∑ i, (∑ j, M.adjugate j i * h j) ^ 2 * Real.exp (t * rate i) := by
  rw [← mul_pow, real_adjugate_phase_reconstruction]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  · intro i _
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  · intro i _
    have he : Real.exp (-(t * rate i)) * Real.exp (t * rate i) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    apply le_of_eq
    calc
      _ = (M.mulVec a i ^ 2 * (∑ j, M.adjugate j i * h j) ^ 2) * 1 := by ring
      _ = _ := by rw [← he]; ring

def realAdjugateHeatPhaseEnvelope {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rate r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (∑ j, |M.adjugate j i| * r j) ^ 2 * Real.exp (t * rate i)

theorem realAdjugateHeatPhaseEnvelope_nonneg {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rate r : Fin n → ℝ) (t : ℝ) :
    0 ≤ realAdjugateHeatPhaseEnvelope M rate r t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- Keeping each interpolation column together never worsens the separated trace bound. -/
theorem realAdjugateHeatPhaseEnvelope_le_separated {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (rate r : Fin n → ℝ) (t : ℝ) :
    realAdjugateHeatPhaseEnvelope M rate r t ≤
      (∑ j, r j ^ 2) * ∑ j, ∑ i, M.adjugate j i ^ 2 * Real.exp (t * rate i) := by
  have h (i : Fin n) := mul_le_mul_of_nonneg_right
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |M.adjugate j i|) r)
    (Real.exp_pos (t * rate i)).le
  simp only [sq_abs] at h
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => h i
  change realAdjugateHeatPhaseEnvelope M rate r t ≤ _ at hs
  calc
    _ ≤ ∑ i, ((∑ j, M.adjugate j i ^ 2) * ∑ j, r j ^ 2) *
        Real.exp (t * rate i) := hs
    _ = (∑ j, r j ^ 2) * ∑ i, (∑ j, M.adjugate j i ^ 2) *
        Real.exp (t * rate i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]

end
end GaloisForLFunctions.HTGeometry
