import GaloisForLFunctions.RHTower.XiLogarithmicIslands

/-!
# Separation of finitely many real exponential marks on Xi inverse disks

A chosen mark agrees with exp(w) on the logarithm disk. Every other mark
avoids the entire unit circle there after moving the disk sufficiently far
right. The theorem treats arbitrary finite sets of real slopes.
-/

open Complex Metric Set

namespace RHTower

/-- Exact modulus of another exponential mark on a chosen logarithmic value. -/
theorem norm_xi_tilt_of_log_value {a b : ℝ} {s w : ℂ}
    (h : xi s * Complex.exp (-(a : ℂ) * s) = Complex.exp w) :
    ‖xi s * Complex.exp (-(b : ℂ) * s)‖ =
      Real.exp (w.re + (a - b) * s.re) := by
  have he : xi s * Complex.exp (-(b : ℂ) * s) =
      Complex.exp (w + ((a - b : ℝ) : ℂ) * s) := by
    rw [Complex.exp_add, ← h, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Each finite family admits a logarithmic island with all other marks off the unit circle. -/
theorem exists_xi_tilt_exp_lift_ball_separated (A : Finset ℝ) (a M R : ℝ) (hM : 0 < M) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 M) ∧
      ∀ w ∈ ball 0 M, R < (h w).re ∧
        xi (h w) * Complex.exp (-(a : ℂ) * h w) = Complex.exp w ∧
        ∀ b ∈ A, b ≠ a → ‖xi (h w) * Complex.exp (-(b : ℂ) * h w)‖ ≠ 1 := by
  classical
  let Q : ℝ := ∑ b ∈ A, (M + 1) / |a - b|
  have hnonneg : ∀ b ∈ A, 0 ≤ (M + 1) / |a - b| := by
    intro b _
    positivity
  have hQ : 0 ≤ Q := Finset.sum_nonneg hnonneg
  obtain ⟨h, hhd, hh⟩ := exists_xi_tilt_exp_lift_ball a M (max R (Q + 1)) hM
  refine ⟨h, hhd, fun w hw => ?_⟩
  obtain ⟨hwr, hwe⟩ := hh w hw
  have hq : Q + 1 < (h w).re := (le_max_right _ _).trans_lt hwr
  have hpos : 0 < (h w).re := by linarith
  refine ⟨(le_max_left _ _).trans_lt hwr, hwe, fun b hb hba he => ?_⟩
  have hab : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hba.symm)
  have hbQ : (M + 1) / |a - b| ≤ Q := Finset.single_le_sum hnonneg hb
  have hsep : M < |a - b| * (h w).re := by
    have hh := (div_le_iff₀ hab).mp hbQ
    nlinarith
  rw [norm_xi_tilt_of_log_value hwe, Real.exp_eq_one_iff] at he
  have heabs : |a - b| * (h w).re = |w.re| := by
    rw [← abs_of_pos hpos, ← abs_mul]
    rw [show (a - b) * (h w).re = -w.re by linarith, abs_neg]
  have hwM : ‖w‖ < M := by simpa using hw
  have hwre := (Complex.abs_re_le_norm w).trans_lt hwM
  linarith

end RHTower
