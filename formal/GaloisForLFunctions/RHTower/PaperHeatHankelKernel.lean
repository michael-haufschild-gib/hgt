import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminants
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-! # A source-normalized full heat-Hankel kernel

Every moment and every signed cross term is retained. Positive diagonal scaling
by the absolute heat-source budgets gives an absolutely summable kernel without
assuming a sign for any Hankel form.
-/

namespace RHTower.PaperHeatHankel
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

abbrev Time := {a : ℝ // 0 < a}

def budget (a : Time) (n : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * n) *
    Real.exp (-(a.val * (xiHeatFrequency q).re))

theorem budget_nonneg (a : Time) (n : ℕ) : 0 ≤ budget a n :=
  tsum_nonneg fun _ => by positivity

theorem summable_budget (a : Time) (n : ℕ) :
    Summable fun q : XiZeroCopy => (1 + ‖xiHeatFrequency q‖) ^ (2 * n) *
      Real.exp (-(a.val * (xiHeatFrequency q).re)) :=
  summable_one_add_norm_pow_mul_exp a.property _

theorem norm_moment_le (a : Time) (i j : ℕ) :
    ‖xiHeatMoment (i + j) a.val‖ ≤ budget a i + budget a j := by
  have hs := summable_pow_mul_exp_xiHeatFrequency a.property (i + j)
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [budget, budget, ← (summable_budget a i).tsum_add (summable_budget a j)]
  apply hs.norm.tsum_le_tsum _ ((summable_budget a i).add (summable_budget a j))
  intro q
  rw [norm_mul, norm_pow, Complex.norm_exp]
  have hre : (-(a.val : ℂ) * xiHeatFrequency q).re =
      -(a.val * (xiHeatFrequency q).re) := by simp
  rw [hre, ← add_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hbase : 1 ≤ 1 + ‖xiHeatFrequency q‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hp := pow_le_pow_left₀ (norm_nonneg (xiHeatFrequency q))
    (show ‖xiHeatFrequency q‖ ≤ 1 + ‖xiHeatFrequency q‖ by linarith) (i + j)
  rcases le_total i j with h | h
  · exact hp.trans ((pow_le_pow_right₀ hbase (show i + j ≤ 2 * j by omega)).trans
      (le_add_of_nonneg_left (by positivity)))
  · exact hp.trans ((pow_le_pow_right₀ hbase (show i + j ≤ 2 * i by omega)).trans
      (le_add_of_nonneg_right (by positivity)))

def scale (a : Time) (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / (1 + budget a n)

theorem scale_pos (a : Time) (n : ℕ) : 0 < scale a n := by
  unfold scale
  positivity [budget_nonneg a n]

def kernel (a : Time) (p : ℕ × ℕ) : ℂ :=
  (scale a p.1 : ℂ) * xiHeatMoment (p.1 + p.2) a.val * (scale a p.2 : ℂ)

theorem kernel_symm (a : Time) (i j : ℕ) : kernel a (i,j) = kernel a (j,i) := by
  simp only [kernel, Nat.add_comm i j]
  ring

theorem kernel_conj (a : Time) (p : ℕ × ℕ) : star (kernel a p) = kernel a p := by
  simp only [kernel, star_mul, Complex.star_def, Complex.conj_ofReal,
    conj_xiHeatMoment]
  ring

theorem norm_kernel_le (a : Time) (i j : ℕ) :
    ‖kernel a (i,j)‖ ≤ (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ j := by
  have hi := budget_nonneg a i
  have hj := budget_nonneg a j
  have hib : 0 < 1 + budget a i := by positivity
  have hjb : 0 < 1 + budget a j := by positivity
  have hm : ‖xiHeatMoment (i + j) a.val‖ ≤ (1 + budget a i) * (1 + budget a j) :=
    (norm_moment_le a i j).trans (by nlinarith [mul_nonneg hi hj])
  rw [kernel, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (scale_pos a i),
    abs_of_pos (scale_pos a j)]
  calc scale a i * ‖xiHeatMoment (i + j) a.val‖ * scale a j
      ≤ scale a i * ((1 + budget a i) * (1 + budget a j)) * scale a j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (scale_pos a i).le) (scale_pos a j).le
    _ = (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ j := by
      unfold scale
      field_simp

theorem summable_kernel_norm (a : Time) : Summable fun p : ℕ × ℕ => ‖kernel a p‖ := by
  have h : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact (h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => norm_kernel_le a p.1 p.2)

theorem kernel_isHS (a : Time) : HilbertSchmidt.IsHS (kernel a) := by
  have h : Summable fun n : ℕ => ((1 / 2 : ℝ) ^ n) ^ 2 := by
    exact (summable_geometric_of_norm_lt_one
      (show ‖(1 / 2 : ℝ) ^ 2‖ < 1 by norm_num)).congr fun n => by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  have hs := h.mul_of_nonneg h (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro p
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_kernel_le a p.1 p.2) 2

end
end RHTower.PaperHeatHankel
