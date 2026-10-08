import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialWeight

/-!
# Finite Dirichlet polynomial weights with literal ratio expansion

The critical-line square and every ratio in the contour expansion retain
their original coefficients. Bounds here allow arbitrary finite length.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceFiniteFactor (N : ℕ) (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, (c m : ℂ) * Complex.exp (-(Real.log m : ℂ) * s)

def sourceFiniteWeight (N : ℕ) (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  sourceFiniteFactor N c s * sourceFiniteFactor N c (1 - s)

theorem differentiable_sourceFiniteWeight (N : ℕ) (c : ℕ → ℝ) :
    Differentiable ℂ (sourceFiniteWeight N c) := by
  unfold sourceFiniteWeight sourceFiniteFactor
  fun_prop

theorem sourceFiniteFactor_conj (N : ℕ) (c : ℕ → ℝ) (s : ℂ) :
    sourceFiniteFactor N c (conj s) = conj (sourceFiniteFactor N c s) := by
  simp only [sourceFiniteFactor, map_sum, map_mul, map_neg,
    conj_ofReal, ← Complex.exp_conj]

theorem sourceFiniteWeight_conj (N : ℕ) (c : ℕ → ℝ) (s : ℂ) :
    sourceFiniteWeight N c (conj s) = conj (sourceFiniteWeight N c s) := by
  simp only [sourceFiniteWeight, map_mul, ← sourceFiniteFactor_conj]
  congr 1
  simp

theorem sourceFiniteWeight_one_sub (N : ℕ) (c : ℕ → ℝ) (s : ℂ) :
    sourceFiniteWeight N c (1 - s) = sourceFiniteWeight N c s := by
  simp only [sourceFiniteWeight, sub_sub_cancel, mul_comm]

theorem sourceFiniteWeight_critical (N : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    sourceFiniteWeight N c ((1 / 2 : ℂ) + t * I) =
      ((‖sourceFiniteFactor N c ((1 / 2 : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  unfold sourceFiniteWeight
  rw [show 1 - ((1 / 2 : ℂ) + t * I) = conj ((1 / 2 : ℂ) + t * I) by
    simp only [map_add, map_div₀, map_ofNat, map_one, map_mul, conj_ofReal, conj_I]; ring,
    sourceFiniteFactor_conj, Complex.mul_conj']
  norm_cast

private theorem norm_sourceFiniteFactor_le (N : ℕ) (c : ℕ → ℝ)
    {s : ℂ} (hs : -(1 / 2) ≤ s.re) :
    ‖sourceFiniteFactor N c s‖ ≤
      ∑ m ∈ Finset.Icc 1 N, |c m| * Real.exp (2 * Real.log m) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hl : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  nlinarith

theorem exists_sourceFiniteWeight_strip_bound (N : ℕ) (c : ℕ → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 2 →
      ‖sourceFiniteWeight N c s‖ ≤ B := by
  let A : ℝ := ∑ m ∈ Finset.Icc 1 N, |c m| * Real.exp (2 * Real.log m)
  have hA : 0 ≤ A := Finset.sum_nonneg fun m _ => by positivity
  refine ⟨A ^ 2, sq_nonneg _, fun s hs0 hs1 => ?_⟩
  unfold sourceFiniteWeight
  rw [norm_mul, pow_two]
  exact mul_le_mul (norm_sourceFiniteFactor_le N c (by linarith))
    (norm_sourceFiniteFactor_le N c (by simp only [Complex.sub_re, Complex.one_re]; linarith))
    (norm_nonneg _) hA

private theorem finite_factor_pair_eq_ratio {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (s : ℂ) :
    Complex.exp (-(Real.log m : ℂ) * s) *
      Complex.exp (-(Real.log n : ℂ) * (1 - s)) =
        (1 / (m : ℂ)) * (((m : ℝ) / n : ℝ) : ℂ) ^ (1 - s) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (0 : ℝ) < (m : ℝ) / n := div_pos hmR hnR
  have hlog : Complex.log (((m : ℝ) / n : ℝ) : ℂ) =
      (Real.log m : ℂ) - (Real.log n : ℂ) := by
    rw [← Complex.ofReal_log hr.le, Real.log_div hmR.ne' hnR.ne', Complex.ofReal_sub]
  have he : Complex.exp (-(Real.log m : ℂ)) = 1 / (m : ℂ) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hmR]
    simp only [one_div, Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), hlog, ← he,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- Exact finite expansion in the scaled-contour normalization. -/
theorem sourceFiniteWeight_expansion (N : ℕ) (c : ℕ → ℝ) (s : ℂ) :
    sourceFiniteWeight N c s =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ((c m : ℂ) * c n / m) * (((m : ℝ) / n : ℝ) : ℂ) ^ (1 - s) := by
  unfold sourceFiniteWeight sourceFiniteFactor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
  calc
    _ = ((c m : ℂ) * c n) * (Complex.exp (-(Real.log m : ℂ) * s) *
        Complex.exp (-(Real.log n : ℂ) * (1 - s))) := by ring
    _ = _ := by rw [finite_factor_pair_eq_ratio hm0 hn0]; ring

/-- The pole coefficient is the product of two literal finite arithmetic sums. -/
theorem sourceFiniteWeight_one (N : ℕ) (c : ℕ → ℝ) :
    sourceFiniteWeight N c 1 =
      (∑ m ∈ Finset.Icc 1 N, (c m : ℂ) / m) *
        (∑ n ∈ Finset.Icc 1 N, (c n : ℂ)) := by
  have h1 : sourceFiniteFactor N c 1 = ∑ m ∈ Finset.Icc 1 N, (c m : ℂ) / m := by
    unfold sourceFiniteFactor
    apply Finset.sum_congr rfl
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [mul_one, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hmR]
    simp only [Complex.ofReal_natCast, div_eq_mul_inv]
  have h0 : sourceFiniteFactor N c 0 = ∑ m ∈ Finset.Icc 1 N, (c m : ℂ) := by
    simp only [sourceFiniteFactor, mul_zero, Complex.exp_zero, mul_one]
  simp only [sourceFiniteWeight, sub_self, h1, h0]

theorem norm_sourceFiniteWeight_one_le (N : ℕ) (c : ℕ → ℝ) :
    ‖sourceFiniteWeight N c 1‖ ≤
      (∑ m ∈ Finset.Icc 1 N, |c m| / m) * (∑ n ∈ Finset.Icc 1 N, |c n|) := by
  rw [sourceFiniteWeight_one, norm_mul]
  apply mul_le_mul _ _ (norm_nonneg _) (Finset.sum_nonneg fun m _ => by positivity)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro m _
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, le_refl]
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n _
    simp only [Complex.norm_real, Real.norm_eq_abs, le_refl]

end RHTower.WeilSingularArithmetic
