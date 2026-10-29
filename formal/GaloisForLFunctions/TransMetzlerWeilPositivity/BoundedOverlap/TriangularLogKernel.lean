import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing
import GaloisForLFunctions.HTGeometry.IntegerLogGap
import GaloisForLFunctions.HTGeometry.FiniteKernelErrorFromDistanceRows

/-!
# A triangular Fourier window for logarithmic atoms

The off-diagonal kernel decays quadratically in the logarithmic gap.
Integer separation makes its complete row cost `16 N² / T`. Consequently
windows of width proportional to the horizon retain a fixed coefficient
mass, uniformly in their center.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open HTGeometry

/-- The real triangular Fourier kernel, with its diagonal removed. -/
def triangularLogOffKernel (T τ : ℝ) (n j : ℕ) : ℝ :=
  if n = j then 0 else
    Real.cos (τ * (Real.log n - Real.log j)) *
      (2 - 2 * Real.cos (T * (Real.log n - Real.log j))) /
        (T * (Real.log n - Real.log j) ^ 2)

/-- Integer logarithmic separation gives a square-distance kernel bound. -/
theorem triangularLogOffKernel_bound {T : ℝ} (hT : 0 < T) (τ : ℝ)
    {n j : ℕ} (hn : 0 < n) (hj : 0 < j) :
    |triangularLogOffKernel T τ n j| ≤
      (4 / T) * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
  by_cases hnj : n = j
  · subst j
    simp only [triangularLogOffKernel, if_pos rfl, abs_zero, sub_self, zero_pow
      (by norm_num : (2 : ℕ) ≠ 0), div_zero, le_refl]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hdist : 0 < |(n : ℝ) - j| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hnj))
  have hmax : 0 < max (n : ℝ) j := hnR.trans_le (le_max_left _ _)
  have hgap := gap_div_le_abs_log_div hn hj hnj
  rw [Real.log_div hnR.ne' hjR.ne'] at hgap
  have hd : 0 < |Real.log n - Real.log j| := (div_pos hdist hmax).trans_le hgap
  have hinv : 1 / |Real.log n - Real.log j| ≤ max (n : ℝ) j / |(n : ℝ) - j| := by
    have h := one_div_le_one_div_of_le (div_pos hdist hmax) hgap
    simpa only [one_div_div] using h
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / |Real.log n - Real.log j|) hinv 2
  have hnum : |Real.cos (τ * (Real.log n - Real.log j)) *
      (2 - 2 * Real.cos (T * (Real.log n - Real.log j)))| ≤ 4 := by
    have hcos := Real.abs_cos_le_one (τ * (Real.log n - Real.log j))
    have hc := Real.cos_le_one (T * (Real.log n - Real.log j))
    have hl := Real.neg_one_le_cos (T * (Real.log n - Real.log j))
    have hp : |2 - 2 * Real.cos (T * (Real.log n - Real.log j))| ≤ 4 :=
      abs_le.mpr ⟨by linarith only [hc], by linarith only [hl]⟩
    rw [abs_mul]
    exact (mul_le_mul hcos hp (abs_nonneg _) zero_le_one).trans_eq (by ring)
  rw [triangularLogOffKernel, if_neg hnj, abs_div,
    abs_of_pos (mul_pos hT (sq_pos_of_ne_zero (abs_pos.mp hd)))]
  calc
    _ ≤ 4 / (T * (Real.log n - Real.log j) ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (4 / T) * (1 / |Real.log n - Real.log j|) ^ 2 := by rw [div_pow, sq_abs]; ring
    _ ≤ (4 / T) * (max (n : ℝ) j / |(n : ℝ) - j|) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [div_pow]; ring

/-- The real window kernel is symmetric at every center. -/
theorem triangularLogOffKernel_comm (T τ : ℝ) (n j : ℕ) :
    triangularLogOffKernel T τ n j = triangularLogOffKernel T τ j n := by
  by_cases h : n = j
  · subst j; rfl
  rw [triangularLogOffKernel, triangularLogOffKernel, if_neg h, if_neg h.symm,
    show Real.log j - Real.log n = -(Real.log n - Real.log j) by ring,
    mul_neg, mul_neg, Real.cos_neg, Real.cos_neg, neg_sq]

/-- The signed complete off-diagonal costs only an inverse-width square-distance row. -/
theorem triangularLogOffKernel_quadratic_bound {T : ℝ} (hT : 0 < T)
    (τ : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * triangularLogOffKernel T τ n j| ≤
      (16 * (N : ℝ) ^ 2 / T) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have h := abs_kernel_quadratic_le_of_integer_distance (N := N)
    (by positivity : (0 : ℝ) ≤ 4 / T)
    (fun n hn j hj => triangularLogOffKernel_bound hT τ (mem_Icc.mp hn).1 (mem_Icc.mp hj).1)
    (fun n _ j _ => triangularLogOffKernel_comm T τ n j) x
  convert h using 1 <;> ring

/-- At half-width `8 N`, the full triangular kernel has a uniform positive floor. -/
theorem triangularLogKernel_lower {N : ℕ} (hN : 0 < N) (τ : ℝ) (x : ℕ → ℝ) :
    (6 * (N : ℝ)) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      (8 * (N : ℝ)) * (∑ n ∈ Icc 1 N, x n ^ 2) +
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          x n * x j * triangularLogOffKernel (8 * N) τ n j := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (abs_le.mp (triangularLogOffKernel_quadratic_bound (by positivity : (0 : ℝ) < 8 * N)
    τ N x)).1
  have hcost : 16 * (N : ℝ) ^ 2 / (8 * N) = 2 * N := by field_simp [hNR.ne']; ring
  rw [hcost] at h
  linarith only [h]

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.triangularLogKernel_lower
