import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The harmonic summatory with Euler–Mascheroni error `O(1/N)`

`∑_{i ≤ N} 1/i = log N + γ + O(1/N)`, in the exact form

`0 < ∑_{i ≤ N} 1/i − log N − γ ≤ 1/N`.

Both sides come from the strict monotone sandwich
`eulerMascheroniSeq N < γ < eulerMascheroniSeq' N`: the upper error is
`log(N+1) − log N ≤ 1/N`.  This is the precision of the harmonic input
consumed by the Tatuzawa–Iseki assembly of Selberg's symmetry formula.
-/

noncomputable section

namespace RHTower

/-- The real harmonic partial sum is the cast of `harmonic`. -/
theorem sum_inv_Icc_eq_ratCast_harmonic (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, ((i : ℝ))⁻¹ = ((harmonic N : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

/-- **Harmonic summatory with `O(1/N)` error**:
`|∑_{i ≤ N} 1/i − log N − γ| ≤ 1/N`. -/
theorem abs_sum_inv_sub_log_sub_mascheroni_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ i ∈ Finset.Icc 1 N, ((i : ℝ))⁻¹ - Real.log N
        - Real.eulerMascheroniConstant| ≤ 1 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  unfold Real.eulerMascheroniSeq at h1
  unfold Real.eulerMascheroniSeq' at h2
  rw [if_neg (by omega : ¬ N = 0)] at h2
  have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by positivity) hN0.ne']
    have hle := Real.log_le_sub_one_of_pos
      (x := ((N : ℝ) + 1) / N) (by positivity)
    have heq : ((N : ℝ) + 1) / N - 1 = 1 / N := by
      field_simp
      ring
    linarith
  rw [sum_inv_Icc_eq_ratCast_harmonic, abs_of_pos (by linarith)]
  linarith

end RHTower
