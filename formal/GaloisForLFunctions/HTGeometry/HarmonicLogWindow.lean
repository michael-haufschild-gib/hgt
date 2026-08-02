import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Sharp harmonic-versus-logarithm comparison

Mathlib sandwiches the Euler--Mascheroni constant between `harmonic n - log (n+1)` and
`harmonic n - log n`.  Reading the sandwich in the other direction bounds the harmonic number by its
logarithm with error `1/n`:

`|harmonic n - log n - gamma| ≤ 1/n`.

Summing the bound at the two ends of a window gives the comparison of a harmonic window sum with the
logarithm of the ratio, again with error the reciprocals of the endpoints.  This is the rate that
makes a multiplicative Riemann sum of mesh `1/N` converge like `1/N`.
-/

open Real

noncomputable section

namespace HTGeometry

/-- **Sharp harmonic comparison.**  The harmonic number is its logarithm plus the
Euler--Mascheroni constant, with error at most `1/n`. -/
theorem abs_harmonic_sub_log_sub_eulerMascheroni_le {n : ℕ} (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - eulerMascheroniConstant| ≤ 1 / n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hupper : eulerMascheroniConstant < (harmonic n : ℝ) - Real.log n := by
    have := eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    rwa [eulerMascheroniSeq', if_neg hn0] at this
  have hlower : (harmonic n : ℝ) - Real.log (n + 1) < eulerMascheroniConstant := by
    have := eulerMascheroniSeq_lt_eulerMascheroniConstant n
    rwa [eulerMascheroniSeq] at this
  have hlog : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) (ne_of_gt hnpos)]
    have hx : ((n : ℝ) + 1) / n = 1 + 1 / n := by
      field_simp
    rw [hx]
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (n : ℝ)) (by positivity)
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **Harmonic window comparison.**  A harmonic sum over a window compares with the logarithm of the
endpoint ratio, with error the sum of the reciprocals of the endpoints. -/
theorem abs_harmonic_window_sub_log_le {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    |((harmonic N : ℝ) - harmonic m) - (Real.log N - Real.log m)| ≤ 1 / N + 1 / m := by
  have h1 := abs_harmonic_sub_log_sub_eulerMascheroni_le hN
  have h2 := abs_harmonic_sub_log_sub_eulerMascheroni_le hm
  have hsplit :
      ((harmonic N : ℝ) - harmonic m) - (Real.log N - Real.log m) =
        ((harmonic N : ℝ) - Real.log N - eulerMascheroniConstant) -
          ((harmonic m : ℝ) - Real.log m - eulerMascheroniConstant) := by
    ring
  rw [hsplit]
  exact le_trans (abs_sub _ _) (add_le_add h1 h2)

end HTGeometry
