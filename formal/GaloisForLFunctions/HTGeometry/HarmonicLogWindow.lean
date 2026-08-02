import Mathlib.NumberTheory.Harmonic.Bounds
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


/-! ## Window sums of reciprocals -/

theorem harmonic_eq_sum_Ioc (n : ℕ) :
    (harmonic n : ℝ) = ∑ i ∈ Finset.Ioc 0 n, ((i : ℝ))⁻¹ := by
  have hset : Finset.Ioc 0 n = Finset.Icc 1 n := rfl
  rw [hset, harmonic_eq_sum_Icc, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- A window sum of reciprocals is a difference of harmonic numbers. -/
theorem sum_Ioc_inv_eq_harmonic_sub {m N : ℕ} (h : m ≤ N) :
    ∑ n ∈ Finset.Ioc m N, ((n : ℝ))⁻¹ = (harmonic N : ℝ) - harmonic m := by
  have hsplit := Finset.sum_Ioc_consecutive (fun i : ℕ => ((i : ℝ))⁻¹) (Nat.zero_le m) h
  rw [harmonic_eq_sum_Ioc, harmonic_eq_sum_Ioc]
  linarith [hsplit]

/-- **Window sum versus logarithm.**  A sum of reciprocals over `(m, N]` differs from the logarithm
of the endpoint ratio by at most the sum of the reciprocals of the endpoints. -/
theorem abs_sum_Ioc_inv_sub_log_le {m N : ℕ} (hm : 1 ≤ m) (h : m ≤ N) :
    |(∑ n ∈ Finset.Ioc m N, ((n : ℝ))⁻¹) - (Real.log N - Real.log m)| ≤ 1 / N + 1 / m := by
  rw [sum_Ioc_inv_eq_harmonic_sub h]
  exact abs_harmonic_window_sub_log_le hm (le_trans hm h)


/-- **Logarithm on a unit index window.**  Between consecutive integers the logarithm moves by at
most the reciprocal of the smaller one. -/
theorem abs_log_sub_log_le_inv {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (h1 : (n : ℝ) ≤ x) (h2 : x ≤ (n : ℝ) + 1) :
    |Real.log x - Real.log n| ≤ 1 / n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hnpos h1
  have hlow : Real.log n ≤ Real.log x := Real.log_le_log hnpos h1
  have hhigh : Real.log x ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hxpos h2
  have hgap : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) (ne_of_gt hnpos)]
    have hx : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
    rw [hx]
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (n : ℝ)) (by positivity)
    linarith
  rw [abs_le]
  constructor <;> linarith

end HTGeometry
