import GaloisForLFunctions.RHTower.PsiRemainderWindowSmallValue

/-!
# The one-sided window average of the remainder

If `R ≥ −ε·id` on a window `(y, z]` — as slow variation guarantees above
every small-value point — then the harmonically weighted *absolute*
remainder average is bounded by a constant plus `ε`-terms:

`∑_{y < n ≤ z} |R(n)|·(1/n − 1/(n+1)) ≤ 40 + 2ε·(log(z/y) + 1)`,

via `|x| = x + 2·max(−x, 0)`: the signed sum is the windowed harmonic
bound (`≤ 40`), and the negative part is pointwise `≤ ε·n`.  Against the
trivial bound `a·log(z/y)` this is the strict gain the Erdős–Selberg
contraction extracts on windows above small-value points.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `1/(n+1) ≤ log(n+1) − log n` for `n ≥ 1`. -/
theorem inv_succ_le_log_succ_sub {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Real.log_le_sub_one_of_pos
    (x := (n : ℝ) / ((n : ℝ) + 1)) (by positivity)
  rw [Real.log_div hn0.ne' (by positivity : ((n : ℝ) + 1) ≠ 0)] at h
  have heq : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
    field_simp
    ring
  rw [heq] at h
  linarith

/-- Windowed harmonic upper bound:
`∑_{y < n ≤ z} 1/(n+1) ≤ log z − log y + 1`. -/
theorem sum_inv_succ_window_le {y z : ℕ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1)
      ≤ Real.log z - Real.log y + 1 := by
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hterm : ∀ n ∈ Finset.Ioc y z,
      1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact inv_succ_le_log_succ_sub (by omega)
  have htel : ∑ n ∈ Finset.Ioc y z,
      (Real.log ((n : ℝ) + 1) - Real.log n)
      = Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1) := by
    have hIco : Finset.Ioc y z = Finset.Ico (y + 1) (z + 1) := by
      ext x
      rw [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hcongr : ∑ n ∈ Finset.Ioc y z,
        (Real.log ((n : ℝ) + 1) - Real.log n)
        = ∑ n ∈ Finset.Ioc y z,
            (Real.log (((n + 1 : ℕ)) : ℝ) - Real.log ((n : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    rw [hcongr, hIco, Finset.sum_Ico_eq_sub _ (show y + 1 ≤ z + 1 by omega),
      Finset.sum_range_sub (fun n => Real.log ((n : ℕ) : ℝ)) (z + 1),
      Finset.sum_range_sub (fun n => Real.log ((n : ℕ) : ℝ)) (y + 1)]
    push_cast
    ring
  have hup : Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1)
      ≤ Real.log z - Real.log y + 1 := by
    have h1 : Real.log ((z : ℝ) + 1) ≤ Real.log z + 1 := by
      have h2 := log_succ_sub_log_le (le_trans hy hyz)
      have h3 : (1 : ℝ) / z ≤ 1 := by
        rw [div_le_one hz0]
        exact_mod_cast le_trans hy hyz
      linarith
    have h4 : Real.log y ≤ Real.log ((y : ℝ) + 1) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < y))
      linarith
    linarith
  calc ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1)
      ≤ ∑ n ∈ Finset.Ioc y z,
          (Real.log ((n : ℝ) + 1) - Real.log n) :=
        Finset.sum_le_sum hterm
    _ = Real.log ((z : ℝ) + 1) - Real.log ((y : ℝ) + 1) := htel
    _ ≤ Real.log z - Real.log y + 1 := hup

/-- **One-sided window average (the gain engine)**: if `R ≥ −ε·id` on
`(y, z]`, then
`∑_{y < n ≤ z} |R(n)|(1/n − 1/(n+1)) ≤ 40 + 2ε(log(z/y) + 1)`. -/
theorem sum_abs_psiRemainder_window_le_of_lower {y z : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hy : 1 ≤ y) (hyz : y ≤ z)
    (hlow : ∀ n ∈ Finset.Ioc y z, -(ε * n) ≤ psiRemainder n) :
    ∑ n ∈ Finset.Ioc y z,
        |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
      ≤ 40 + 2 * ε * (Real.log z - Real.log y + 1) := by
  have hwpos : ∀ n ∈ Finset.Ioc y z,
      (0 : ℝ) ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [sub_nonneg]
    apply div_le_div_of_nonneg_left one_pos.le hn0
    linarith
  have hnw : ∀ n ∈ Finset.Ioc y z,
      (n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    field_simp
    ring
  -- split `|R| = R + 2·max(−R, 0)`
  have hsplit : ∀ n ∈ Finset.Ioc y z,
      |psiRemainder n| * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
        = psiRemainder n * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          + 2 * (max (-psiRemainder n) 0
              * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
    intro n _
    rcases le_or_gt 0 (psiRemainder n) with h0 | h0
    · rw [abs_of_nonneg h0, max_eq_right (by linarith)]
      ring
    · rw [abs_of_neg h0, max_eq_left (by linarith)]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- signed part
  have hsigned := (abs_le.1
    (abs_windowed_psiRemainder_harmonic_le hy hyz)).2
  -- negative part
  have hnegpart : ∑ n ∈ Finset.Ioc y z,
      2 * (max (-psiRemainder n) 0 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
      ≤ 2 * ε * (Real.log z - Real.log y + 1) := by
    have hterm : ∀ n ∈ Finset.Ioc y z,
        2 * (max (-psiRemainder n) 0 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
          ≤ 2 * ε * (1 / ((n : ℝ) + 1)) := by
      intro n hn
      have hmax : max (-psiRemainder n) 0 ≤ ε * n := by
        apply max_le _ (by positivity)
        have := hlow n hn
        linarith
      have h1 : max (-psiRemainder n) 0
          * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          ≤ (ε * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hmax (hwpos n hn)
      have h2 : (ε * n) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          = ε * ((n : ℝ) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by
        ring
      rw [h2, hnw n hn] at h1
      linarith
    calc ∑ n ∈ Finset.Ioc y z,
          2 * (max (-psiRemainder n) 0
            * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
        ≤ ∑ n ∈ Finset.Ioc y z, 2 * ε * (1 / ((n : ℝ) + 1)) :=
          Finset.sum_le_sum hterm
      _ = 2 * ε * ∑ n ∈ Finset.Ioc y z, 1 / ((n : ℝ) + 1) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * ε * (Real.log z - Real.log y + 1) := by
          apply mul_le_mul_of_nonneg_left
            (sum_inv_succ_window_le hy hyz) (by positivity)
  linarith

end RHTower
