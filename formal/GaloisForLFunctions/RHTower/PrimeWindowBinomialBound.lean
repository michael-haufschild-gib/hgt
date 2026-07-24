import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory

/-!
# The binomial bound for prime log-mass in short windows

For `x < y ≤ 2x`, every prime in `(x, y]` divides `C(y, y−x)`, so

`∑_{p prime ∈ (x,y]} log p ≤ log C(y, y−x) ≤ (y−x)·(log y − log(y−x) + 1)`,

using `C(y,k)·k! = y·(y−1)⋯(y−k+1) ≤ y^k` and the Stirling lower bound
`log k! ≥ k log k − k + 1`.  For a window of relative width `ρ` this is
`ρ·x·(log(1/ρ) + O(1))` — the elementary Brun–Titchmarsh-type upper bound
that provides the two-sided slow-variation control around small-value
points of `ψ − id`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- `log k! = ∑_{m ≤ k} log m`. -/
private theorem log_factorial_eq (k : ℕ) :
    Real.log ((k.factorial : ℕ) : ℝ) = ∑ m ∈ Finset.Icc 1 k, Real.log m := by
  rw [Nat.factorial_eq_prod_range_add_one]
  push_cast
  have hne : ∀ i ∈ Finset.range k, ((i : ℝ) + 1) ≠ 0 := fun i _ => by
    positivity
  rw [Real.log_prod hne]
  apply Finset.sum_nbij' (i := fun i => i + 1) (j := fun m => m - 1)
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_range]
    omega
  · intro i _
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    omega
  · intro i _
    push_cast
    ring_nf

/-- `log C(y,k) ≤ k(log y − log k + 1)` for `1 ≤ k ≤ y`. -/
theorem log_choose_le {y k : ℕ} (hk : 1 ≤ k) (hky : k ≤ y) :
    Real.log ((y.choose k : ℕ) : ℝ)
      ≤ (k : ℝ) * (Real.log y - Real.log k + 1) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have h1 : y.choose k * k.factorial ≤ y ^ k := by
    calc y.choose k * k.factorial = k.factorial * y.choose k := mul_comm _ _
      _ = y.descFactorial k :=
        (Nat.descFactorial_eq_factorial_mul_choose y k).symm
      _ ≤ y ^ k := Nat.descFactorial_le_pow y k
  have hchoose0 : 0 < y.choose k := Nat.choose_pos hky
  have hfact0 : 0 < k.factorial := Nat.factorial_pos k
  have h2 : Real.log ((y.choose k : ℕ) : ℝ)
      + Real.log ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) * Real.log y := by
    rw [← Real.log_mul (by exact_mod_cast hchoose0.ne')
      (by exact_mod_cast hfact0.ne'), ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h1
  have h3 : (k : ℝ) * Real.log k - k + 1
      ≤ Real.log ((k.factorial : ℕ) : ℝ) := by
    rw [log_factorial_eq]
    exact stirling_le_sum_log k hk
  linarith

/-- **Prime log-mass in a short window**: for `x < y ≤ 2x`,
`∑_{p prime ∈ (x,y]} log p ≤ (y−x)(log y − log(y−x) + 1)`. -/
theorem sum_primes_log_window_le {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y)
    (hy2 : y ≤ 2 * x) :
    ∑ p ∈ (Finset.Ioc x y).filter Nat.Prime, Real.log p
      ≤ ((y - x : ℕ) : ℝ)
        * (Real.log y - Real.log ((y - x : ℕ) : ℝ) + 1) := by
  set k := y - x with hkdef
  set S := (Finset.Ioc x y).filter Nat.Prime with hSdef
  have hdvd : (∏ p ∈ S, p) ∣ y.choose k := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact ((Finset.mem_filter.1 hp).2).prime
    · intro p hp
      obtain ⟨hmem, hprime⟩ := Finset.mem_filter.1 hp
      rw [Finset.mem_Ioc] at hmem
      exact hprime.dvd_choose (by omega) (by omega) hmem.2
  have hchoose0 : 0 < y.choose k := Nat.choose_pos (by omega)
  have hle : (∏ p ∈ S, p) ≤ y.choose k := Nat.le_of_dvd hchoose0 hdvd
  have hprod0 : 0 < ∏ p ∈ S, p := by
    apply Finset.prod_pos
    intro p hp
    exact ((Finset.mem_filter.1 hp).2).pos
  have hlogsum : ∑ p ∈ S, Real.log p
      = Real.log (((∏ p ∈ S, p : ℕ)) : ℝ) := by
    push_cast
    rw [Real.log_prod]
    intro p hp
    have := ((Finset.mem_filter.1 hp).2).pos
    exact_mod_cast (by omega : p ≠ 0)
  rw [hlogsum]
  calc Real.log (((∏ p ∈ S, p : ℕ)) : ℝ)
      ≤ Real.log ((y.choose k : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hprod0) (by exact_mod_cast hle)
    _ ≤ (k : ℝ) * (Real.log y - Real.log k + 1) :=
        log_choose_le (by omega) (by omega)

end RHTower
