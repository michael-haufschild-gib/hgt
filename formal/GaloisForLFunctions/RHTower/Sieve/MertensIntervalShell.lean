import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Mertens' first theorem on an interval, and the cofactor-shell weights

Subtracting the two sides of Mertens' first theorem bounds the prime harmonic sum on any interval
by its logarithmic length plus an absolute constant.  Dividing by a lower bound for the cofactor
logarithm gives the two shell estimates the Granville--Harper--Soundararajan argument uses.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The absolute constant in Mertens' first theorem on an interval. -/
def mertensIntervalConst : ℝ := Real.log 4 + 1 + 2 * logSqTailConst

theorem mertensIntervalConst_nonneg : 0 ≤ mertensIntervalConst := by
  have h1 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 := logSqTailConst_nonneg
  rw [mertensIntervalConst]
  linarith

theorem primesLE_subset_of_le {a b : ℕ} (hab : a ≤ b) : Nat.primesLE a ⊆ Nat.primesLE b := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨le_trans hp.1 hab, hp.2⟩

/-- **(A3).**  Mertens' first theorem on an interval, with an absolute additive constant. -/
theorem sum_log_div_prime_interval_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    {s : Finset ℕ} (hs : s ⊆ Nat.primesLE b \ Nat.primesLE a) :
    ∑ p ∈ s, Real.log p / (p : ℝ)
      ≤ Real.log b - Real.log a + mertensIntervalConst := by
  classical
  have hnn : ∀ p ∈ Nat.primesLE b \ Nat.primesLE a, 0 ≤ Real.log p / (p : ℝ) := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
    have hp2 := hp.1.2.two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    positivity
  have hmono : ∑ p ∈ s, Real.log p / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun i hi _ => hnn i hi)
  refine le_trans hmono ?_
  have hsplit : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ)
      = (∑ p ∈ Nat.primesLE b, Real.log p / (p : ℝ))
        - ∑ p ∈ Nat.primesLE a, Real.log p / (p : ℝ) := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff (primesLE_subset_of_le hab)]
  rw [hsplit]
  have hb1 : 1 ≤ b := le_trans ha hab
  have hup := mertensFirst_upper hb1
  have hlo := mertensFirst_lower ha
  rw [mertensIntervalConst]
  linarith

/-- **(A4).**  On a shell where the cofactor logarithm is at least `u`, the reciprocal-weighted
prime sum is `(interval length + C)/u`. -/
theorem sum_log_div_prime_mul_weight_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    {s : Finset ℕ} (hs : s ⊆ Nat.primesLE b \ Nat.primesLE a)
    {v : ℕ → ℝ} {u : ℝ} (hu : 0 < u) (hv : ∀ p ∈ s, u ≤ v p) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * v p)
      ≤ (Real.log b - Real.log a + mertensIntervalConst) / u := by
  classical
  have hterm : ∀ p ∈ s, Real.log p / ((p : ℝ) * v p) ≤ (Real.log p / (p : ℝ)) / u := by
    intro p hp
    have hpm := Finset.mem_sdiff.mp (hs hp)
    have hpp := (Nat.mem_primesLE.mp hpm.1).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hvp := hv p hp
    have hv0 : (0 : ℝ) < v p := lt_of_lt_of_le hu hvp
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hvp (mul_nonneg hlogp hp0.le)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsd : ∑ p ∈ s, (Real.log p / (p : ℝ)) / u
      = (∑ p ∈ s, Real.log p / (p : ℝ)) / u := by
    simp [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsd]
  gcongr
  exact sum_log_div_prime_interval_le ha hab hs

/-- **(A5).**  The same with the square of the cofactor logarithm. -/
theorem sum_log_div_prime_mul_weight_sq_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    {s : Finset ℕ} (hs : s ⊆ Nat.primesLE b \ Nat.primesLE a)
    {v : ℕ → ℝ} {u : ℝ} (hu : 0 < u) (hv : ∀ p ∈ s, u ≤ v p) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * v p ^ 2)
      ≤ (Real.log b - Real.log a + mertensIntervalConst) / u ^ 2 := by
  classical
  have hterm : ∀ p ∈ s, Real.log p / ((p : ℝ) * v p ^ 2)
      ≤ (Real.log p / (p : ℝ)) / u ^ 2 := by
    intro p hp
    have hpm := Finset.mem_sdiff.mp (hs hp)
    have hpp := (Nat.mem_primesLE.mp hpm.1).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hvp := hv p hp
    have hv0 : (0 : ℝ) < v p := lt_of_lt_of_le hu hvp
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le hvp 2)
      (mul_nonneg hlogp hp0.le)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsd : ∑ p ∈ s, (Real.log p / (p : ℝ)) / u ^ 2
      = (∑ p ∈ s, Real.log p / (p : ℝ)) / u ^ 2 := by
    simp [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsd]
  gcongr
  exact sum_log_div_prime_interval_le ha hab hs

/-- **(A6).**  Mertens' upper bound restated for the cofactor range. -/
theorem sum_log_div_prime_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ≤ Real.log n + Real.log 4 :=
  mertensFirst_upper hn

end

end RHTower.Sieve
