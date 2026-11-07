import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.CountDistanceRigidity

/-!
# A logarithmic floor for count distance

A positive integer-norm Beurling system different from rational primes has
count discrepancy at least a positive multiple of log n at arbitrarily large
natural thresholds. Geometric collision jumps and linear missing-integer
deficits give the two alternatives.
-/

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open GaloisForLFunctions.RigidArithmeticOfCuts


private theorem index_lt_power {m : ℕ} (hm : 2 ≤ m) (k : ℕ) : k + 1 ≤ m ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (show k + 1 + 1 ≤ (k + 1) * 2 by omega).trans (Nat.mul_le_mul ih hm)

private theorem log_floor_of_geometric_jumps (f : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hjump : ∀ k : ℕ, (k : ℝ) ≤ |f (m ^ k)| + |f (m ^ k - 1)|) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c * Real.log n ≤ |f n| := by
  have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  let c : ℝ := 1 / (2 * Real.log m)
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro N
  let k := N + 1
  have hg := index_lt_power hm k
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hpow : Real.log ((m ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log m := by
    rw [Nat.cast_pow, Real.log_pow]
  have hscale : c * ((k : ℝ) * Real.log m) = (k : ℝ) / 2 := by
    dsimp only [c]
    field_simp [hl.ne']
  have hj := hjump k
  by_cases hh : (k : ℝ) / 2 ≤ |f (m ^ k)|
  · refine ⟨m ^ k, by dsimp only [k] at hg ⊢; omega, ?_⟩
    rw [hpow, hscale]
    exact hh
  · refine ⟨m ^ k - 1, by dsimp only [k] at hg ⊢; omega, ?_⟩
    have hnpos : (0 : ℝ) < (m ^ k - 1 : ℕ) := by exact_mod_cast (show 0 < m ^ k - 1 by omega)
    have hlog := Real.log_le_log hnpos
      (show ((m ^ k - 1 : ℕ) : ℝ) ≤ (m ^ k : ℕ) by exact_mod_cast Nat.sub_le (m ^ k) 1)
    calc
      c * Real.log ((m ^ k - 1 : ℕ) : ℝ) ≤ c * Real.log ((m ^ k : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog hc.le
      _ = (k : ℝ) / 2 := by rw [hpow, hscale]
      _ ≤ |f (m ^ k - 1)| := by linarith only [hj, hh]

private theorem log_floor_of_linear_deficit (f : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m)
    (hdef : ∀ k : ℕ, (k : ℝ) ≤ |f (m * (4 * k + 1))|) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c * Real.log n ≤ |f n| := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let c : ℝ := 1 / (5 * m)
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro N
  let k := N + 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨m * (4 * k + 1), ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_right (4 * k + 1) hm
    dsimp only [k] at hmul ⊢
    omega
  · have hnpos : (0 : ℝ) < (m * (4 * k + 1) : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hnpos
    have hbound : Real.log ((m * (4 * k + 1) : ℕ) : ℝ) ≤ 5 * m * (k : ℝ) := by
      push_cast at hlog ⊢
      nlinarith only [hlog, mul_nonneg hmR.le (sub_nonneg.mpr hkR)]
    calc
      _ ≤ c * (5 * m * (k : ℝ)) := mul_le_mul_of_nonneg_left hbound hc.le
      _ = (k : ℝ) := by dsimp only [c]; field_simp [hmR.ne']
      _ ≤ |f (m * (4 * k + 1))| := hdef k


/-- A nonclassical positive integer-norm system has logarithmic discrepancy arbitrarily far out. -/
theorem primes_or_logarithmic_count_distance (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete) :
    (Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} //
      ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)}) ∨
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ c * Real.log n ≤ |(B.countBall n : ℝ) - n| := by
  rcases count_distance_trichotomy B h hdisc with hp | ⟨m, hm, hj⟩ | ⟨m, hm, hd⟩
  · exact Or.inl hp
  · right
    apply log_floor_of_geometric_jumps (fun n => (B.countBall n : ℝ) - n) hm
    intro k
    exact_mod_cast hj k
  · right
    apply log_floor_of_linear_deficit (fun n => (B.countBall n : ℝ) - n) (by omega : 1 ≤ m)
    intro k
    have hdef : (B.countBall (m * (4 * k + 1) : ℕ) : ℝ) + k ≤ (m * (4 * k + 1) : ℕ) := by
      exact_mod_cast hd k
    have hab := neg_le_abs ((B.countBall (m * (4 * k + 1) : ℕ) : ℝ) -
      (m * (4 * k + 1) : ℕ))
    linarith only [hdef, hab]

/-- Count error o(log n), expressed by its epsilon bound, forces the rational-prime system. -/
theorem primes_of_sublogarithmic_count_error (B : RHTower.BeurlingSystem)
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(B.countBall n : ℝ) - n| ≤ ε * Real.log n) :
    Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} //
      ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  rcases primes_or_logarithmic_count_distance B h hdisc with hp | ⟨c, hc, hlarge⟩
  · exact hp
  · obtain ⟨N, hN⟩ := hsmall (c / 2) (by positivity)
    obtain ⟨n, hn, hbig⟩ := hlarge (max N 2)
    have hs := hN n ((le_max_left N 2).trans hn)
    have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hpos := mul_pos hc hl
    nlinarith only [hs, hbig, hpos]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
