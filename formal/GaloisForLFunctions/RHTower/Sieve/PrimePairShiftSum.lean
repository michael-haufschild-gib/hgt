import GaloisForLFunctions.RHTower.Sieve.PrimePairCount

/-!
# The singular series on average over the shift

The two-dimensional sieve bound of `Sieve/PrimePairCount` carries the shift correction

```text
C(d) = ∏_{p ∣ d, P₁ < p ≤ h} (p − 1)/p ,
```

whose reciprocal is the singular series of the shift `d`.  Averaged over `d ≤ K` the reciprocal is
bounded by an absolute constant: expanding the product over subsets, counting the multiples of each
subset product, and reassembling gives

```text
∑_{d ≤ K} 1/C(d) ≤ K ∏_{p} (1 + 1/(p(p−1))) ≤ e·K ,
```

because `∑_{n ≥ 2} 1/(n(n−1)) = 1` telescopes.  No prime-counting input is used.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The telescoping sum `∑_{2 ≤ n ≤ h} 1/(n(n−1)) = 1 − 1/h`. -/
private theorem sum_inv_mul_pred_eq {h : ℕ} (hh : 1 ≤ h) :
    ∑ n ∈ Finset.Icc 2 h, 1 / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (h : ℝ) := by
  induction h with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hh with h1 | h1
    · simp [← h1]
    · have hm : 1 ≤ m := by omega
      rw [Finset.sum_Icc_succ_top (by omega), ih hm]
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hne : (m : ℝ) ≠ 0 := ne_of_gt hm0
      have hne1 : (m : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      rw [show ((m : ℝ) + 1) - 1 = (m : ℝ) by ring]
      rw [eq_sub_iff_add_eq, sub_add_eq_add_sub]
      field_simp
      ring

/-- `∑_{2 ≤ n ≤ h} 1/(n(n−1)) ≤ 1`. -/
theorem sum_inv_mul_pred_le (h : ℕ) :
    ∑ n ∈ Finset.Icc 2 h, 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · rw [sum_inv_mul_pred_eq hh]
    have : (0 : ℝ) ≤ 1 / (h : ℝ) := by positivity
    linarith

/-- The sifting primes satisfy `∑ 1/(p(p−1)) ≤ 1`. -/
theorem sum_rangePrimes_inv_mul_pred_le (P₁ h : ℕ) :
    ∑ p ∈ rangePrimes P₁ h, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (sum_inv_mul_pred_le h)
  · intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    have h2 : 2 ≤ p := hp.2.two_le
    exact ⟨h2, hp.1.2⟩
  · intro n hn _
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n <;> norm_num
    · have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
      have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      positivity

/-- For a set of primes, the product divides `d` exactly when every member does. -/
theorem prod_dvd_iff_forall_dvd {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (d : ℕ) :
    (∏ p ∈ T, p) ∣ d ↔ ∀ p ∈ T, p ∣ d := by
  constructor
  · intro hdvd p hp
    exact dvd_trans (Finset.dvd_prod_of_mem _ hp) hdvd
  · intro hall
    exact Finset.prod_primes_dvd d (fun p hp => (hT p hp).prime) hall

/-- **The reciprocal shift correction, expanded over subsets.** -/
theorem prod_shiftCorrection_inv_eq {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) :
    (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      = ∑ T ∈ (rangePrimes P₁ h).powerset,
          (if (∏ p ∈ T, p) ∣ d then ∏ p ∈ T, 1 / ((p : ℝ) - 1) else 0) := by
  classical
  set P : Finset ℕ := rangePrimes P₁ h with hPdef
  have hp3 : ∀ p ∈ P, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [hPdef, rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hstep : ∀ p ∈ P.filter (fun p => p ∣ d),
      ((p : ℝ) / ((p : ℝ) - 1)) = 1 / ((p : ℝ) - 1) + 1 := by
    intro p hp
    have h3 := hp3 p (Finset.mem_filter.1 hp).1
    have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl hstep]
  have hexp := Finset.prod_add (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ => (1 : ℝ))
    (P.filter (fun p => p ∣ d))
  simp only [Finset.prod_const_one, mul_one] at hexp
  rw [hexp, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext T
  simp only [Finset.mem_powerset, Finset.mem_filter]
  constructor
  · intro hT
    have hsub : T ⊆ P := hT.trans (Finset.filter_subset _ _)
    have hprimes : ∀ p ∈ T, p.Prime := fun p hp =>
      rangePrimes_prime (by rw [← hPdef]; exact hsub hp)
    refine ⟨hsub, (prod_dvd_iff_forall_dvd hprimes d).2 fun p hp => ?_⟩
    exact (Finset.mem_filter.1 (hT hp)).2
  · intro hT
    have hprimes : ∀ p ∈ T, p.Prime := fun p hp => rangePrimes_prime (by
      rw [← hPdef]; exact hT.1 hp)
    intro p hp
    exact Finset.mem_filter.2 ⟨hT.1 hp, (prod_dvd_iff_forall_dvd hprimes d).1 hT.2 p hp⟩

/-- **The singular series is bounded on average over the shift.** -/
theorem sum_inv_shiftCorrection_le {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h K : ℕ) :
    ∑ d ∈ Finset.Icc 1 K,
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ Real.exp 1 * (K : ℝ) := by
  classical
  set P : Finset ℕ := rangePrimes P₁ h with hPdef
  have hp3 : ∀ p ∈ P, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [hPdef, rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hTpos : ∀ T ∈ P.powerset, (0 : ℝ) < ((∏ p ∈ T, p : ℕ) : ℝ) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have : 0 < ∏ p ∈ T, p := by
      refine Finset.prod_pos fun p hp => ?_
      have := hp3 p (hT hp)
      exact_mod_cast (by linarith : (0:ℝ) < (p:ℝ))
    exact_mod_cast this
  have hFnn : ∀ T ∈ P.powerset, (0 : ℝ) ≤ ∏ p ∈ T, 1 / ((p : ℝ) - 1) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine Finset.prod_nonneg fun p hp => ?_
    have h3p := hp3 p (hT hp)
    have h1p : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  -- expand and exchange the two sums
  have h1 : ∑ d ∈ Finset.Icc 1 K,
        (∏ p ∈ P.filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      = ∑ T ∈ P.powerset, ∑ d ∈ Finset.Icc 1 K,
          (if (∏ p ∈ T, p) ∣ d then ∏ p ∈ T, 1 / ((p : ℝ) - 1) else 0) := by
    rw [← Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => prod_shiftCorrection_inv_eq hP₁ h d
  -- the inner sum counts multiples
  have h2 : ∀ T ∈ P.powerset,
      (∑ d ∈ Finset.Icc 1 K,
          (if (∏ p ∈ T, p) ∣ d then ∏ p ∈ T, 1 / ((p : ℝ) - 1) else 0))
        = (∏ p ∈ T, 1 / ((p : ℝ) - 1)) * (((K / (∏ p ∈ T, p) : ℕ) : ℝ)) := by
    intro T hT
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    exact Nat.Ioc_filter_dvd_card_eq_div K (∏ p ∈ T, p)
  rw [h1, Finset.sum_congr rfl h2]
  -- replace the integer quotient by the real one
  have h3 : ∑ T ∈ P.powerset,
        (∏ p ∈ T, 1 / ((p : ℝ) - 1)) * (((K / (∏ p ∈ T, p) : ℕ) : ℝ))
      ≤ ∑ T ∈ P.powerset,
        (∏ p ∈ T, 1 / ((p : ℝ) - 1)) * ((K : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun T hT => ?_
    exact mul_le_mul_of_nonneg_left (Nat.cast_div_le) (hFnn T hT)
  refine le_trans h3 ?_
  -- rewrite each term as `K` times a product
  have h4 : ∀ T ∈ P.powerset,
      (∏ p ∈ T, 1 / ((p : ℝ) - 1)) * ((K : ℝ) / ((∏ p ∈ T, p : ℕ) : ℝ))
        = (K : ℝ) * ∏ p ∈ T, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hcast : ((∏ p ∈ T, p : ℕ) : ℝ) = ∏ p ∈ T, (p : ℝ) := by push_cast; ring
    have hsplit : ∏ p ∈ T, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        = (∏ p ∈ T, 1 / (p : ℝ)) * ∏ p ∈ T, 1 / ((p : ℝ) - 1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have h3p := hp3 p (hT hp)
      have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
      have hne' : ((p : ℝ)) ≠ 0 := by linarith
      field_simp
    have hinv : (∏ p ∈ T, 1 / (p : ℝ)) = 1 / ∏ p ∈ T, (p : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    rw [hsplit, hinv, hcast]
    field_simp
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum]
  -- the sum over subsets is the Euler product
  have h5 : ∑ T ∈ P.powerset, ∏ p ∈ T, 1 / ((p : ℝ) * ((p : ℝ) - 1))
      = ∏ p ∈ P, (1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1) := by
    have := Finset.prod_add (fun p : ℕ => 1 / ((p : ℝ) * ((p : ℝ) - 1)))
      (fun _ => (1 : ℝ)) P
    simp only [Finset.prod_const_one, mul_one] at this
    rw [this]
  rw [h5]
  -- the Euler product is at most `e`
  have h6 : ∏ p ∈ P, (1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1)
      ≤ Real.exp (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h3p := hp3 p hp
      have : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have h1p : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      linarith
    · exact Real.add_one_le_exp _
  have h7 : Real.exp (∑ p ∈ P, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.exp 1 :=
    Real.exp_le_exp.2 (by rw [hPdef]; exact sum_rangePrimes_inv_mul_pred_le P₁ h)
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  calc (K : ℝ) * ∏ p ∈ P, (1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1)
      ≤ (K : ℝ) * Real.exp 1 := by
        exact mul_le_mul_of_nonneg_left (le_trans h6 h7) hK
    _ = Real.exp 1 * (K : ℝ) := by ring

end

end RHTower.Sieve
