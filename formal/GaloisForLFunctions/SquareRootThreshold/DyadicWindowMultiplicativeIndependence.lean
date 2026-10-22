import GaloisForLFunctions.SquareRootThreshold.LargeDyadicPrimeWindowsDecideTheCriticalLine

/-!
# Multiplicative independence inside a dyadic prime window, and the critical ratio `4`

A lag `v` of the two-bump family reads the prime powers of one window `|log n − v| ≤ 2w`, of
ratio `e^{4w} < 4`. This module determines the multiplicative relations available inside such a
window.

* **Rigidity** (`window_relation_eq_zero_of_log`). In a window `Y ≤ n < 4Y` of prime powers every
  integer relation `∑ c_n log n = 0` with `(∑ |c_n|) log 3 ≤ 2 log Y` is trivial. The proof runs
  valuation by valuation: two powers of one prime `p` fit in a window of ratio `< 4` only when
  `p < 4` and the exponents are consecutive, and then `c_k k + c_{k+1}(k+1) = 0` with
  `gcd(k, k+1) = 1` forces `|c_k| ≥ k + 1` and `|c_{k+1}| ≥ k`, an `ℓ¹` cost of `2k + 1`, while
  `p^k ≥ Y` and `p ≤ 3` give `k log 3 ≥ log Y`.
* **Diagonal multiplicative energy** (`mult_eq_of_prod_pow_eq`). Two multiplicities on a dyadic
  window with the same product and total size below the same threshold are equal: every
  multiplicative energy of order below `≍ log Y` is exactly diagonal.
* **Sharpness** (`exists_window_relation_of_two_powers`). At `Y = 2^k` the window holds `2^k` and
  `2^{k+1}`, with the relation `(k+1) log 2^k = k log 2^{k+1}` of `ℓ¹` norm `2k + 1`: the
  threshold has the exact order `log Y`, and `log 3` can be improved at best to `log 2`.
* **The critical ratio is `4`** (`exists_closed_window_relation_of_three_powers`). One step wider,
  on the closed window `Y ≤ n ≤ 4Y`, three powers of `2` fit and carry
  `2^k · 2^{k+2} = (2^{k+1})²`, of `ℓ¹` norm `4` uniformly in `Y`. The minimal relation order
  drops from `≍ log Y` to `4` exactly at window ratio `4`.
* **For the lag family** (`lagPrimeWindow_relation_eq_zero`): at lag `v` and width `2w < log 2`
  the window read by the test carries no nontrivial relation of `ℓ¹` norm at most
  `2(v − 2w)/log 3`; the admissible relation order grows linearly in the lag.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

/-! ### The two-exponent relation -/

/-- A relation `c₁ k + c₂ (k+1) = 0` with `k ≥ 1` and a nonzero coefficient costs `2k + 1` in
`ℓ¹`: coprimality of `k` and `k + 1` forces `(k+1) ∣ c₁` and `k ∣ c₂`. -/
private theorem two_exponent_bounds {k : ℕ} (hk : 1 ≤ k) {c₁ c₂ : ℤ}
    (h : c₁ * (k : ℤ) + c₂ * ((k : ℤ) + 1) = 0) (hne : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    (k : ℤ) + 1 ≤ |c₁| ∧ (k : ℤ) ≤ |c₂| := by
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hk1 : ((k : ℤ) + 1) ≠ 0 := by positivity
  have hc1 : c₁ ≠ 0 := by
    rcases hne with h1 | h2
    · exact h1
    · intro h1
      rw [h1, zero_mul, zero_add] at h
      exact h2 ((mul_eq_zero.mp h).resolve_right hk1)
  have hc2 : c₂ ≠ 0 := by
    intro h2
    rw [h2, zero_mul, add_zero] at h
    exact hc1 ((mul_eq_zero.mp h).resolve_right hk0.ne')
  have hcop1 : IsCoprime ((k : ℤ) + 1) (k : ℤ) := ⟨1, -1, by ring⟩
  have hcop2 : IsCoprime (k : ℤ) ((k : ℤ) + 1) := ⟨-1, 1, by ring⟩
  have hd1 : ((k : ℤ) + 1) ∣ c₁ :=
    hcop1.dvd_of_dvd_mul_left ⟨-c₂, by linarith [h]⟩
  have hd2 : (k : ℤ) ∣ c₂ :=
    hcop2.dvd_of_dvd_mul_left ⟨-c₁, by linarith [h]⟩
  exact ⟨Int.le_of_dvd (abs_pos.mpr hc1) ((dvd_abs _ _).mpr hd1),
    Int.le_of_dvd (abs_pos.mpr hc2) ((dvd_abs _ _).mpr hd2)⟩

/-! ### The window and its `p`-part -/

/-- A prime power in the window `Y ≤ n < 4Y`. -/
def InDyadicWindow (Y : ℝ) (n : ℕ) : Prop :=
  IsPrimePow n ∧ Y ≤ (n : ℝ) ∧ (n : ℝ) < 4 * Y

private theorem two_le_of_isPrimePow {n : ℕ} (h : IsPrimePow n) : 2 ≤ n := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp h
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    _ = n := hpk

/-- A window element divisible by a prime `p` is a positive power of `p`. -/
private theorem exists_pow_of_dvd {n p : ℕ} (hn : IsPrimePow n) (hp : p.Prime) (hpn : p ∣ n) :
    ∃ m : ℕ, 1 ≤ m ∧ n = p ^ m := by
  obtain ⟨q, m, hq, hm, hqm⟩ := (isPrimePow_nat_iff n).mp hn
  refine ⟨m, hm, ?_⟩
  have hpq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow (hqm ▸ hpn))
  rw [hpq, hqm]

/-- Two powers of one prime inside a window of ratio `4` force `p < 4` and consecutive
exponents. -/
private theorem pow_succ_of_two_in_window {Y : ℝ} {p a b : ℕ} (hp : p.Prime)
    (ha : InDyadicWindow Y (p ^ a)) (hb : InDyadicWindow Y (p ^ b)) (hab : a < b) :
    b = a + 1 ∧ p < 4 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) ^ a := by positivity
  have hlt : ((p : ℝ) ^ b) < 4 * ((p : ℝ) ^ a) := by
    have h1 : ((p ^ b : ℕ) : ℝ) < 4 * Y := hb.2.2
    have h2 : Y ≤ ((p ^ a : ℕ) : ℝ) := ha.2.1
    push_cast at h1 h2
    linarith
  have hpow : (p : ℝ) ^ b = (p : ℝ) ^ a * (p : ℝ) ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  have hratio : ((p : ℝ) ^ (b - a)) < 4 := by
    rw [hpow] at hlt
    nlinarith
  have hd : b - a = 1 := by
    by_contra hne
    have h2 : 2 ≤ b - a := by omega
    have hge : (4 : ℝ) ≤ (p : ℝ) ^ (b - a) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (p : ℝ) ^ 2 := by nlinarith
        _ ≤ (p : ℝ) ^ (b - a) := pow_le_pow_right₀ (by linarith) h2
    linarith
  refine ⟨by omega, ?_⟩
  rw [hd, pow_one] at hratio
  exact_mod_cast hratio

/-! ### The rigidity theorem -/

/-- **Dyadic window rigidity, valuation form.** An integer relation holding at every prime
valuation on a window of prime powers of ratio `4` is trivial once its `ℓ¹` norm is at most
`2 log Y / log 3`. -/
theorem window_relation_eq_zero_of_valuation {Y : ℝ} (hY : 0 < Y) {s : Finset ℕ}
    (hs : ∀ n ∈ s, InDyadicWindow Y n) {c : ℕ → ℤ}
    (hval : ∀ p : ℕ, p.Prime → ∑ n ∈ s, c n * (n.factorization p : ℤ) = 0)
    (hsmall : ((∑ n ∈ s, |c n| : ℤ) : ℝ) * Real.log 3 ≤ 2 * Real.log Y) :
    ∀ n ∈ s, c n = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨n₀, hn₀s, hn₀⟩ := hcon
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n₀).mp (hs n₀ hn₀s).1
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set S := s.filter (fun n => p ∣ n) with hSdef
  have hSs : S ⊆ s := filter_subset _ _
  have hn₀S : n₀ ∈ S := by
    refine mem_filter.mpr ⟨hn₀s, ?_⟩
    rw [← hpk]
    exact dvd_pow_self p (by omega)
  -- off the `p`-part the valuation vanishes, so the relation is carried by `S`
  have hsum : ∑ n ∈ S, c n * (n.factorization p : ℤ) = 0 := by
    rw [sum_subset hSs]
    · exact hval p hp
    · intro n hn hnS
      have hnd : ¬ p ∣ n := fun hdvd => hnS (mem_filter.mpr ⟨hn, hdvd⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
  obtain ⟨x, hxS, hxmin⟩ : ∃ x ∈ S, ∀ n ∈ S, x ≤ n :=
    ⟨S.min' ⟨n₀, hn₀S⟩, S.min'_mem _, fun n hn => S.min'_le n hn⟩
  have hxs : x ∈ s := hSs hxS
  obtain ⟨a, ha1, hxa⟩ := exists_pow_of_dvd (hs x hxs).1 hp (mem_filter.mp hxS).2
  have hxw : InDyadicWindow Y (p ^ a) := hxa ▸ hs x hxs
  have hex : (x.factorization p : ℤ) = (a : ℤ) := by
    rw [hxa, hp.factorization_pow, Finsupp.single_eq_same]
  -- every member of the `p`-part is `x = p ^ a` or `p ^ (a + 1)`
  have hsub : S ⊆ {x, p ^ (a + 1)} := by
    intro n hn
    obtain ⟨m, hm1, hnm⟩ := exists_pow_of_dvd (hs n (hSs hn)).1 hp (mem_filter.mp hn).2
    have hnw : InDyadicWindow Y (p ^ m) := hnm ▸ hs n (hSs hn)
    rcases lt_trichotomy a m with hlt | heq | hgt
    · exact mem_insert_of_mem (mem_singleton.mpr
        (by rw [hnm, (pow_succ_of_two_in_window hp hxw hnw hlt).1]))
    · exact mem_insert.mpr (Or.inl (by rw [hnm, ← heq, hxa]))
    · exact absurd (hxmin n hn) (by
        rw [hxa, hnm]
        exact not_le.mpr (Nat.pow_lt_pow_right hp.one_lt hgt))
  by_cases hy : p ^ (a + 1) ∈ S
  · -- two consecutive powers of `p`: the relation costs `2a + 1` in `ℓ¹`
    have hxy : x ≠ p ^ (a + 1) := by
      rw [hxa]
      exact fun h => absurd ((Nat.pow_right_injective hp.two_le) h) (by omega)
    have hSeq : S = {x, p ^ (a + 1)} :=
      Subset.antisymm hsub (by
        intro n hn
        rcases mem_insert.mp hn with h | h
        · exact h ▸ hxS
        · exact (mem_singleton.mp h) ▸ hy)
    have hey : (((p ^ (a + 1)).factorization p : ℕ) : ℤ) = (a : ℤ) + 1 := by
      rw [hp.factorization_pow, Finsupp.single_eq_same]
      push_cast
      ring
    rw [hSeq, sum_pair hxy, hex, hey] at hsum
    have hne : c x ≠ 0 ∨ c (p ^ (a + 1)) ≠ 0 := by
      rcases mem_insert.mp (hSeq ▸ hn₀S) with h | h
      · exact Or.inl (h ▸ hn₀)
      · exact Or.inr ((mem_singleton.mp h) ▸ hn₀)
    obtain ⟨hb1, hb2⟩ := two_exponent_bounds ha1 hsum hne
    have hpairsub : ({x, p ^ (a + 1)} : Finset ℕ) ⊆ s := hSeq ▸ hSs
    have hpairsum : ∑ n ∈ ({x, p ^ (a + 1)} : Finset ℕ), |c n| = |c x| + |c (p ^ (a + 1))| :=
      sum_pair hxy
    have hpair : |c x| + |c (p ^ (a + 1))| ≤ ∑ n ∈ s, |c n| := by
      rw [← hpairsum]
      exact sum_le_sum_of_subset_of_nonneg hpairsub fun n _ _ => abs_nonneg _
    have hL1 : 2 * (a : ℝ) + 1 ≤ ((∑ n ∈ s, |c n| : ℤ) : ℝ) := by
      have hz : (2 * (a : ℤ) + 1) ≤ ∑ n ∈ s, |c n| := by linarith
      have hz' := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at hz'
      linarith
    -- the window places `p ^ a` above `Y`, and the prime is at most `3`
    have hp3 : p < 4 := (pow_succ_of_two_in_window hp hxw
      (show InDyadicWindow Y (p ^ (a + 1)) from hs _ (hSs hy)) (by omega)).2
    have hYle : Real.log Y ≤ (a : ℝ) * Real.log 3 := by
      have h1 : Y ≤ (3 : ℝ) ^ a := by
        refine le_trans hxw.2.1 ?_
        push_cast
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.lt_succ_iff.mp hp3) a
      calc Real.log Y ≤ Real.log ((3 : ℝ) ^ a) := Real.log_le_log hY h1
        _ = (a : ℝ) * Real.log 3 := by rw [Real.log_pow]
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith [hsmall, hL1, hYle, hl3]
  · -- a single power of `p`: the relation reads `a · c x = 0`
    have hSeq : S = {x} :=
      Subset.antisymm (by
        intro n hn
        rcases mem_insert.mp (hsub hn) with h | h
        · exact mem_singleton.mpr h
        · exact absurd ((mem_singleton.mp h) ▸ hn) hy)
        (by intro n hn; exact (mem_singleton.mp hn) ▸ hxS)
    rw [hSeq, sum_singleton, hex] at hsum
    have ha0 : (a : ℤ) ≠ 0 := by
      have hpos : 0 < a := ha1
      exact_mod_cast hpos.ne'
    have hcx : c x = 0 := (mul_eq_zero.mp hsum).resolve_right ha0
    exact hn₀ ((mem_singleton.mp (hSeq ▸ hn₀S)) ▸ hcx)

/-! ### From products and from frequencies to valuations -/

/-- Equal products of window powers give the valuation relation of the difference. -/
private theorem valuation_relation_of_prod_pow_eq {s : Finset ℕ} (hs0 : ∀ n ∈ s, n ≠ 0)
    {α β : ℕ → ℕ} (hprod : ∏ n ∈ s, n ^ α n = ∏ n ∈ s, n ^ β n) (p : ℕ) :
    ∑ n ∈ s, ((α n : ℤ) - (β n : ℤ)) * (n.factorization p : ℤ) = 0 := by
  have hA : ∀ n ∈ s, n ^ α n ≠ 0 := fun n hn => pow_ne_zero _ (hs0 n hn)
  have hB : ∀ n ∈ s, n ^ β n ≠ 0 := fun n hn => pow_ne_zero _ (hs0 n hn)
  have hnat : ∑ n ∈ s, α n * n.factorization p = ∑ n ∈ s, β n * n.factorization p := by
    have hpp : (∏ n ∈ s, n ^ α n).factorization p = (∏ n ∈ s, n ^ β n).factorization p := by
      rw [hprod]
    rw [Nat.factorization_prod hA, Nat.factorization_prod hB,
      Finset.sum_apply', Finset.sum_apply'] at hpp
    simpa only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] using hpp
  have hint : ∑ n ∈ s, (α n : ℤ) * (n.factorization p : ℤ) =
      ∑ n ∈ s, (β n : ℤ) * (n.factorization p : ℤ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hnat
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, hint, sub_self]

/-- A vanishing real relation among the logarithms of positive integers is an equality of the
two one-sided products. -/
private theorem prod_pow_eq_of_log_relation {s : Finset ℕ} (hs1 : ∀ n ∈ s, 1 ≤ n) {c : ℕ → ℤ}
    (hrel : ∑ n ∈ s, (c n : ℝ) * Real.log n = 0) :
    ∏ n ∈ s, n ^ (c n).toNat = ∏ n ∈ s, n ^ (-c n).toNat := by
  have hne : ∀ n ∈ s, ((n : ℝ)) ≠ 0 := fun n hn => by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs1 n hn
    linarith
  have hcastA : ((∏ n ∈ s, n ^ (c n).toNat : ℕ) : ℝ) = ∏ n ∈ s, ((n : ℝ) ^ (c n).toNat) := by
    push_cast
    ring
  have hcastB : ((∏ n ∈ s, n ^ (-c n).toNat : ℕ) : ℝ) = ∏ n ∈ s, ((n : ℝ) ^ (-c n).toNat) := by
    push_cast
    ring
  have hlogA : Real.log ((∏ n ∈ s, n ^ (c n).toNat : ℕ) : ℝ) =
      ∑ n ∈ s, ((c n).toNat : ℝ) * Real.log n := by
    rw [hcastA, Real.log_prod (fun n hn => pow_ne_zero _ (hne n hn))]
    exact sum_congr rfl fun n _ => Real.log_pow _ _
  have hlogB : Real.log ((∏ n ∈ s, n ^ (-c n).toNat : ℕ) : ℝ) =
      ∑ n ∈ s, (((-c n).toNat : ℕ) : ℝ) * Real.log n := by
    rw [hcastB, Real.log_prod (fun n hn => pow_ne_zero _ (hne n hn))]
    exact sum_congr rfl fun n _ => Real.log_pow _ _
  have hkey : ∀ m : ℤ, ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = (m : ℝ) := by
    intro m
    have h : ((m.toNat : ℕ) : ℤ) - (((-m).toNat : ℕ) : ℤ) = m := by omega
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have hlogeq : Real.log ((∏ n ∈ s, n ^ (c n).toNat : ℕ) : ℝ) =
      Real.log ((∏ n ∈ s, n ^ (-c n).toNat : ℕ) : ℝ) := by
    rw [hlogA, hlogB, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    calc ∑ n ∈ s, (((c n).toNat : ℝ) * Real.log n - (((-c n).toNat : ℕ) : ℝ) * Real.log n)
        = ∑ n ∈ s, (c n : ℝ) * Real.log n := by
          refine sum_congr rfl fun n _ => ?_
          rw [← sub_mul, hkey (c n)]
      _ = 0 := hrel
  have hposA : (0 : ℝ) < ((∏ n ∈ s, n ^ (c n).toNat : ℕ) : ℝ) := by
    have hp : 0 < ∏ n ∈ s, n ^ (c n).toNat := prod_pos fun n hn => pow_pos (hs1 n hn) _
    exact_mod_cast hp
  have hposB : (0 : ℝ) < ((∏ n ∈ s, n ^ (-c n).toNat : ℕ) : ℝ) := by
    have hp : 0 < ∏ n ∈ s, n ^ (-c n).toNat := prod_pos fun n hn => pow_pos (hs1 n hn) _
    exact_mod_cast hp
  have hreal : ((∏ n ∈ s, n ^ (c n).toNat : ℕ) : ℝ) = ((∏ n ∈ s, n ^ (-c n).toNat : ℕ) : ℝ) := by
    rw [← Real.exp_log hposA, ← Real.exp_log hposB, hlogeq]
  exact_mod_cast hreal

/-! ### The two usable forms -/

/-- **Dyadic window rigidity, frequency form.** On a window `Y ≤ n < 4Y` of prime powers every
integer relation among the frequencies `log n` of `ℓ¹` norm at most `2 log Y / log 3` is
trivial. -/
theorem window_relation_eq_zero_of_log {Y : ℝ} (hY : 0 < Y) {s : Finset ℕ}
    (hs : ∀ n ∈ s, InDyadicWindow Y n) {c : ℕ → ℤ}
    (hrel : ∑ n ∈ s, (c n : ℝ) * Real.log n = 0)
    (hsmall : ((∑ n ∈ s, |c n| : ℤ) : ℝ) * Real.log 3 ≤ 2 * Real.log Y) :
    ∀ n ∈ s, c n = 0 := by
  have hs1 : ∀ n ∈ s, 1 ≤ n := fun n hn => by
    have h2 := two_le_of_isPrimePow (hs n hn).1
    omega
  have hs0 : ∀ n ∈ s, n ≠ 0 := fun n hn => by
    have h1 := hs1 n hn
    omega
  have hprod := prod_pow_eq_of_log_relation hs1 hrel
  refine window_relation_eq_zero_of_valuation hY hs (fun p _ => ?_) hsmall
  have hval := valuation_relation_of_prod_pow_eq hs0 hprod p
  have hterm : ∀ n ∈ s, c n * (n.factorization p : ℤ) =
      ((((c n).toNat : ℕ) : ℤ) - ((((-c n)).toNat : ℕ) : ℤ)) * (n.factorization p : ℤ) := by
    intro n _
    congr 1
    omega
  rw [sum_congr rfl hterm]
  exact hval

/-- **Diagonal multiplicative energy of a dyadic window.** Two multiplicities on a window of
prime powers of ratio `4` with the same product and total size at most `2 log Y / log 3` agree. -/
theorem mult_eq_of_prod_pow_eq {Y : ℝ} (hY : 0 < Y) {s : Finset ℕ}
    (hs : ∀ n ∈ s, InDyadicWindow Y n) {α β : ℕ → ℕ}
    (hprod : ∏ n ∈ s, n ^ α n = ∏ n ∈ s, n ^ β n)
    (hcard : ((∑ n ∈ s, (α n + β n) : ℕ) : ℝ) * Real.log 3 ≤ 2 * Real.log Y) :
    ∀ n ∈ s, α n = β n := by
  have hs0 : ∀ n ∈ s, n ≠ 0 := fun n hn => by
    have h2 := two_le_of_isPrimePow (hs n hn).1
    omega
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbound : ((∑ n ∈ s, |(α n : ℤ) - (β n : ℤ)| : ℤ) : ℝ) ≤
      ((∑ n ∈ s, (α n + β n) : ℕ) : ℝ) := by
    have h : (∑ n ∈ s, |(α n : ℤ) - (β n : ℤ)|) ≤ (∑ n ∈ s, ((α n : ℤ) + (β n : ℤ))) :=
      sum_le_sum fun n _ => by
        rw [abs_le]
        omega
    calc ((∑ n ∈ s, |(α n : ℤ) - (β n : ℤ)| : ℤ) : ℝ)
        ≤ ((∑ n ∈ s, ((α n : ℤ) + (β n : ℤ)) : ℤ) : ℝ) := by exact_mod_cast h
      _ = ((∑ n ∈ s, (α n + β n) : ℕ) : ℝ) := by push_cast; ring
  have hsmall : ((∑ n ∈ s, |(α n : ℤ) - (β n : ℤ)| : ℤ) : ℝ) * Real.log 3 ≤ 2 * Real.log Y :=
    le_trans (mul_le_mul_of_nonneg_right hbound hl3.le) hcard
  have hzero := window_relation_eq_zero_of_valuation hY hs
    (c := fun n => (α n : ℤ) - (β n : ℤ))
    (fun p _ => valuation_relation_of_prod_pow_eq hs0 hprod p) hsmall
  intro n hn
  have hz := hzero n hn
  omega

/-! ### Sharpness and the critical ratio -/

private theorem isPrimePow_two_pow {k : ℕ} (hk : 1 ≤ k) : IsPrimePow (2 ^ k : ℕ) :=
  (isPrimePow_nat_iff _).mpr ⟨2, k, Nat.prime_two, hk, rfl⟩

private theorem two_pow_ne {i j : ℕ} (h : i ≠ j) : (2 ^ i : ℕ) ≠ (2 ^ j : ℕ) :=
  fun he => h ((Nat.pow_right_injective (le_refl 2)) he)

/-- Coefficients of the minimal two-power relation `(k+1) log 2^k = k log 2^{k+1}`. -/
private def twoPowCoeff (k : ℕ) : ℕ → ℤ :=
  fun n => if n = 2 ^ k then (k : ℤ) + 1 else if n = 2 ^ (k + 1) then -(k : ℤ) else 0

private theorem twoPowCoeff_lo (k : ℕ) : twoPowCoeff k (2 ^ k) = (k : ℤ) + 1 := by
  unfold twoPowCoeff
  rw [if_pos rfl]

private theorem twoPowCoeff_hi (k : ℕ) : twoPowCoeff k (2 ^ (k + 1)) = -(k : ℤ) := by
  unfold twoPowCoeff
  rw [if_neg (two_pow_ne (by omega)), if_pos rfl]

/-- Coefficients of the three-power relation `2^k · 2^{k+2} = (2^{k+1})²`. -/
private def threePowCoeff (k : ℕ) : ℕ → ℤ :=
  fun n => if n = 2 ^ k then 1 else if n = 2 ^ (k + 1) then -2 else
    if n = 2 ^ (k + 2) then 1 else 0

private theorem threePowCoeff_0 (k : ℕ) : threePowCoeff k (2 ^ k) = 1 := by
  unfold threePowCoeff
  rw [if_pos rfl]

private theorem threePowCoeff_1 (k : ℕ) : threePowCoeff k (2 ^ (k + 1)) = -2 := by
  unfold threePowCoeff
  rw [if_neg (two_pow_ne (by omega)), if_pos rfl]

private theorem threePowCoeff_2 (k : ℕ) : threePowCoeff k (2 ^ (k + 2)) = 1 := by
  unfold threePowCoeff
  rw [if_neg (two_pow_ne (by omega)), if_neg (two_pow_ne (by omega)), if_pos rfl]

/-- **The threshold has the exact order `log Y`.** At `Y = 2^k` the window `Y ≤ n < 4Y` holds
`2^k` and `2^{k+1}`, carrying the relation `(k+1) log 2^k − k log 2^{k+1} = 0` of `ℓ¹` norm
`2k + 1`, while `log Y = k log 2`. -/
theorem exists_window_relation_of_two_powers {k : ℕ} (hk : 1 ≤ k) :
    ∃ (Y : ℝ) (s : Finset ℕ) (c : ℕ → ℤ), 0 < Y ∧ Real.log Y = (k : ℝ) * Real.log 2 ∧
      (∀ n ∈ s, InDyadicWindow Y n) ∧ (∑ n ∈ s, (c n : ℝ) * Real.log n = 0) ∧
      (∑ n ∈ s, |c n| : ℤ) = 2 * (k : ℤ) + 1 ∧ ∃ n ∈ s, c n ≠ 0 := by
  classical
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hne : (2 ^ k : ℕ) ≠ (2 ^ (k + 1) : ℕ) := two_pow_ne (by omega)
  have hA : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  have hB : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ k := by push_cast; ring
  refine ⟨(2 : ℝ) ^ k, {2 ^ k, 2 ^ (k + 1)}, twoPowCoeff k, hpk, by rw [Real.log_pow], ?_, ?_,
    ?_, ?_⟩
  · intro n hn
    rcases mem_insert.mp hn with h | h
    · rw [h]
      exact ⟨isPrimePow_two_pow hk, by rw [hA], by rw [hA]; linarith⟩
    · rw [mem_singleton.mp h]
      exact ⟨isPrimePow_two_pow (by omega), by rw [hB]; linarith, by rw [hB]; linarith⟩
  · rw [sum_pair hne, twoPowCoeff_lo, twoPowCoeff_hi, hA, hB,
      show (2 : ℝ) * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) by ring, Real.log_pow, Real.log_pow]
    push_cast
    ring
  · rw [sum_pair hne, twoPowCoeff_lo, twoPowCoeff_hi,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ (k : ℤ) + 1), abs_neg,
      abs_of_nonneg (Int.natCast_nonneg k)]
    ring
  · exact ⟨2 ^ k, mem_insert_self _ _, by rw [twoPowCoeff_lo]; positivity⟩

/-- **The critical window ratio is `4`.** On the closed window `Y ≤ n ≤ 4Y` with `Y = 2^k` the
three powers `2^k, 2^{k+1}, 2^{k+2}` all fit and carry `2^k · 2^{k+2} = (2^{k+1})²`, a relation of
`ℓ¹` norm `4` for every `k`: one step beyond ratio `4` the minimal relation order collapses from
`≍ log Y` to a constant. -/
theorem exists_closed_window_relation_of_three_powers {k : ℕ} (hk : 1 ≤ k) :
    ∃ (Y : ℝ) (s : Finset ℕ) (c : ℕ → ℤ), 0 < Y ∧
      (∀ n ∈ s, IsPrimePow n ∧ Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * Y) ∧
      (∑ n ∈ s, (c n : ℝ) * Real.log n = 0) ∧ (∑ n ∈ s, |c n| : ℤ) = 4 ∧
      ∃ n ∈ s, c n ≠ 0 := by
  classical
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h01 : (2 ^ k : ℕ) ≠ (2 ^ (k + 1) : ℕ) := two_pow_ne (by omega)
  have h02 : (2 ^ k : ℕ) ≠ (2 ^ (k + 2) : ℕ) := two_pow_ne (by omega)
  have h12 : (2 ^ (k + 1) : ℕ) ≠ (2 ^ (k + 2) : ℕ) := two_pow_ne (by omega)
  have hA : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  have hB : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ k := by push_cast; ring
  have hC : ((2 ^ (k + 2) : ℕ) : ℝ) = 4 * (2 : ℝ) ^ k := by push_cast; ring
  have hnotmem : (2 ^ k : ℕ) ∉ ({2 ^ (k + 1), 2 ^ (k + 2)} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]
    exact fun h => h.elim h01 h02
  refine ⟨(2 : ℝ) ^ k, {2 ^ k, 2 ^ (k + 1), 2 ^ (k + 2)}, threePowCoeff k, hpk, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases mem_insert.mp hn with h | h
    · rw [h]
      exact ⟨isPrimePow_two_pow hk, by rw [hA], by rw [hA]; linarith⟩
    rcases mem_insert.mp h with h | h
    · rw [h]
      exact ⟨isPrimePow_two_pow (by omega), by rw [hB]; linarith, by rw [hB]; linarith⟩
    · rw [mem_singleton.mp h]
      exact ⟨isPrimePow_two_pow (by omega), by rw [hC]; linarith, by rw [hC]⟩
  · rw [sum_insert hnotmem, sum_pair h12, threePowCoeff_0, threePowCoeff_1, threePowCoeff_2,
      hA, hB, hC, show (2 : ℝ) * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) by ring,
      show (4 : ℝ) * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 2) by ring,
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    ring
  · rw [sum_insert hnotmem, sum_pair h12, threePowCoeff_0, threePowCoeff_1, threePowCoeff_2]
    norm_num
  · exact ⟨2 ^ k, mem_insert_self _ _, by rw [threePowCoeff_0]; norm_num⟩

/-! ### The window read by the lag family -/

/-- **The lag window carries no short relation.** At lag `v` and width `2w < log 2` the prime
powers read by the two-bump test at that lag admit no nontrivial integer relation among their
frequencies of `ℓ¹` norm at most `2(v − 2w)/log 3`: the admissible relation order grows linearly
in the lag. -/
theorem lagPrimeWindow_relation_eq_zero {v w : ℝ} (hw2 : 2 * w < Real.log 2) {s : Finset ℕ}
    (hs : ∀ n ∈ s, n ∈ lagPrimeWindow v w ∧ IsPrimePow n) {c : ℕ → ℤ}
    (hrel : ∑ n ∈ s, (c n : ℝ) * Real.log n = 0)
    (hsmall : ((∑ n ∈ s, |c n| : ℤ) : ℝ) * Real.log 3 ≤ 2 * (v - 2 * w)) :
    ∀ n ∈ s, c n = 0 := by
  have hY0 : 0 < Real.exp (v - 2 * w) := Real.exp_pos _
  have hlogY : Real.log (Real.exp (v - 2 * w)) = v - 2 * w := Real.log_exp _
  refine window_relation_eq_zero_of_log hY0 (fun n hn => ?_) hrel (by rw [hlogY]; exact hsmall)
  obtain ⟨hnw, hnp⟩ := hs n hn
  have hn2 : 2 ≤ n := two_le_of_isPrimePow hnp
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp (mem_filter.mp hnw).2
  refine ⟨hnp, ?_, ?_⟩
  · calc Real.exp (v - 2 * w) ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = (n : ℝ) := Real.exp_log hnpos
  · have hup : (n : ℝ) ≤ Real.exp (v + 2 * w) := by
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp (v + 2 * w) := Real.exp_le_exp.mpr (by linarith)
    have hsplit : Real.exp (v + 2 * w) = Real.exp (v - 2 * w) * Real.exp (4 * w) := by
      rw [← Real.exp_add]
      ring_nf
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h4 : Real.exp (4 * w) < 4 := by
      calc Real.exp (4 * w) < Real.exp (Real.log 4) :=
            Real.exp_lt_exp.mpr (by rw [hlog4]; linarith)
        _ = 4 := Real.exp_log (by norm_num)
    calc (n : ℝ) ≤ Real.exp (v - 2 * w) * Real.exp (4 * w) := by rw [← hsplit]; exact hup
      _ < Real.exp (v - 2 * w) * 4 := mul_lt_mul_of_pos_left h4 hY0
      _ = 4 * Real.exp (v - 2 * w) := by ring

end GaloisForLFunctions.SquareRootThreshold
