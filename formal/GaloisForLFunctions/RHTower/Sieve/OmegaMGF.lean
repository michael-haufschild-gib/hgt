import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# Factorial moments of the small-prime count

For a squarefree modulus the divisors with a prescribed number of prime factors are counted by a
binomial coefficient, so the `i`-th factorial moment of

`ω_{≤z}(n) = ω (gcd n z#)`

over an interval is an exact divisor sum:

`∑_{n ∈ (a,b]} C(ω_{≤z} n, i) = ∑_{d ∣ z#, ω d = i} #{n ∈ (a,b] : d ∣ n}`.

Each inner count is `(b-a)/d` up to one unit, so the moment is `(b-a)` times an elementary
symmetric function of `(1/p)_{p ≤ z}` plus an error of one unit per divisor.  Truncated Bonferroni
combinations of these moments give both tails of `ω_{≤z}` with the sharp Chernoff rate, the number
of divisors involved staying bounded by the truncation level.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Divisors with a prescribed number of prime factors.**  For squarefree `m` these are counted
by a binomial coefficient. -/
theorem card_divisors_filter_card_primeFactors_eq {m : ℕ} (hm : Squarefree m) (i : ℕ) :
    (#{d ∈ m.divisors | d.primeFactors.card = i}) = (m.primeFactors.card).choose i := by
  classical
  rw [← Finset.card_powersetCard i m.primeFactors]
  refine Finset.card_bij' (fun d _ => d.primeFactors) (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdmem, hdcard⟩ := Finset.mem_filter.1 hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hdmem
    exact Finset.mem_powersetCard.2 ⟨Nat.primeFactors_mono hdvd hm.ne_zero, hdcard⟩
  · intro t ht
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    have hdvd : (∏ p ∈ t, p) ∣ m :=
      dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
        (Nat.prod_primeFactors_of_squarefree hm).dvd
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdvd, hm.ne_zero⟩, ?_⟩
    rw [Nat.primeFactors_prod hprime]
    exact hcard
  · intro d hd
    obtain ⟨hdmem, -⟩ := Finset.mem_filter.1 hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hdmem
    exact Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hdvd)
  · intro t ht
    obtain ⟨hsub, -⟩ := Finset.mem_powersetCard.1 ht
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)

/-- The number of primes at most `z` dividing `n`. -/
def omegaSmall (z n : ℕ) : ℕ := (Nat.gcd n (primorial z)).primeFactors.card

/-- The divisors of `z#` with exactly `i` prime factors. -/
def levelDivisors (z i : ℕ) : Finset ℕ :=
  {d ∈ (primorial z).divisors | d.primeFactors.card = i}

theorem levelDivisors_gcd (z n i : ℕ) :
    {d ∈ (Nat.gcd n (primorial z)).divisors | d.primeFactors.card = i}
      = {d ∈ levelDivisors z i | d ∣ n} := by
  ext d
  have hm0 : primorial z ≠ 0 := (squarefree_primorial z).ne_zero
  have hgcd : Nat.gcd n (primorial z) ≠ 0 := Nat.gcd_ne_zero_right hm0
  simp only [levelDivisors, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, hgcd, hm0,
    ne_eq, not_false_eq_true, and_true]
  tauto

/-- **Factorial moment identity.**  The `i`-th factorial moment of the small-prime count over an
interval is an exact divisor sum. -/
theorem sum_choose_omegaSmall_eq (z a b i : ℕ) :
    ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i)
      = ∑ d ∈ levelDivisors z i, (#{n ∈ Finset.Ioc a b | d ∣ n}) := by
  classical
  have hsq : Squarefree (primorial z) := squarefree_primorial z
  have hterm : ∀ n ∈ Finset.Ioc a b,
      (omegaSmall z n).choose i = ∑ d ∈ levelDivisors z i, (if d ∣ n then 1 else 0) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Ioc.1 hn).1
      omega
    have hgsq : Squarefree (Nat.gcd n (primorial z)) :=
      hsq.squarefree_of_dvd (Nat.gcd_dvd_right n (primorial z))
    have hcount := card_divisors_filter_card_primeFactors_eq hgsq i
    rw [omegaSmall, ← hcount, levelDivisors_gcd z n i, Finset.card_eq_sum_ones,
      Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]

/-- Truncated binomial expansion of `(1-x)^w`. -/
noncomputable def binomialPartial (x : ℝ) (w r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), (w.choose i : ℝ) * (-x) ^ i

theorem binomialPartial_zero (x : ℝ) (r : ℕ) : binomialPartial x 0 r = 1 := by
  unfold binomialPartial
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      simp [ih]

theorem binomialPartial_succ (x : ℝ) (w r : ℕ) :
    binomialPartial x (w + 1) (r + 1)
      = binomialPartial x w (r + 1) + (-x) * binomialPartial x w r := by
  unfold binomialPartial
  have hcomb : ∑ k ∈ Finset.range (r + 1), (w.choose (k + 1) : ℝ) * (-x) ^ (k + 1)
      + ∑ i ∈ Finset.range (r + 1), -x * ((w.choose i : ℝ) * (-x) ^ i)
      = ∑ k ∈ Finset.range (r + 1), ((w + 1).choose (k + 1) : ℝ) * (-x) ^ (k + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [Finset.sum_range_succ' (fun i => ((w + 1).choose i : ℝ) * (-x) ^ i) (r + 1),
    Finset.sum_range_succ' (fun i => (w.choose i : ℝ) * (-x) ^ i) (r + 1), Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  linarith [hcomb]

/-- **Bonferroni inequalities for the binomial expansion.**  Truncating `(1-x)^w` at level `r`
overshoots for even `r` and undershoots for odd `r`, for every `x ∈ [0,1]`. -/
theorem binomialPartial_sign {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ w r : ℕ, 0 ≤ (-1 : ℝ) ^ r * (binomialPartial x w r - (1 - x) ^ w) := by
  intro w
  induction w with
  | zero =>
      intro r
      rw [binomialPartial_zero]
      simp
  | succ w ih =>
      intro r
      cases r with
      | zero =>
          have hb : binomialPartial x (w + 1) 0 = 1 := by
            unfold binomialPartial
            simp
          have hle : (1 - x) ^ (w + 1) ≤ 1 := by
            refine pow_le_one₀ (by linarith) (by linarith)
          rw [hb]
          simp only [pow_zero, one_mul]
          linarith
      | succ r' =>
          have hrec := binomialPartial_succ x w r'
          have h1 := ih (r' + 1)
          have h2 := ih r'
          have hexp : (1 - x) ^ (w + 1) = (1 - x) * (1 - x) ^ w := by ring
          have hsplit : (-1 : ℝ) ^ (r' + 1) * (binomialPartial x (w + 1) (r' + 1)
                - (1 - x) ^ (w + 1))
              = (-1 : ℝ) ^ (r' + 1) * (binomialPartial x w (r' + 1) - (1 - x) ^ w)
                + x * ((-1 : ℝ) ^ r' * (binomialPartial x w r' - (1 - x) ^ w)) := by
            rw [hrec, hexp, pow_succ]
            ring
          rw [hsplit]
          have := mul_nonneg hx0 h2
          linarith

/-- **Upper indicator.**  A truncated factorial-moment combination dominates the indicator of
`k ≤ w`, for every tilt `u ≥ 1`. -/
theorem indicator_mul_pow_le_sum_choose {u : ℝ} (hu : 1 ≤ u) (k w : ℕ) :
    (if k ≤ w then (1 : ℝ) else 0) * u ^ k
      ≤ ∑ i ∈ Finset.range (k + 1), (w.choose i : ℝ) * (u - 1) ^ i := by
  have hu0 : (0 : ℝ) ≤ u - 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), (w.choose i : ℝ) * (u - 1) ^ i := by
    refine Finset.sum_nonneg ?_
    intro i _
    positivity
  by_cases hk : k ≤ w
  · rw [if_pos hk, one_mul]
    have hbin : u ^ k = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (u - 1) ^ i := by
      have := add_pow (u - 1) (1 : ℝ) k
      simp only [one_pow, mul_one] at this
      rw [show u - 1 + 1 = u by ring] at this
      rw [this]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hbin]
    refine Finset.sum_le_sum ?_
    intro i _
    have hchoose : (k.choose i : ℝ) ≤ (w.choose i : ℝ) := by
      exact_mod_cast Nat.choose_le_choose i hk
    exact mul_le_mul_of_nonneg_right hchoose (by positivity)
  · rw [if_neg hk, zero_mul]
    exact hnonneg

/-- **Lower indicator.**  An even Bonferroni truncation dominates the indicator of `w ≤ k`, for
every tilt `0 < t ≤ 1`. -/
theorem indicator_mul_pow_le_binomialPartial {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {r : ℕ}
    (hr : Even r) (k w : ℕ) :
    (if w ≤ k then (1 : ℝ) else 0) * t ^ k ≤ binomialPartial (1 - t) w r := by
  have hx0 : (0 : ℝ) ≤ 1 - t := by linarith
  have hx1 : (1 : ℝ) - t ≤ 1 := by linarith
  have hsign := binomialPartial_sign hx0 hx1 w r
  rw [hr.neg_one_pow, one_mul] at hsign
  have hpow : (1 : ℝ) - (1 - t) = t := by ring
  rw [hpow] at hsign
  have hge : t ^ w ≤ binomialPartial (1 - t) w r := by linarith
  by_cases hk : w ≤ k
  · rw [if_pos hk, one_mul]
    have : t ^ k ≤ t ^ w := pow_le_pow_of_le_one ht0.le ht1 hk
    linarith
  · rw [if_neg hk, zero_mul]
    have : (0 : ℝ) < t ^ w := pow_pos ht0 w
    linarith

/-- Every level divisor is positive. -/
theorem pos_of_mem_levelDivisors {z i d : ℕ} (hd : d ∈ levelDivisors z i) : 0 < d := by
  have := (Finset.mem_filter.1 hd).1
  exact Nat.pos_of_mem_divisors this

/-- **Moment estimate.**  The `i`-th factorial moment is the interval length times an elementary
symmetric weight, up to one unit per level divisor. -/
theorem abs_sum_choose_omegaSmall_sub_le (z a b i : ℕ) (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ))
        - ((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d|
      ≤ ((levelDivisors z i).card : ℝ) := by
  have hid : (∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ))
      = ∑ d ∈ levelDivisors z i, ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) := by
    have := sum_choose_omegaSmall_eq z a b i
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
  have hmain : ((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d
      = ∑ d ∈ levelDivisors z i, ((b : ℝ) - a) / d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    ring
  rw [hid, hmain, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ d ∈ levelDivisors z i,
      |((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) - ((b : ℝ) - a) / d| ≤ 1 := by
    intro d hd
    exact (abs_card_filter_dvd_Ioc_sub_lt d a b (pos_of_mem_levelDivisors hd) hab).le
  calc ∑ d ∈ levelDivisors z i,
        |((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) - ((b : ℝ) - a) / d|
      ≤ ∑ _d ∈ levelDivisors z i, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((levelDivisors z i).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Upper tail of the small-prime count.**  Sharp Chernoff shape: the main term is the tilted
Euler weight, the error one unit per level divisor. -/
theorem card_omegaSmall_ge_mul_pow_le (z a b k : ℕ) (hab : a ≤ b) {u : ℝ} (hu : 1 ≤ u) :
    ((#{n ∈ Finset.Ioc a b | k ≤ omegaSmall z n} : ℕ) : ℝ) * u ^ k
      ≤ ((b : ℝ) - a) * (∑ i ∈ Finset.range (k + 1),
            (u - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
        + ∑ i ∈ Finset.range (k + 1), (u - 1) ^ i * ((levelDivisors z i).card : ℝ) := by
  classical
  have hu0 : (0 : ℝ) ≤ u - 1 := by linarith
  have hcard : ((#{n ∈ Finset.Ioc a b | k ≤ omegaSmall z n} : ℕ) : ℝ)
      = ∑ n ∈ Finset.Ioc a b, (if k ≤ omegaSmall z n then (1 : ℝ) else 0) :=
    Finset.natCast_card_filter (fun n => k ≤ omegaSmall z n) (Finset.Ioc a b)
  rw [hcard, Finset.sum_mul]
  have hpt : ∀ n ∈ Finset.Ioc a b,
      (if k ≤ omegaSmall z n then (1 : ℝ) else 0) * u ^ k
        ≤ ∑ i ∈ Finset.range (k + 1), ((omegaSmall z n).choose i : ℝ) * (u - 1) ^ i :=
    fun n _ => indicator_mul_pow_le_sum_choose hu k (omegaSmall z n)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_comm]
  have hswap : ∀ i ∈ Finset.range (k + 1),
      ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ) * (u - 1) ^ i
        = (u - 1) ^ i * ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ) := by
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl hswap]
  have hstep : ∀ i ∈ Finset.range (k + 1),
      (u - 1) ^ i * ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ)
        ≤ (u - 1) ^ i * (((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
          + (u - 1) ^ i * ((levelDivisors z i).card : ℝ) := by
    intro i _
    have habs := abs_sum_choose_omegaSmall_sub_le z a b i hab
    have hle : ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ)
        ≤ ((b : ℝ) - a) * (∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
          + ((levelDivisors z i).card : ℝ) := by
      have := (abs_le.1 habs).2
      linarith
    have hpow : (0 : ℝ) ≤ (u - 1) ^ i := by positivity
    nlinarith [hle, hpow]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Lower tail of the small-prime count.**  An even Bonferroni truncation gives the sharp
Chernoff shape with the same one-unit-per-divisor error. -/
theorem card_omegaSmall_le_mul_pow_le (z a b k r : ℕ) (hab : a ≤ b) (hr : Even r) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((#{n ∈ Finset.Ioc a b | omegaSmall z n ≤ k} : ℕ) : ℝ) * t ^ k
      ≤ ((b : ℝ) - a) * (∑ i ∈ Finset.range (r + 1),
            (t - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
        + ∑ i ∈ Finset.range (r + 1), ((levelDivisors z i).card : ℝ) := by
  classical
  have hcard : ((#{n ∈ Finset.Ioc a b | omegaSmall z n ≤ k} : ℕ) : ℝ)
      = ∑ n ∈ Finset.Ioc a b, (if omegaSmall z n ≤ k then (1 : ℝ) else 0) :=
    Finset.natCast_card_filter (fun n => omegaSmall z n ≤ k) (Finset.Ioc a b)
  rw [hcard, Finset.sum_mul]
  have hpt : ∀ n ∈ Finset.Ioc a b,
      (if omegaSmall z n ≤ k then (1 : ℝ) else 0) * t ^ k
        ≤ ∑ i ∈ Finset.range (r + 1), ((omegaSmall z n).choose i : ℝ) * (t - 1) ^ i := by
    intro n _
    have := indicator_mul_pow_le_binomialPartial ht0 ht1 hr k (omegaSmall z n)
    unfold binomialPartial at this
    have hneg : ∀ i : ℕ, (-(1 - t)) ^ i = (t - 1) ^ i := by
      intro i
      rw [show -(1 - t) = t - 1 by ring]
    simpa [hneg] using this
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_comm]
  have hswap : ∀ i ∈ Finset.range (r + 1),
      ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ) * (t - 1) ^ i
        = (t - 1) ^ i * ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ) := by
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl hswap]
  have hstep : ∀ i ∈ Finset.range (r + 1),
      (t - 1) ^ i * ∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ)
        ≤ (t - 1) ^ i * (((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
          + ((levelDivisors z i).card : ℝ) := by
    intro i _
    have habs := abs_sum_choose_omegaSmall_sub_le z a b i hab
    have hpow : |(t - 1) ^ i| ≤ 1 := by
      rw [abs_pow]
      refine pow_le_one₀ (abs_nonneg _) ?_
      rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
      linarith
    have h1 : (t - 1) ^ i * ((∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ))
          - ((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
        ≤ |(t - 1) ^ i| * |(∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ))
          - ((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |(t - 1) ^ i| * |(∑ n ∈ Finset.Ioc a b, ((omegaSmall z n).choose i : ℝ))
          - ((b : ℝ) - a) * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d|
        ≤ 1 * ((levelDivisors z i).card : ℝ) :=
      mul_le_mul hpow habs (abs_nonneg _) zero_le_one
    nlinarith [h1, h2]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

end RHTower.Sieve
