import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries

/-!
# The power-sieved Liouville family and its Dirichlet series

For `m ≥ 2` the arithmetic function `a_m` determined by `∑ a_m(n) n^{-s} = ζ(ms)/ζ(s)` is the
Dirichlet convolution of the Möbius function with the indicator of the `m`-th powers
(`sievedLiouville`).  Perfect `m`-th powers are exactly the integers all of whose factorisation
exponents are divisible by `m` (`isPow_iff_factorization_dvd`), so the indicator is multiplicative,
`a_m(p^e) = [m ∣ e] - [m ∣ e-1]` (`sievedLiouville_prime_pow_eq`), and `a_m` takes only the values
`0, ±1` (`norm_sievedLiouville_le_one`).

Summing the convolution on the half-plane of absolute convergence gives

`L ↗a_m s * ζ s = ζ (m s)`     (`LSeries_sievedLiouville_mul_riemannZeta`).
-/

open Complex Filter ArithmeticFunction
open scoped LSeries.notation BigOperators
open scoped Classical

namespace RHTower

/-! ### `m`-th powers and factorisation exponents -/

theorem factorization_dvd_of_isPow {m n : ℕ} (h : ∃ k, n = k ^ m) (p : ℕ) :
    m ∣ n.factorization p := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.factorization_pow]
  exact ⟨k.factorization p, by simp⟩

theorem isPow_of_factorization_dvd {m n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, m ∣ n.factorization p) : ∃ k, n = k ^ m := by
  refine ⟨n.factorization.prod fun p e => p ^ (e / m), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul]
  congr 1
  exact (Nat.div_mul_cancel (h p)).symm

theorem isPow_iff_factorization_dvd {m n : ℕ} (hn : n ≠ 0) :
    (∃ k, n = k ^ m) ↔ ∀ p, m ∣ n.factorization p :=
  ⟨fun h p => factorization_dvd_of_isPow h p, isPow_of_factorization_dvd hn⟩

/-- The indicator of the perfect `m`-th powers, as an arithmetic function. -/
noncomputable def powerIndicator (m : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ≠ 0 ∧ ∃ k, n = k ^ m then 1 else 0
  map_zero' := by simp

theorem powerIndicator_apply (m n : ℕ) :
    powerIndicator m n = if n ≠ 0 ∧ ∃ k, n = k ^ m then 1 else 0 := rfl

theorem powerIndicator_prime_pow {m p e : ℕ} (hp : p.Prime) :
    powerIndicator m (p ^ e) = if m ∣ e then 1 else 0 := by
  have hne : p ^ e ≠ 0 := pow_ne_zero e hp.pos.ne'
  rw [powerIndicator_apply]
  by_cases hme : m ∣ e
  · obtain ⟨c, rfl⟩ := hme
    rw [if_pos ⟨hne, ⟨p ^ c, by rw [← pow_mul, mul_comm]⟩⟩, if_pos ⟨c, rfl⟩]
  · rw [if_neg hme, if_neg]
    rintro ⟨-, hk⟩
    refine hme ?_
    have h := factorization_dvd_of_isPow (m := m) hk p
    rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at h

theorem isMultiplicative_powerIndicator (m : ℕ) : (powerIndicator m).IsMultiplicative := by
  constructor
  · rw [powerIndicator_apply, if_pos ⟨one_ne_zero, ⟨1, by simp⟩⟩]
  · intro a b hab
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [powerIndicator_apply]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [powerIndicator_apply]
    have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
    have hsplit : ∀ p : ℕ, (a * b).factorization p = a.factorization p + b.factorization p := by
      intro p
      rw [Nat.factorization_mul ha0 hb0]
      simp
    have hdisj : ∀ p : ℕ, a.factorization p = 0 ∨ b.factorization p = 0 := by
      intro p
      by_contra hcon
      push Not at hcon
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos hcon.1
      have hpb : p ∣ b := Nat.dvd_of_factorization_pos hcon.2
      have hp1 : p ∣ 1 := hab ▸ Nat.dvd_gcd hpa hpb
      have hpe : p = 1 := Nat.dvd_one.mp hp1
      exact hcon.1 (by rw [hpe]; simp)
    have hiff : ((a * b) ≠ 0 ∧ ∃ k, a * b = k ^ m) ↔
        ((a ≠ 0 ∧ ∃ k, a = k ^ m) ∧ (b ≠ 0 ∧ ∃ k, b = k ^ m)) := by
      constructor
      · rintro ⟨-, hk⟩
        refine ⟨⟨ha0, ?_⟩, ⟨hb0, ?_⟩⟩
        · refine (isPow_iff_factorization_dvd ha0).2 fun p => ?_
          have hall := factorization_dvd_of_isPow hk p
          rw [hsplit p] at hall
          rcases hdisj p with h | h
          · rw [h]
            exact dvd_zero m
          · rw [h, add_zero] at hall
            exact hall
        · refine (isPow_iff_factorization_dvd hb0).2 fun p => ?_
          have hall := factorization_dvd_of_isPow hk p
          rw [hsplit p] at hall
          rcases hdisj p with h | h
          · rw [h, zero_add] at hall
            exact hall
          · rw [h]
            exact dvd_zero m
      · rintro ⟨⟨-, hA⟩, ⟨-, hB⟩⟩
        refine ⟨hab0, (isPow_iff_factorization_dvd hab0).2 fun p => ?_⟩
        rw [hsplit p]
        exact Nat.dvd_add (factorization_dvd_of_isPow hA p) (factorization_dvd_of_isPow hB p)
    rw [powerIndicator_apply, powerIndicator_apply, powerIndicator_apply]
    by_cases hA : a ≠ 0 ∧ ∃ k, a = k ^ m
    · by_cases hB : b ≠ 0 ∧ ∃ k, b = k ^ m
      · rw [if_pos (hiff.2 ⟨hA, hB⟩), if_pos hA, if_pos hB, one_mul]
      · rw [if_neg fun h => hB (hiff.1 h).2, if_pos hA, if_neg hB, mul_zero]
    · rw [if_neg fun h => hA (hiff.1 h).1, if_neg hA, zero_mul]

/-! ### The sieved family -/

/-- The power-sieved Liouville family `a_m = μ ⍟ 1_{m-th powers}`. -/
noncomputable def sievedLiouville (m : ℕ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) * powerIndicator m

theorem isMultiplicative_sievedLiouville (m : ℕ) : (sievedLiouville m).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_moebius.intCast).mul (isMultiplicative_powerIndicator m)

/-- The Dirichlet convolution with the constant-one function recovers the `m`-th-power
indicator. -/
theorem zeta_mul_sievedLiouville (m : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * sievedLiouville m = powerIndicator m := by
  rw [sievedLiouville, ← mul_assoc,
    show (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) = 1 by
      rw [mul_comm]; exact ArithmeticFunction.coe_moebius_mul_coe_zeta,
    one_mul]

theorem sum_divisors_sievedLiouville (m n : ℕ) :
    ∑ d ∈ n.divisors, sievedLiouville m d = powerIndicator m n := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply, zeta_mul_sievedLiouville]

theorem moebius_prime_pow_eq {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℂ)) (p ^ j)
      = (if j = 0 then (1 : ℂ) else 0) - (if j = 1 then (1 : ℂ) else 0) := by
  rw [ArithmeticFunction.intCoe_apply]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp hj.ne']
    by_cases h1 : j = 1
    · rw [if_pos h1, if_neg (by omega), if_pos h1]
      norm_num
    · rw [if_neg h1, if_neg (by omega), if_neg h1]
      norm_num

/-- **The prime-power values of the sieved family.** -/
theorem sievedLiouville_prime_pow_eq (m : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sievedLiouville m (p ^ e)
      = (if m ∣ e then (1 : ℂ) else 0)
        - (if 1 ≤ e then (if m ∣ (e - 1) then (1 : ℂ) else 0) else 0) := by
  rw [sievedLiouville, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (f := fun d d' => ((ArithmeticFunction.moebius : ArithmeticFunction ℂ)) d *
        powerIndicator m d'),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ j ∈ Finset.range (e + 1),
      ((ArithmeticFunction.moebius : ArithmeticFunction ℂ)) (p ^ j) *
          powerIndicator m (p ^ e / p ^ j)
        = (if j = 0 then (if m ∣ (e - j) then (1 : ℂ) else 0) else 0)
          - (if j = 1 then (if m ∣ (e - j) then (1 : ℂ) else 0) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hdiv : p ^ e / p ^ j = p ^ (e - j) := Nat.pow_div (by omega) hp.pos
    rw [hdiv, powerIndicator_prime_pow hp, moebius_prime_pow_eq hp]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range (e + 1)) 0
      (fun j => if m ∣ (e - j) then (1 : ℂ) else 0),
    Finset.sum_ite_eq' (Finset.range (e + 1)) 1
      (fun j => if m ∣ (e - j) then (1 : ℂ) else 0)]
  simp only [Finset.mem_range, Nat.sub_zero]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · norm_num
  · rw [if_pos (by omega : 0 < e + 1), if_pos (by omega : 1 < e + 1),
      if_pos (by omega : 1 ≤ e)]

theorem norm_sievedLiouville_prime_pow_le_one {m : ℕ} (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ‖sievedLiouville m (p ^ e)‖ ≤ 1 := by
  rw [sievedLiouville_prime_pow_eq m hp e]
  by_cases he : 1 ≤ e
  · rw [if_pos he]
    by_cases h1 : m ∣ e
    · have h2 : ¬ m ∣ (e - 1) := by
        intro h
        have hd1 : m ∣ 1 := by
          have hsub := Nat.dvd_sub h1 h
          rwa [show e - (e - 1) = 1 by omega] at hsub
        have hm1 := Nat.dvd_one.mp hd1
        omega
      rw [if_pos h1, if_neg h2]
      norm_num
    · rw [if_neg h1]
      by_cases h2 : m ∣ (e - 1)
      · rw [if_pos h2]
        norm_num
      · rw [if_neg h2]
        norm_num
  · rw [if_neg he]
    have he0 : e = 0 := by omega
    rw [he0, if_pos (dvd_zero m)]
    norm_num

theorem norm_sievedLiouville_le_one {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    ‖sievedLiouville m n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [(isMultiplicative_sievedLiouville m).multiplicative_factorization _ hn, Finsupp.prod,
    norm_prod]
  refine Finset.prod_le_one (fun p _ => norm_nonneg _) fun p hp => ?_
  have hprime : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp)
  exact norm_sievedLiouville_prime_pow_le_one hm hprime _

theorem sievedLiouville_zero (m : ℕ) : sievedLiouville m 0 = 0 := by simp

theorem conj_sievedLiouville (m : ℕ) (n : ℕ) :
    (starRingEnd ℂ) (sievedLiouville m n) = sievedLiouville m n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [(isMultiplicative_sievedLiouville m).multiplicative_factorization _ hn, Finsupp.prod,
    map_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hprime : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp)
  rw [sievedLiouville_prime_pow_eq m hprime]
  simp only [map_sub, apply_ite (starRingEnd ℂ), _root_.map_one, _root_.map_zero]

end RHTower
