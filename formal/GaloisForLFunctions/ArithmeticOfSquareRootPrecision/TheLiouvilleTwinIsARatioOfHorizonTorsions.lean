import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheBatteryOfTheCount

/-!
# The Liouville twin is a ratio of horizon torsions

For a prime power `m = p^k` the Liouville twin weight is `(−1)^k log p`, and `k` is even exactly
when `m` is a square. Hence `λΛ = 2 Λ·1_{Ω even} − Λ`, and the squares `j²` with `Λ(j²) = Λ(j)`
carry the even part. This gives the exact identity (`partialSum_liouvilleWeight_eq`)

`Σ_{m ≤ n} λ(m) Λ(m) = 2 ψ(⌊√n⌋) − ψ(n)`.

In the language of horizon torsion (`ψ(N) = log |ℤ / lcm(1, …, N)|`):

* `lcm(1, …, ⌊√n⌋)² ∣ lcm(1, …, n)` (`lcmUpto_sqrt_sq_dvd`), since `2 ⌊log_p √n⌋ ≤ log_p n`;
* the twin's horizon value is the **reciprocal** of the order of a finite group
  (`exp_partialSum_liouvilleWeight`):
  `exp(Σ_{m ≤ n} λΛ(m)) = 1 / r_n`, `r_n = lcm(1, …, n) / lcm(1, …, ⌊√n⌋)²`.

So integrality sees parity: for `Λ` each new horizon point multiplies the torsion by a cyclic
kernel, for the twin the torsion of the squares is counted twice against the horizon and the net
value is a reciprocal group order. The identity is an exact (precision-`0`) statement, and it shows
at once why the twin fails the count: `2ψ(√n) − ψ(n) − n = −2n + O(√n)`.
-/

noncomputable section

open Real Finset
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The even part of `Λ`: `Λ(m)` if `Ω(m)` is even, else `0`. -/
def evenVonMangoldt (m : ℕ) : ℝ := if Even (cardFactors m) then vonMangoldt m else 0

/-- `λΛ = 2 Λ·1_{Ω even} − Λ`. -/
theorem liouvilleWeight_eq (m : ℕ) :
    liouvilleWeight m = 2 * evenVonMangoldt m - vonMangoldt m := by
  unfold liouvilleWeight evenVonMangoldt
  split_ifs with h
  · rw [h.neg_one_pow]; ring
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]; ring

/-- **The even part of `Λ` is carried by the squares**: `Σ_{m ≤ n} Λ(m)1_{Ω(m) even} = ψ(⌊√n⌋)`. -/
theorem sum_evenVonMangoldt (n : ℕ) :
    ∑ m ∈ Ioc 0 n, evenVonMangoldt m = Chebyshev.psi (Nat.sqrt n) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  symm
  refine sum_bij_ne_zero (fun j _ _ => j ^ 2) ?_ ?_ ?_ ?_
  · intro j hj _
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hj
    exact mem_Ioc.mpr ⟨by positivity, Nat.le_sqrt'.mp h2⟩
  · intro a _ _ b _ _ h
    exact Nat.pow_left_injective (by norm_num) h
  · intro m hm hne
    have hΛ : vonMangoldt m ≠ 0 := by
      intro h0; apply hne; simp [evenVonMangoldt, h0]
    have heven : Even (cardFactors m) := by
      by_contra h; apply hne; simp [evenVonMangoldt, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff _ |>.mp
      (not_not.mp (mt ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hΛ))
    rw [ArithmeticFunction.cardFactors_apply_prime_pow hp] at heven
    obtain ⟨i, rfl⟩ := heven
    have hi : 0 < i := by omega
    refine ⟨p ^ i, mem_Ioc.mpr ⟨by have := hp.pos; positivity, Nat.le_sqrt'.mpr ?_⟩, ?_, ?_⟩
    · rw [← pow_mul, mul_two]; exact (mem_Ioc.mp hm).2
    · rw [ArithmeticFunction.vonMangoldt_apply_pow hi.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    · rw [← pow_mul, mul_two]
  · intro j hj _
    have hj0 : j ≠ 0 := by have := (mem_Ioc.mp hj).1; omega
    have heven : Even (cardFactors (j ^ 2)) := by
      rw [sq, ArithmeticFunction.cardFactors_mul hj0 hj0]; exact ⟨_, rfl⟩
    simp [evenVonMangoldt, heven, ArithmeticFunction.vonMangoldt_apply_pow (two_ne_zero)]

/-- **The Liouville identity**: `Σ_{m ≤ n} λΛ(m) = 2 ψ(⌊√n⌋) − ψ(n)`. -/
theorem partialSum_liouvilleWeight_eq (n : ℕ) :
    partialSum liouvilleWeight n = 2 * Chebyshev.psi (Nat.sqrt n) - Chebyshev.psi n := by
  unfold partialSum
  simp_rw [liouvilleWeight_eq]
  rw [sum_sub_distrib, ← mul_sum, Nat.floor_natCast, sum_evenVonMangoldt]
  simp only [Chebyshev.psi, Nat.floor_natCast]

/-- `lcm(1, …, ⌊√n⌋)² ∣ lcm(1, …, n)`. -/
theorem lcmUpto_sqrt_sq_dvd (n : ℕ) : Nat.lcmUpto (Nat.sqrt n) ^ 2 ∣ Nat.lcmUpto n := by
  refine (Nat.factorization_le_iff_dvd (pow_ne_zero 2 (Nat.lcmUpto_ne_zero _))
    (Nat.lcmUpto_ne_zero n)).mp fun p => ?_
  by_cases hp : p.Prime
  · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_lcmUpto _ hp, Nat.factorization_lcmUpto _ hp]
    rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h0 | h0
    · simp [h0]
    refine Nat.le_log_of_pow_le hp.one_lt ?_
    calc p ^ (2 * p.log (Nat.sqrt n)) = (p ^ p.log (Nat.sqrt n)) ^ 2 := by ring
      _ ≤ Nat.sqrt n ^ 2 := Nat.pow_le_pow_left (Nat.pow_log_le_self p h0.ne') 2
      _ ≤ n := Nat.sqrt_le' n
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The twin's **reciprocal torsion** `r_n = lcm(1, …, n) / lcm(1, …, ⌊√n⌋)²`. -/
def twinTorsion (n : ℕ) : ℕ := Nat.lcmUpto n / Nat.lcmUpto (Nat.sqrt n) ^ 2

theorem twinTorsion_pos (n : ℕ) : 0 < twinTorsion n :=
  Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos n) (lcmUpto_sqrt_sq_dvd n))
    (pow_pos (Nat.lcmUpto_pos _) 2)

/-- **The twin's horizon value is a reciprocal group order**:
`exp(Σ_{m ≤ n} λΛ(m)) = 1 / |ℤ / r_n ℤ|`. -/
theorem exp_partialSum_liouvilleWeight (n : ℕ) :
    exp (partialSum liouvilleWeight n) = 1 / (Nat.card (ZMod (twinTorsion n)) : ℝ) := by
  have hd := lcmUpto_sqrt_sq_dvd n
  have hs : (0 : ℝ) < Nat.lcmUpto (Nat.sqrt n) := by exact_mod_cast Nat.lcmUpto_pos _
  have hl : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos _
  rw [partialSum_liouvilleWeight_eq, Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi_eq_log_lcmUpto,
    Nat.card_zmod, twinTorsion,
    Nat.cast_div hd (by exact_mod_cast (pow_pos (Nat.lcmUpto_pos _) 2).ne'), Real.exp_sub, mul_comm,
    Real.exp_mul, Real.exp_log hs, Real.exp_log hl]
  push_cast
  rw [Real.rpow_two]
  field_simp

/-- The twin's partial sum is minus a log-order: `Σ_{m ≤ n} λΛ(m) = −log |ℤ / r_n ℤ| ≤ 0`. -/
theorem partialSum_liouvilleWeight_eq_neg_log (n : ℕ) :
    partialSum liouvilleWeight n = -Real.log (Nat.card (ZMod (twinTorsion n))) := by
  have h := congrArg Real.log (exp_partialSum_liouvilleWeight n)
  rw [Real.log_exp, one_div, Real.log_inv] at h
  exact h

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
