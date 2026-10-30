import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Factorial ratios have bounded multiplicity above the square root

The producer ledger says that an auxiliary integer `A` vanishing to order `m_p` at the counted
primes pays `Σ m_p log p ≤ log A`. Stepanov's auxiliary over `𝔽_q` reaches multiplicity `≈ √q` at every
counted point because Frobenius makes `x^q = x`. Over `ℤ` the classical producers are balanced
factorial ratios `A_n = ∏_i (a_i n)! / ∏_j (b_j n)!` with `Σ a_i = Σ b_j` (Chebyshev's
`(30n)! n! / ((15n)! (10n)! (6n)!)`, the central binomial coefficient). This file shows that their
multiplicity cannot grow.

* **Legendre above the square root** (`padicValNat_factorial_of_lt_sq`). If `m < p²`, then
  `v_p(m!) = ⌊m/p⌋`.
* **Floors of a sum** (`sum_div_le_div_sum`, `div_sum_le_sum_div_add`). `Σ ⌊c_j/p⌋ ≤ ⌊Σ c_j/p⌋ ≤
  Σ ⌊c_j/p⌋ + (#T − 1)`.
* **Bounded multiplicity** (`sum_padicValNat_factorial_le`, `padicValNat_le_of_factorialRatio`).
  For every prime `p` with `p² > a_i n, b_j n`, the ratio has `v_p(A_n) ≤ #T − 1`, the number of
  denominator factorials minus one, uniformly in `n`. The central binomial coefficient
  (`padicValNat_centralBinom_le_one`) has multiplicity at most one above `√(2n)`.

So the factorial-ratio producers have a fixed multiplicity ceiling on all primes above the square
root of their length, the range where the counting happens. A Frobenius substitute must produce
multiplicity that grows with the scale; no balanced factorial ratio does.
-/

open Finset Nat

namespace GaloisForLFunctions.ArithmeticGaugeTheory

/-- **Legendre above the square root.** For `m < p²` only the first term of Legendre's formula
survives: `v_p(m!) = ⌊m/p⌋`. -/
theorem padicValNat_factorial_of_lt_sq {p m : ℕ} [hp : Fact p.Prime] (h : m < p ^ 2) :
    padicValNat p (m !) = m / p := by
  have hlog : Nat.log p m < 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Nat.log_lt_of_lt_pow hm.ne' h
  rw [padicValNat_factorial hlog, Nat.Ico_succ_singleton, sum_singleton, pow_one]

/-- The sum of floors is at most the floor of the sum. -/
theorem sum_div_le_div_sum {κ : Type*} (T : Finset κ) (c : κ → ℕ) {p : ℕ} (hp : 0 < p) :
    ∑ j ∈ T, c j / p ≤ (∑ j ∈ T, c j) / p := by
  rw [Nat.le_div_iff_mul_le hp, sum_mul]
  exact sum_le_sum fun j _ => Nat.div_mul_le_self (c j) p

/-- The floor of a sum exceeds the sum of floors by at most the number of terms minus one. -/
theorem div_sum_le_sum_div_add {κ : Type*} (T : Finset κ) (hT : T.Nonempty) (c : κ → ℕ) {p : ℕ}
    (hp : 0 < p) : (∑ j ∈ T, c j) / p ≤ ∑ j ∈ T, c j / p + (#T - 1) := by
  have hsplit : ∑ j ∈ T, c j = p * ∑ j ∈ T, c j / p + ∑ j ∈ T, c j % p := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => (Nat.div_add_mod (c j) p).symm
  have hrem : (∑ j ∈ T, c j % p) / p ≤ #T - 1 := by
    have hlt : ∑ j ∈ T, c j % p < #T * p := by
      calc ∑ j ∈ T, c j % p < ∑ _j ∈ T, p := sum_lt_sum_of_nonempty hT fun j _ => Nat.mod_lt _ hp
        _ = #T * p := by rw [sum_const, smul_eq_mul]
    have hcard : 0 < #T := card_pos.mpr hT
    have := (Nat.div_lt_iff_lt_mul hp).mpr hlt
    omega
  rw [hsplit, Nat.mul_add_div hp]
  omega

/-- **Bounded multiplicity of balanced factorial products.** If `Σ a_i = Σ b_j` and every `a_i n`,
`b_j n` is below `p²`, then `Σ_i v_p((a_i n)!) ≤ Σ_j v_p((b_j n)!) + (#T − 1)`. -/
theorem sum_padicValNat_factorial_le {ι κ : Type*} (S : Finset ι) (T : Finset κ) (a : ι → ℕ)
    (b : κ → ℕ) (hbal : ∑ i ∈ S, a i = ∑ j ∈ T, b j) (hT : T.Nonempty) (p n : ℕ)
    [hp : Fact p.Prime] (ha : ∀ i ∈ S, a i * n < p ^ 2) (hb : ∀ j ∈ T, b j * n < p ^ 2) :
    ∑ i ∈ S, padicValNat p ((a i * n) !) ≤ ∑ j ∈ T, padicValNat p ((b j * n) !) + (#T - 1) := by
  have hp0 : 0 < p := hp.out.pos
  rw [sum_congr rfl fun i hi => padicValNat_factorial_of_lt_sq (ha i hi),
    sum_congr rfl fun j hj => padicValNat_factorial_of_lt_sq (hb j hj)]
  calc ∑ i ∈ S, a i * n / p ≤ (∑ i ∈ S, a i * n) / p := sum_div_le_div_sum S _ hp0
    _ = (∑ j ∈ T, b j * n) / p := by rw [← sum_mul, hbal, sum_mul]
    _ ≤ ∑ j ∈ T, b j * n / p + (#T - 1) := div_sum_le_sum_div_add T hT _ hp0

/-- The `p`-adic valuation of a finite product of factorials. -/
theorem padicValNat_prod_factorial {ι : Type*} (S : Finset ι) (m : ι → ℕ) (p : ℕ)
    [Fact p.Prime] : padicValNat p (∏ i ∈ S, (m i) !) = ∑ i ∈ S, padicValNat p ((m i) !) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [prod_insert hi, sum_insert hi, padicValNat.mul (factorial_ne_zero _)
      (prod_ne_zero_iff.mpr fun j _ => factorial_ne_zero _), ih]

/-- **Bounded multiplicity of a factorial-ratio producer.** If `A ∏_j (b_j n)! = ∏_i (a_i n)!` with
`Σ a_i = Σ b_j`, then `v_p(A) ≤ #T − 1` for every prime `p` with `p² > a_i n, b_j n`. -/
theorem padicValNat_le_of_factorialRatio {ι κ : Type*} (S : Finset ι) (T : Finset κ) (a : ι → ℕ)
    (b : κ → ℕ) (hbal : ∑ i ∈ S, a i = ∑ j ∈ T, b j) (hT : T.Nonempty) {A n p : ℕ}
    [Fact p.Prime] (hA : A * ∏ j ∈ T, (b j * n) ! = ∏ i ∈ S, (a i * n) !)
    (ha : ∀ i ∈ S, a i * n < p ^ 2) (hb : ∀ j ∈ T, b j * n < p ^ 2) :
    padicValNat p A ≤ #T - 1 := by
  have hden : ∏ j ∈ T, (b j * n) ! ≠ 0 := prod_ne_zero_iff.mpr fun j _ => factorial_ne_zero _
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hA
    exact (prod_ne_zero_iff.mpr fun i _ => factorial_ne_zero _) hA.symm
  have hval := congrArg (padicValNat p) hA
  rw [padicValNat.mul hA0 hden, padicValNat_prod_factorial, padicValNat_prod_factorial] at hval
  have := sum_padicValNat_factorial_le S T a b hbal hT p n ha hb
  omega

/-- **The central binomial coefficient** has multiplicity at most one at every prime above
`√(2n)`. -/
theorem padicValNat_centralBinom_le_one {n p : ℕ} [Fact p.Prime] (h : 2 * n < p ^ 2) :
    padicValNat p (centralBinom n) ≤ 1 := by
  have hA : centralBinom n * ∏ j ∈ (univ : Finset (Fin 2)), (1 * n) ! =
      ∏ i ∈ (univ : Finset (Fin 1)), (2 * n) ! := by
    simp only [one_mul, prod_const, card_univ, Fintype.card_fin, pow_one]
    rw [sq, ← mul_assoc, centralBinom_eq_two_mul_choose]
    have h := choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
    rwa [show 2 * n - n = n by omega] at h
  have := padicValNat_le_of_factorialRatio (univ : Finset (Fin 1)) (univ : Finset (Fin 2))
    (fun _ => 2) (fun _ => 1) (by simp) univ_nonempty hA (fun _ _ => h)
    (fun _ _ => by omega)
  simpa using this

end GaloisForLFunctions.ArithmeticGaugeTheory
