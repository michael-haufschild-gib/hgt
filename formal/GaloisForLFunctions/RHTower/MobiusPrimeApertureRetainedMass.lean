import GaloisForLFunctions.RHTower.InfiniteMobiusSignedChannel
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The finite-prime retained mass of the normalized Möbius channel

`mobius-prime-aperture-differential-order-profile.md`, equations `(4)` and `(5)`.

The squarefree Dirichlet weight `mass_sigma(n) = mu(n)^(2 : ℕ) n^(-sigma)` is multiplicative with
`sum_e mass(p^e) = 1 + p^(-sigma)`.  Euler's product over a finite prime aperture therefore computes
exactly the channel mass carried by the `N`-smooth divisors:

```text
sum_{m N-smooth} mass_sigma(m) = prod_{p < N} (1 + p^(-sigma)) ,
M_omega(N) = prod_{p < N}(1 + p^(-sigma)) / Z_sigma ,
log M_omega(N) = - sum_{p >= N} log(1 + p^(-sigma)) .
```
-/

open Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

/-! ### The squarefree weight is a multiplicative Euler datum -/

theorem squarefreeMobiusMass_one (sigma : ℝ) : squarefreeMobiusMass sigma 1 = 1 := by
  rw [squarefreeMobiusMass, if_pos squarefree_one]
  norm_num

theorem squarefreeMobiusMass_zero (sigma : ℝ) : squarefreeMobiusMass sigma 0 = 0 := by
  rw [squarefreeMobiusMass, if_neg not_squarefree_zero]

theorem squarefreeMobiusMass_mul_of_coprime (sigma : ℝ) {m n : ℕ} (h : m.Coprime n) :
    squarefreeMobiusMass sigma (m * n) =
      squarefreeMobiusMass sigma m * squarefreeMobiusMass sigma n := by
  by_cases hsq : Squarefree (m * n)
  · obtain ⟨hm, hn⟩ := (Nat.squarefree_mul h).mp hsq
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at hm
      exact not_squarefree_zero hm
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0] at hn
      exact not_squarefree_zero hn
    have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hnr : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [squarefreeMobiusMass, if_pos hsq, squarefreeMobiusMass, if_pos hm,
      squarefreeMobiusMass, if_pos hn, Nat.cast_mul, Real.mul_rpow hmr hnr]
  · have hnot : ¬(Squarefree m ∧ Squarefree n) := fun hc => hsq ((Nat.squarefree_mul h).mpr hc)
    simp only [squarefreeMobiusMass]
    rw [if_neg hsq]
    rcases not_and_or.mp hnot with hm | hn
    · rw [if_neg hm, zero_mul]
    · rw [if_neg hn, mul_zero]

/-- Only the exponents `0` and `1` contribute at a prime. -/
theorem squarefreeMobiusMass_prime_pow_eq_zero {sigma : ℝ} {p : ℕ} (hp : p.Prime) {e : ℕ}
    (he : 2 ≤ e) : squarefreeMobiusMass sigma (p ^ e) = 0 := by
  have hnsq : ¬ Squarefree (p ^ e) := by
    intro hsq
    have hdvd : p * p ∣ p ^ e := by
      have h2 : p ^ 2 ∣ p ^ e := pow_dvd_pow p he
      rwa [pow_two] at h2
    exact hp.not_isUnit (hsq p hdvd)
  simp only [squarefreeMobiusMass, if_neg hnsq]

theorem tsum_squarefreeMobiusMass_prime_pow (sigma : ℝ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, squarefreeMobiusMass sigma (p ^ e)) = 1 + (p : ℝ) ^ (-sigma) := by
  have hsupp : ∀ e ∉ ({0, 1} : Finset ℕ), squarefreeMobiusMass sigma (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    exact squarefreeMobiusMass_prime_pow_eq_zero hp (by omega)
  rw [tsum_eq_sum hsupp]
  have h0 : squarefreeMobiusMass sigma (p ^ 0) = 1 := by
    rw [pow_zero]
    exact squarefreeMobiusMass_one sigma
  have h1 : squarefreeMobiusMass sigma (p ^ 1) = (p : ℝ) ^ (-sigma) := by
    rw [pow_one, squarefreeMobiusMass, if_pos hp.squarefree]
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton, h0, h1]

/-! ### Euler's finite aperture product -/

/-- **Card `(5)`.**  The squarefree channel mass carried by the `N`-smooth divisors is the finite
Euler product over the primes below `N`. -/
theorem prod_primesBelow_eq_tsum_smoothNumbers {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) :
    (∏ p ∈ N.primesBelow, (1 + (p : ℝ) ^ (-sigma)))
      = ∑' m : N.smoothNumbers, squarefreeMobiusMass sigma (m : ℕ) := by
  have hnorm : Summable (fun n : ℕ => ‖squarefreeMobiusMass sigma n‖) := by
    refine (summable_squarefreeMobiusMass hsigma).congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (squarefreeMobiusMass_nonneg sigma n)]
  have heuler := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := squarefreeMobiusMass sigma) (squarefreeMobiusMass_one sigma)
    (fun {m n} h => squarefreeMobiusMass_mul_of_coprime sigma h) hnorm N
  rw [← heuler]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact (tsum_squarefreeMobiusMass_prime_pow sigma (Nat.mem_primesBelow.mp hp).2).symm

/-- **The cofinal Euler product.**  The squarefree partition is the infinite Euler product. -/
theorem hasProd_squarefreeEuler {sigma : ℝ} (hsigma : 1 < sigma) :
    HasProd (fun p : Nat.Primes => 1 + ((p : ℕ) : ℝ) ^ (-sigma)) (squarefreeMobiusTotal sigma) := by
  have hnorm : Summable (fun n : ℕ => ‖squarefreeMobiusMass sigma n‖) := by
    refine (summable_squarefreeMobiusMass hsigma).congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (squarefreeMobiusMass_nonneg sigma n)]
  have heuler := EulerProduct.eulerProduct_hasProd
    (f := squarefreeMobiusMass sigma) (squarefreeMobiusMass_one sigma)
    (fun {m n} h => squarefreeMobiusMass_mul_of_coprime sigma h) hnorm
    (squarefreeMobiusMass_zero sigma)
  have hcongr : (fun p : Nat.Primes => ∑' e : ℕ, squarefreeMobiusMass sigma ((p : ℕ) ^ e))
      = fun p : Nat.Primes => 1 + ((p : ℕ) : ℝ) ^ (-sigma) := by
    funext p
    exact tsum_squarefreeMobiusMass_prime_pow sigma p.2
  rw [hcongr] at heuler
  exact heuler

/-! ### The logarithmic form -/

theorem summable_prime_rpow {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-sigma)) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-sigma)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact hbase.comp_injective Nat.Primes.coe_nat_injective

theorem log_one_add_prime_rpow_nonneg (sigma : ℝ) (p : Nat.Primes) :
    0 ≤ Real.log (1 + ((p : ℕ) : ℝ) ^ (-sigma)) := by
  refine Real.log_nonneg ?_
  have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-sigma) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  linarith

theorem summable_log_one_add_prime_rpow {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun p : Nat.Primes => Real.log (1 + ((p : ℕ) : ℝ) ^ (-sigma))) := by
  refine Summable.of_nonneg_of_le (log_one_add_prime_rpow_nonneg sigma) (fun p => ?_)
    (summable_prime_rpow hsigma)
  have hx : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := Real.add_one_le_exp (((p : ℕ) : ℝ) ^ (-sigma))
  have hpos : (0 : ℝ) < 1 + ((p : ℕ) : ℝ) ^ (-sigma) := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **The cofinal logarithmic Euler sum.** -/
theorem tsum_log_one_add_prime_rpow {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' p : Nat.Primes, Real.log (1 + ((p : ℕ) : ℝ) ^ (-sigma)))
      = Real.log (squarefreeMobiusTotal sigma) := by
  have hpos : ∀ p : Nat.Primes, (0 : ℝ) < 1 + ((p : ℕ) : ℝ) ^ (-sigma) := by
    intro p
    have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hsum := summable_log_one_add_prime_rpow hsigma
  have hprod := Real.hasProd_of_hasSum_log hpos hsum.hasSum
  have huniq := hprod.unique (hasProd_squarefreeEuler hsigma)
  have hZ : 0 < squarefreeMobiusTotal sigma := squarefreeMobiusTotal_pos hsigma
  rw [← huniq, Real.log_exp]

end RHTower
