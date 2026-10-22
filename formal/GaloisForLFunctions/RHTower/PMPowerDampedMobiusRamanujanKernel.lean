import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanTransfer

/-!
# Closed form of the Ramanujan transfer kernel

For `ε > 0` the Ramanujan column `k_m(d) = d μ(m) w_ε(dm)` factors as
`μ(m) w_ε(m) · d^(−ε) · μ_{g_m}(d)`, where `μ_g(d) = μ(d) ∏_{p|d} g(p)` is the damped Möbius
function of the prime correction `g_m(p) = 0` for `p | m` and `g_m(p) = p^(1+ε)/(p^(1+ε) − 1)`
otherwise. Convolving with `n ↦ n^(−ε)` then gives the transfer kernel in closed form:
`T_m(n) = |w_ε(m)| n^(−ε) ∏_{p|n} (1 if p | m, else −1/(p^(1+ε) − 1))`, and
`|T_m(n)| = |w_ε(m)| n^(−ε) ∏_{p|n, p∤m} 1/(p^(1+ε) − 1)`. The absolute prime product lies in
`[0, 1]` because `p^(1+ε) − 1 > 1` for every prime `p`.

## Main results

- `pmPowerDampedRamanujanColumn_eq_dampedMobius`: `k_m(d) = μ(m) w_ε(m) d^(−ε) μ_{g_m}(d)`.
- `pmPowerDampedRamanujanTransfer_eq_divisorSum`: `T_m(n) = |w_ε(m)| n^(−ε) ∏_{p|n} (1 − g_m(p))`.
- `pmPowerDampedRamanujanTransfer_eq_prod`: the explicit prime-product form of `T_m(n)` for `n ≠ 0`.
- `norm_pmPowerDampedRamanujanTransfer`: `|T_m(n)| = |w_ε(m)| n^(−ε) ∏_{p|n} (1 if p | m, else 1/(p^(1+ε) − 1))`.
- `pmPowerDampedRamanujanAbsProduct_nonneg`, `pmPowerDampedRamanujanAbsProduct_le_one`: the absolute prime product is in `[0,1]`.

## Hypotheses

All results are unconditional; they assume `0 < ε` (and primality of the indexing primes,
`n ≠ 0`, where stated).
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The prime correction `g_m(p) = 0` if `p | m`, else `p^(1+ε)/(p^(1+ε) − 1)`. -/
def pmPowerDampedRamanujanPrimeCorrection (ε : ℝ) (m p : ℕ) : ℝ :=
  if p ∣ m then 0 else (p : ℝ)^(1+ε)/((p : ℝ)^(1+ε)-1)

/-- For prime `p`, `μ_f(pq) = 0` if `p | q`, else `−f(p) μ_f(q)`. -/
theorem pm_dampedMobius_prime_mul (f : ℕ → ℝ) {p q : ℕ} (hp : p.Prime) :
    DampedMobius.dampedMobius f (p*q) =
      if p ∣ q then 0 else -f p*DampedMobius.dampedMobius f q := by
  by_cases hpq : p ∣ q
  · have hns : ¬Squarefree (p*q) := fun hs =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hpq
    simp [hpq, DampedMobius.dampedMobius, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.intCoe_apply, moebius_eq_zero_of_not_squarefree hns]
  · have hprime : DampedMobius.dampedMobius f p = -f p := by
      simpa using DampedMobius.dampedMobius_apply_prime_pow f (k := 1) hp
    rw [if_neg hpq, (DampedMobius.isMultiplicative_dampedMobius f).map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr hpq), hprime]

/-- For `ε > 0` and prime `p`: `k_m(pq) = 0` if `p | qm`, else `−p/(p^(1+ε) − 1) · k_m(q)`. -/
theorem pmPowerDampedRamanujanColumn_prime_mul {ε : ℝ} (hε : 0 < ε)
    {p q : ℕ} (hp : p.Prime) (m : ℕ) :
    pmPowerDampedRamanujanColumn ε m (p*q) =
      if p ∣ q*m then 0 else
        -((p : ℂ)/(((p : ℝ)^(1+ε)-1 : ℝ) : ℂ))*pmPowerDampedRamanujanColumn ε m q := by
  by_cases hdiv : p ∣ q*m
  · have hns : ¬Squarefree (p*(q*m)) := fun hs =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hdiv
    simp only [pmPowerDampedRamanujanColumn, ArithmeticFunction.coe_mk, Nat.mul_assoc,
      pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hns, mul_zero, if_pos hdiv]
  · simp only [pmPowerDampedRamanujanColumn, ArithmeticFunction.coe_mk,
      Nat.mul_assoc, pmPowerDampedRamanujanWeight_prime_mul hε hp hdiv, if_neg hdiv,
      Nat.cast_mul]
    ring

/-- For prime `p ∤ m`, `p^(−ε) g_m(p) = p/(p^(1+ε) − 1)`. -/
theorem pmPowerDampedRamanujanPrimeCorrection_balance (ε : ℝ) {p m : ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m) :
    (p : ℝ)^(-ε)*pmPowerDampedRamanujanPrimeCorrection ε m p =
      (p : ℝ)/((p : ℝ)^(1+ε)-1) := by
  rw [pmPowerDampedRamanujanPrimeCorrection, if_neg hpm, ← mul_div_assoc,
    ← Real.rpow_add (by exact_mod_cast hp.pos)]
  rw [show -ε+(1+ε) = (1 : ℝ) by ring, Real.rpow_one]

/-- For `ε > 0`, the column factors as `k_m(d) = μ(m) w_ε(m) · d^(−ε) μ_{g_m}(d)`. -/
theorem pmPowerDampedRamanujanColumn_eq_dampedMobius {ε : ℝ} (hε : 0 < ε)
    (m d : ℕ) :
    pmPowerDampedRamanujanColumn ε m d =
      ((moebius m : ℂ)*pmPowerDampedRamanujanWeight ε m) *
        (((d : ℝ)^(-ε)*DampedMobius.dampedMobius
          (pmPowerDampedRamanujanPrimeCorrection ε m) d : ℝ) : ℂ) := by
  let f := pmPowerDampedRamanujanPrimeCorrection ε m
  induction d using induction_on_primes with
  | zero => simp
  | one =>
    simp only [pmPowerDampedRamanujanColumn, ArithmeticFunction.coe_mk, Nat.cast_one,
      one_mul, Real.one_rpow, (DampedMobius.isMultiplicative_dampedMobius _).map_one,
      Complex.ofReal_one, mul_one]
  | prime_mul p q hp ih =>
    rw [pmPowerDampedRamanujanColumn_prime_mul hε hp, pm_dampedMobius_prime_mul _ hp]
    by_cases hpq : p ∣ q
    · have hdiv : p ∣ q*m := dvd_mul_of_dvd_left hpq m
      simp [if_pos hdiv, if_pos hpq]
    by_cases hpm : p ∣ m
    · have hdiv : p ∣ q*m := dvd_mul_of_dvd_right hpm q
      simp [if_pos hdiv, pmPowerDampedRamanujanPrimeCorrection, hpm]
    have hdiv : ¬p ∣ q*m := fun h => (hp.dvd_mul.mp h).elim hpq hpm
    rw [if_neg hdiv, if_neg hpq, ih]
    have hw := congrArg (fun y : ℝ => (y : ℂ))
      (pmPowerDampedRamanujanPrimeCorrection_balance ε hp hpm)
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] at hw
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q),
      Complex.ofReal_mul, Complex.ofReal_neg]
    linear_combination ((moebius m : ℂ)*pmPowerDampedRamanujanWeight ε m)*
      (((q : ℝ)^(-ε) : ℝ) : ℂ)*
      ((DampedMobius.dampedMobius (pmPowerDampedRamanujanPrimeCorrection ε m) q : ℝ) : ℂ)*hw

/-- `∑_{d|n} μ_f(d) = ∏_{p|n} (1 − f(p))`. -/
theorem pm_dampedMobius_antidiagonal_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, DampedMobius.dampedMobius f x.2) =
      DampedMobius.divisorSum f n := by
  rw [Nat.sum_divisorsAntidiagonal (fun _ b => DampedMobius.dampedMobius f b),
    Nat.sum_div_divisors (f := fun b => DampedMobius.dampedMobius f b)]
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n) (DampedMobius.dampedMobius_mul_zeta f)
  simpa only [ArithmeticFunction.coe_mul_zeta_apply] using h

/-- For `ε > 0`, `T_m(n) = |w_ε(m)| n^(−ε) ∏_{p|n} (1 − g_m(p))`. -/
theorem pmPowerDampedRamanujanTransfer_eq_divisorSum {ε : ℝ} (hε : 0 < ε) (m n : ℕ) :
    pmPowerDampedRamanujanTransfer ε m n =
      (‖pmPowerDampedRamanujanWeight ε m‖ : ℂ) *
        (((n : ℝ)^(-ε)*DampedMobius.divisorSum
          (pmPowerDampedRamanujanPrimeCorrection ε m) n : ℝ) : ℂ) := by
  have hc : (moebius m : ℂ)*pmPowerDampedRamanujanWeight ε m =
      (‖pmPowerDampedRamanujanWeight ε m‖ : ℂ) := by
    simpa using pmPowerDampedRamanujanWeight_mobius_pair hε 1 m
  by_cases hn : n = 0
  · subst n; simp
  rw [pmPowerDampedRamanujanTransfer, ArithmeticFunction.mul_apply]
  have hterm (x : ℕ × ℕ) (hx : x ∈ n.divisorsAntidiagonal) :
      pmPowerDampedUnitAF ε x.1 * pmPowerDampedRamanujanColumn ε m x.2 =
      (‖pmPowerDampedRamanujanWeight ε m‖ : ℂ) *
        (((n : ℝ)^(-ε) : ℝ) : ℂ) *
        ((DampedMobius.dampedMobius (pmPowerDampedRamanujanPrimeCorrection ε m) x.2 : ℝ) : ℂ) := by
    have hm := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx0 : x.1 ≠ 0 := by intro hz; simp only [hz, zero_mul] at hm; exact hn hm.symm
    have hw := congrArg (fun y : ℝ => (y : ℂ)) ((pmNaturalRpowHom ε).map_mul x.1 x.2)
    change ((((x.1*x.2 : ℕ) : ℝ)^(-ε) : ℝ) : ℂ) =
      (((x.1 : ℝ)^(-ε)*(x.2 : ℝ)^(-ε) : ℝ) : ℂ) at hw
    rw [hm, Complex.ofReal_mul] at hw
    rw [pmPowerDampedRamanujanColumn_eq_dampedMobius hε, hc]
    simp only [pmPowerDampedUnitAF, ArithmeticFunction.coe_mk, if_neg hx0, Complex.ofReal_mul]
    rw [hw]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Complex.ofReal_sum,
    pm_dampedMobius_antidiagonal_sum, Complex.ofReal_mul]
  ring

/-- For `ε > 0` and prime `p`, `1 − g_m(p) = 1` if `p | m`, else `−1/(p^(1+ε) − 1)`. -/
theorem pmPowerDampedRamanujanPrimeCorrection_complement {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) {p : ℕ} (hp : p.Prime) :
    1-pmPowerDampedRamanujanPrimeCorrection ε m p =
      if p ∣ m then 1 else -1/((p : ℝ)^(1+ε)-1) := by
  unfold pmPowerDampedRamanujanPrimeCorrection
  split_ifs
  · ring
  · have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hd : (p : ℝ)^(1+ε)-1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hpR (by linarith)))
    field_simp
    ring

/-- For `ε > 0` and `n ≠ 0`,
`T_m(n) = |w_ε(m)| n^(−ε) ∏_{p|n} (1 if p | m, else −1/(p^(1+ε) − 1))`. -/
theorem pmPowerDampedRamanujanTransfer_eq_prod {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    pmPowerDampedRamanujanTransfer ε m n =
      (‖pmPowerDampedRamanujanWeight ε m‖ : ℂ) *
        (((n : ℝ)^(-ε)*(∏ p ∈ n.primeFactors,
          if p ∣ m then 1 else -1/((p : ℝ)^(1+ε)-1)) : ℝ) : ℂ) := by
  rw [pmPowerDampedRamanujanTransfer_eq_divisorSum hε,
    DampedMobius.divisorSum, ArithmeticFunction.prodPrimeFactors_apply hn]
  congr 3
  apply Finset.prod_congr rfl
  intro p hp
  exact pmPowerDampedRamanujanPrimeCorrection_complement hε m (Nat.prime_of_mem_primeFactors hp)

/-- The absolute prime product `∏_{p∈S} (1 if p | m, else 1/(p^(1+ε) − 1))`. -/
def pmPowerDampedRamanujanAbsProduct (ε : ℝ) (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ S, if p ∣ m then 1 else 1/((p : ℝ)^(1+ε)-1)

/-- For `ε > 0` and prime `p`, `p^(1+ε) − 1 > 1`. -/
theorem pmPowerDampedRamanujan_prime_denominator_one_lt {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) : 1 < (p : ℝ)^(1+ε)-1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hexp := Real.one_lt_rpow hp1 hε
  rw [Real.rpow_add (by linarith : (0 : ℝ) < p), Real.rpow_one]
  nlinarith

/-- For `ε > 0` and a set of primes `S`, the absolute prime product is nonnegative. -/
theorem pmPowerDampedRamanujanAbsProduct_nonneg {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    0 ≤ pmPowerDampedRamanujanAbsProduct ε S m := by
  apply Finset.prod_nonneg
  intro p hp
  split_ifs
  · norm_num
  · exact div_nonneg (by norm_num) (le_trans (by norm_num)
      (pmPowerDampedRamanujan_prime_denominator_one_lt hε (hS p hp)).le)

/-- For `ε > 0` and a set of primes `S`, the absolute prime product is at most `1`. -/
theorem pmPowerDampedRamanujanAbsProduct_le_one {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (m : ℕ) :
    pmPowerDampedRamanujanAbsProduct ε S m ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    split_ifs
    · norm_num
    · exact div_nonneg (by norm_num) (le_trans (by norm_num)
        (pmPowerDampedRamanujan_prime_denominator_one_lt hε (hS p hp)).le)
  · intro p hp
    split_ifs
    · rfl
    · have hd := pmPowerDampedRamanujan_prime_denominator_one_lt hε (hS p hp)
      exact (div_le_one (by linarith)).mpr hd.le

/-- For `ε > 0` and `n ≠ 0`, `|T_m(n)| = |w_ε(m)| n^(−ε)` times the absolute prime product over
the prime factors of `n`. -/
theorem norm_pmPowerDampedRamanujanTransfer {ε : ℝ} (hε : 0 < ε)
    (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ‖pmPowerDampedRamanujanTransfer ε m n‖ =
      ‖pmPowerDampedRamanujanWeight ε m‖*(n : ℝ)^(-ε)*
        pmPowerDampedRamanujanAbsProduct ε n.primeFactors m := by
  rw [pmPowerDampedRamanujanTransfer_eq_prod hε m hn,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), Finset.abs_prod, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro p hp
  have hd := pmPowerDampedRamanujan_prime_denominator_one_lt hε (Nat.prime_of_mem_primeFactors hp)
  split_ifs
  · norm_num
  · rw [abs_div, abs_neg, abs_one, abs_of_pos (by linarith)]

end RHTower
