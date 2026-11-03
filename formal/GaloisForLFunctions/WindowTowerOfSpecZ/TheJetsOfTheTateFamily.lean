import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFamilyIsAnExponentialOfPointCounts

/-!
# The jets of the Tate family at dimension zero

`J_k(n) = Σ_{d∣n} μ(n/d) d^k` is a finite sum of exponentials `e^{k log d}`. Its jets at dimension zero
are the **generalized von Mangoldt functions** `Λ_j = log^j * μ` (Bombieri, Selberg):

* **The jet tower** (`hasDerivAt_tateJet`, `tateJet_zero_dim`): the functions
  `k ↦ Σ_{d∣n} μ(n/d)(log d)^j d^k` differentiate into each other, start at `J_k(n)` and take the value
  `Λ_j(n)` at `k = 0`. So `Λ_j(n)` is the `j`-th derivative of the Tate family at dimension zero:
  `Λ_0 = [n = 1]`, `Λ_1 = Λ` (Weil's arithmetic term), `Λ_2 = Λ log + Λ * Λ` (Selberg's function).
* **Exponential generating function** (`hasSum_tateJet`): `J_k(n) = Σ_j k^j Λ_j(n)/j!` for every
  real `k`: the Tate family is the exponential generating function of the generalized von Mangoldt
  functions.
* **Bombieri's recursion** (`genVonMangoldt_succ`): `Λ_{j+1} = Λ_j·log + Λ * Λ_j`, from the degree
  derivation (`D μ = −Λ * μ`).
* **Positivity and support** (`genVonMangoldt_nonneg`, `genVonMangoldt_eq_zero_of_lt`): `Λ_j ≥ 0`, and
  `Λ_j(n) = 0` when `n` has more than `j` distinct prime factors. The `j`-th jet of the Tate family at
  dimension zero sees only the integers with at most `j` distinct primes.

On a window, `τ_H(k) = Σ_j (k^j/j!)⟨ρ_A(Λ_j)H, H⟩`: Weil's arithmetic term is the first Taylor
coefficient of the Tate function, Selberg's symmetry function the second, and all coefficients are
nonnegative arithmetic functions (the higher tangent principles for nonnegative tests).
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory
open scoped ArithmeticFunction.omega

/-! ### Generalized von Mangoldt functions -/

/-- `log^j` as an arithmetic function. -/
def logPow (j : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else Real.log n ^ j, by simp⟩

theorem logPow_apply {j n : ℕ} (hn : n ≠ 0) : logPow j n = Real.log n ^ j := by
  simp [logPow, hn]

/-- The **generalized von Mangoldt function** `Λ_j = log^j * μ`. -/
def genVonMangoldt (j : ℕ) : ArithmeticFunction ℝ :=
  logPow j * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

theorem logPow_zero : logPow 0 = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logPow]
  · rw [logPow_apply hn.ne', pow_zero, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hn.ne', Nat.cast_one]

theorem degD_logPow (j : ℕ) : degD (logPow j) = logPow (j + 1) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logPow]
  · rw [degD_apply, logPow_apply hn.ne', logPow_apply hn.ne', pow_succ]

theorem genVonMangoldt_zero : genVonMangoldt 0 = 1 := by
  rw [genVonMangoldt, logPow_zero, ArithmeticFunction.coe_zeta_mul_coe_moebius]

theorem logPow_one : logPow 1 = ArithmeticFunction.log := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logPow]
  · rw [logPow_apply hn.ne', pow_one, ArithmeticFunction.log_apply]

theorem genVonMangoldt_one : genVonMangoldt 1 = ArithmeticFunction.vonMangoldt := by
  rw [genVonMangoldt, logPow_one, ← ArithmeticFunction.vonMangoldt_mul_zeta, mul_assoc,
    ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

/-- **Bombieri's recursion** `Λ_{j+1} = Λ_j·log + Λ * Λ_j`. -/
theorem genVonMangoldt_succ (j : ℕ) :
    genVonMangoldt (j + 1) =
      degD (genVonMangoldt j) + ArithmeticFunction.vonMangoldt * genVonMangoldt j := by
  rw [genVonMangoldt, genVonMangoldt, degD_mul, degD_logPow, degD_moebius]
  ring

/-- **Selberg's function is the second jet**: `Λ_2 = Λ log + Λ * Λ`. -/
theorem genVonMangoldt_two :
    genVonMangoldt 2 = degD ArithmeticFunction.vonMangoldt +
      ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt := by
  rw [genVonMangoldt_succ, genVonMangoldt_one]

theorem genVonMangoldt_nonneg (j n : ℕ) : 0 ≤ genVonMangoldt j n := by
  induction j generalizing n with
  | zero =>
    rw [genVonMangoldt_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ j ih =>
    rw [genVonMangoldt_succ, ArithmeticFunction.add_apply, degD_apply, ArithmeticFunction.mul_apply]
    refine add_nonneg (mul_nonneg (ih n) (Real.log_natCast_nonneg n)) ?_
    exact Finset.sum_nonneg fun x _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (ih _)

theorem cardDistinctFactors_eq_card (n : ℕ) : ArithmeticFunction.cardDistinctFactors n =
    n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]; rfl

/-- **The `j`-th jet sees at most `j` distinct primes**: `Λ_j(n) = 0` if `ω(n) > j`. -/
theorem genVonMangoldt_eq_zero_of_lt {j n : ℕ} (h : j < ArithmeticFunction.cardDistinctFactors n) :
    genVonMangoldt j n = 0 := by
  induction j generalizing n with
  | zero =>
    have h1 : 1 < n := ArithmeticFunction.cardDistinctFactors_pos.mp h
    rw [genVonMangoldt_zero, ArithmeticFunction.one_apply, if_neg (by omega)]
  | succ j ih =>
    rw [genVonMangoldt_succ, ArithmeticFunction.add_apply, degD_apply, ih (by omega), zero_mul,
      zero_add, ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    by_cases hΛ : ArithmeticFunction.vonMangoldt x.1 = 0
    · rw [hΛ, zero_mul]
    obtain ⟨p, e, hp, he, hpe⟩ := (isPrimePow_nat_iff x.1).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hx2 : x.2 ≠ 0 := fun h0 => hn0 (by rw [← hxn, h0, mul_zero])
    -- `ω(n) ≤ 1 + ω(n / p^e)`
    have hcard : ArithmeticFunction.cardDistinctFactors n ≤
        1 + ArithmeticFunction.cardDistinctFactors x.2 := by
      rw [cardDistinctFactors_eq_card, cardDistinctFactors_eq_card, ← hxn,
        Nat.primeFactors_mul (by rw [← hpe]; exact pow_ne_zero _ hp.ne_zero) hx2, ← hpe,
        Nat.primeFactors_prime_pow he.ne' hp]
      exact (Finset.card_union_le _ _).trans (by rw [Finset.card_singleton])
    rw [ih (by omega), mul_zero]

/-! ### The jet tower of the Tate family -/

/-- The `j`-th jet function `k ↦ Σ_{d∣n} (log d)^j d^k μ(n/d)`. -/
def tateJet (j n : ℕ) (k : ℝ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, Real.log x.1 ^ j * (x.1 : ℝ) ^ k *
    (ArithmeticFunction.moebius x.2 : ℝ)

theorem tateJet_zero (n : ℕ) (k : ℝ) : tateJet 0 n k = jordanTotient k n := by
  rw [← jordanFun_apply, jordanFun_eq, ArithmeticFunction.mul_apply, tateJet]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : x.1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))
  rw [tateTwist_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hx1,
    neg_neg, pow_zero, one_mul, Nat.cast_one, one_mul, ArithmeticFunction.intCoe_apply]

/-- **The jets differentiate into each other.** -/
theorem hasDerivAt_tateJet (j n : ℕ) (k : ℝ) :
    HasDerivAt (tateJet j n) (tateJet (j + 1) n k) k := by
  unfold tateJet
  refine HasDerivAt.fun_sum fun x hx => ?_
  have hx1 : (0 : ℝ) < x.1 := by
    exact_mod_cast Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  exact (((Real.hasStrictDerivAt_const_rpow hx1 k).hasDerivAt.const_mul
    (Real.log x.1 ^ j)).mul_const (ArithmeticFunction.moebius x.2 : ℝ)).congr_deriv (by ring)

/-- **The `j`-th jet at dimension zero is `Λ_j`.** -/
theorem tateJet_zero_dim (j n : ℕ) : tateJet j n 0 = genVonMangoldt j n := by
  rw [tateJet, genVonMangoldt, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : x.1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))
  rw [Real.rpow_zero, mul_one, logPow_apply hx1, ArithmeticFunction.intCoe_apply]

/-- **The Tate family is the exponential generating function of the generalized von Mangoldt
functions**: `J_k(n) = Σ_j k^j Λ_j(n)/j!`. -/
theorem hasSum_tateJet (n : ℕ) (k : ℝ) :
    HasSum (fun j : ℕ => k ^ j * genVonMangoldt j n / j.factorial) (jordanTotient k n) := by
  rw [← tateJet_zero]
  simp_rw [← tateJet_zero_dim, tateJet, Finset.mul_sum, Finset.sum_div]
  refine hasSum_sum fun x hx => ?_
  have hx1 : (0 : ℝ) < x.1 := by
    exact_mod_cast Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
  have he := NormedSpace.expSeries_div_hasSum_exp (k * Real.log x.1)
  rw [← Real.exp_eq_exp_ℝ, mul_comm k, ← Real.rpow_def_of_pos hx1] at he
  have := (he.mul_right (ArithmeticFunction.moebius x.2 : ℝ))
  have hf : (fun j : ℕ => k ^ j * (Real.log x.1 ^ j * (x.1 : ℝ) ^ (0 : ℝ) *
      (ArithmeticFunction.moebius x.2 : ℝ)) / j.factorial) =
      fun i : ℕ => (Real.log x.1 * k) ^ i / i.factorial * (ArithmeticFunction.moebius x.2 : ℝ) := by
    funext j
    rw [Real.rpow_zero, mul_one, mul_pow]
    ring
  have hv : Real.log x.1 ^ 0 * (x.1 : ℝ) ^ k * (ArithmeticFunction.moebius x.2 : ℝ) =
      (x.1 : ℝ) ^ k * (ArithmeticFunction.moebius x.2 : ℝ) := by rw [pow_zero, one_mul]
  rw [hf, hv]
  exact this

end GaloisForLFunctions.WindowTowerOfSpecZ
