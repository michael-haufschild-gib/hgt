import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The frustration of a prime tower is rank one

In the lattice model of the odd Weil form a half-line profile is a finitely supported
`q : ℕ → ℝ` on the integers `n ≥ 1` (positions `log n`).  Its **ratio correlation** at `m` is
`R_q(m) = Σ_a q(a) q(am)` (difference pairs in the log coordinate) and its **product
correlation** is `P_q(m) = Σ_{ab = m} q(a) q(b)` (sum pairs).  The odd extension of a half-line
profile has autocorrelation `2R − P` at every positive lag
(`ArithmeticIncidencePositivity.autoCorr_sub_reflect` in the continuum), so the prime side of the
odd Weil form is `Σ_m Λ(m) m^{−1/2} (2 R_q(m) − P_q(m))` (`latticeOddPrimeSide`): the sum pairs are
the frustrating edges of the ledger, and they are the only ones.

* **Tower locality** (`productCorr_prime_pow`): at a prime power `p^k` the product pairs lie in
  one tower, `P_q(p^k) = Σ_{i ≤ k} q(p^i) q(p^{k−i})`.
* **Rank-one law** (`sum_vonMangoldt_productCorr_prime_pow`): the whole product contribution of
  the tower of `p` is one square,
  `Σ_k Λ(p^k) (p^k)^{−1/2} P_q(p^k) = log p · (S_p(q)² − q(1)²)`, where
  `S_p(q) = Σ_i q(p^i) p^{−i/2}` is the local Mellin value of the profile at `s = ½`.
  The Cauchy product of the tower sequence is read off a polynomial square.
* **Orientation reading** (`sum_vonMangoldt_productCorr_prime_pow_ge`): the frustrating part of a
  tower is bounded below by the pole-like term `−log p · q(1)²`, and is a sum of squares once
  the profile vanishes at `1`; so the odd prime side is at most twice its ratio part
  (`latticeOddPrimeSide_le_of_eq_zero`, over a finite set of towers).

The arithmetic content of the sign of the odd form is therefore the competition between the
difference correlations, which couple every tower to every other, and a sum of independent
rank-one squares, one per prime.
-/

open Finset ArithmeticFunction Polynomial

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### Correlations in the lattice model -/

/-- The ratio (difference-pair) correlation of a profile at `m`, over the support bound `X`. -/
def ratioCorr (q : ℕ → ℝ) (X m : ℕ) : ℝ := ∑ a ∈ Icc 1 X, q a * q (a * m)

/-- The product (sum-pair) correlation of a profile at `m`. -/
def productCorr (q : ℕ → ℝ) (m : ℕ) : ℝ := ∑ d ∈ m.divisors, q d * q (m / d)

/-- The local Mellin value of the tower of `p` at `s = ½`, `S_p(q) = Σ_{i ≤ K} q(p^i) p^{−i/2}`. -/
def towerMellin (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ i ∈ range (K + 1), q (p ^ i) * (p : ℝ) ^ (-(i : ℝ) / 2)

/-- The product (frustrating) part of the tower of `p`, through `p^{2K}`. -/
def towerProductPart (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ k ∈ range (2 * K + 1), Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k)

/-- The prime side of the odd Weil form on the lattice: `Σ_m Λ(m) m^{−1/2} (2R_q(m) − P_q(m))`
over the towers in `S`. -/
def latticeOddPrimeSide (q : ℕ → ℝ) (X : ℕ) (S : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ k ∈ range (2 * K + 1),
    Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * ratioCorr q X (p ^ k) - productCorr q (p ^ k))

/-! ### Tower locality -/

/-- **Tower locality**: the product pairs of a prime power lie in one tower. -/
theorem productCorr_prime_pow (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    productCorr q (p ^ k) = ∑ i ∈ range (k + 1), q (p ^ i) * q (p ^ (k - i)) := by
  unfold productCorr
  rw [Nat.divisors_prime_pow hp k, sum_map]
  refine sum_congr rfl fun i hi => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (Nat.lt_succ_iff.1 (mem_range.1 hi)) hp.pos]

/-- The critical weight of a prime power splits along the tower: for `i ≤ k`,
`(p^k)^{−1/2} = p^{−i/2} p^{−(k−i)/2}`. -/
theorem rpow_neg_half_split {p : ℝ} (hp : 0 < p) {i k : ℕ} (hik : i ≤ k) :
    (p ^ k) ^ (-(1 / 2 : ℝ)) = p ^ (-(i : ℝ) / 2) * p ^ (-((k - i : ℕ) : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_add hp, Nat.cast_sub hik]
  congr 1
  ring

/-! ### The Cauchy product of a tower is a polynomial square -/

/-- The generating polynomial of a finitely supported sequence. -/
def genPoly (u : ℕ → ℝ) (K : ℕ) : ℝ[X] := ∑ i ∈ range (K + 1), C (u i) * X ^ i

theorem coeff_genPoly {u : ℕ → ℝ} {K : ℕ} (hu : ∀ i, K < i → u i = 0) (j : ℕ) :
    (genPoly u K).coeff j = u j := by
  unfold genPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hu j (by simpa using h)).symm

theorem eval_one_genPoly (u : ℕ → ℝ) (K : ℕ) :
    (genPoly u K).eval 1 = ∑ i ∈ range (K + 1), u i := by
  unfold genPoly
  rw [eval_finsetSum]
  simp

theorem natDegree_genPoly_le (u : ℕ → ℝ) (K : ℕ) : (genPoly u K).natDegree ≤ K :=
  natDegree_sum_le_of_forall_le _ _ fun i hi =>
    (natDegree_C_mul_X_pow_le (u i) i).trans (Nat.lt_succ_iff.1 (mem_range.1 hi))

/-- **Cauchy product of a finitely supported sequence**:
`(Σ_{i ≤ K} u_i)² = Σ_{k ≤ 2K} Σ_{i ≤ k} u_i u_{k−i}`. -/
theorem sq_sum_eq_sum_cauchy {u : ℕ → ℝ} {K : ℕ} (hu : ∀ i, K < i → u i = 0) :
    (∑ i ∈ range (K + 1), u i) ^ 2 =
      ∑ k ∈ range (2 * K + 1), ∑ i ∈ range (k + 1), u i * u (k - i) := by
  have hdeg : (genPoly u K * genPoly u K).natDegree < 2 * K + 1 :=
    Nat.lt_succ_of_le (natDegree_mul_le.trans
      (by have := natDegree_genPoly_le u K; omega))
  have h1 : (genPoly u K * genPoly u K).eval 1 = (∑ i ∈ range (K + 1), u i) ^ 2 := by
    rw [eval_mul, eval_one_genPoly, sq]
  rw [← h1, eval_eq_sum_range' hdeg]
  refine sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_genPoly hu, coeff_genPoly hu]

/-! ### The rank-one law -/

/-- **The frustration of a tower is rank one**: the product contribution of the tower of `p` is
`log p · (S_p(q)² − q(1)²)`. -/
theorem sum_vonMangoldt_productCorr_prime_pow (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hq : ∀ i, K < i → q (p ^ i) = 0) :
    towerProductPart q p K = Real.log p * (towerMellin q p K ^ 2 - q 1 ^ 2) := by
  set u : ℕ → ℝ := fun i => q (p ^ i) * (p : ℝ) ^ (-(i : ℝ) / 2) with hu_def
  have hu : ∀ i, K < i → u i = 0 := fun i hi => by simp [hu_def, hq i hi]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- each tower term is the Cauchy coefficient of `u`
  have hterm : ∀ k, ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k)
      = ∑ i ∈ range (k + 1), u i * u (k - i) := by
    intro k
    rw [productCorr_prime_pow q hp k, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    simp only [hu_def]
    rw [Nat.cast_pow, rpow_neg_half_split hp0 hik]
    ring
  have hΛ : ∀ k, 1 ≤ k → Λ (p ^ k) = Real.log p := fun k hk => by
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  -- peel the `k = 0` term, where `Λ(1) = 0`
  unfold towerProductPart towerMellin
  rw [sq_sum_eq_sum_cauchy hu, sum_range_succ', sum_range_succ']
  simp only [mul_assoc, hterm]
  have h0 : ∑ i ∈ range (0 + 1), u i * u (0 - i) = q 1 ^ 2 := by simp [hu_def, sq]
  have hΛ0 : Λ (p ^ 0) = 0 := by simp
  rw [h0, hΛ0, zero_mul, add_zero, add_sub_cancel_right, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [hΛ (k + 1) (by omega)]

/-- **Orientation reading**: the product part of a tower is at least `−log p · q(1)²`. -/
theorem sum_vonMangoldt_productCorr_prime_pow_ge (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hq : ∀ i, K < i → q (p ^ i) = 0) :
    -(Real.log p * q 1 ^ 2) ≤ towerProductPart q p K := by
  rw [sum_vonMangoldt_productCorr_prime_pow q hp hq]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  nlinarith [sq_nonneg (towerMellin q p K)]

/-- For a profile vanishing at `1`, the product part of every tower is a square. -/
theorem towerProductPart_nonneg (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hq : ∀ i, K < i → q (p ^ i) = 0) (h1 : q 1 = 0) : 0 ≤ towerProductPart q p K := by
  have := sum_vonMangoldt_productCorr_prime_pow_ge q hp hq
  rw [h1] at this
  simpa using this

/-- **The odd prime side is at most twice its ratio part**, over any finite set of towers, for
profiles vanishing at `1`: the frustrating sum pairs subtract a sum of rank-one squares. -/
theorem latticeOddPrimeSide_le_of_eq_zero (q : ℕ → ℝ) (X : ℕ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {K : ℕ} (hq : ∀ p ∈ S, ∀ i, K < i → q (p ^ i) = 0) (h1 : q 1 = 0) :
    latticeOddPrimeSide q X S K ≤
      2 * ∑ p ∈ S, ∑ k ∈ range (2 * K + 1),
        Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ratioCorr q X (p ^ k) := by
  unfold latticeOddPrimeSide
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  rw [mul_sum]
  have hsplit : ∀ k, Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 * ratioCorr q X (p ^ k) - productCorr q (p ^ k)) =
      2 * (Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ratioCorr q X (p ^ k)) -
        Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k) := fun k => by ring
  simp_rw [hsplit]
  rw [sum_sub_distrib]
  have := towerProductPart_nonneg q (hS p hp) (hq p hp) h1
  unfold towerProductPart at this
  linarith

/-- **The rank-one law over a finite set of towers.** -/
theorem sum_towerProductPart (q : ℕ → ℝ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {K : ℕ}
    (hq : ∀ p ∈ S, ∀ i, K < i → q (p ^ i) = 0) :
    ∑ p ∈ S, towerProductPart q p K =
      ∑ p ∈ S, Real.log p * (towerMellin q p K ^ 2 - q 1 ^ 2) :=
  sum_congr rfl fun p hp => sum_vonMangoldt_productCorr_prime_pow q (hS p hp) (hq p hp)

end

end GaloisForLFunctions.ArithmeticOrientationTheory
