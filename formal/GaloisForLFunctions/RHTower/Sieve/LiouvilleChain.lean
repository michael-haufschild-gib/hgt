import GaloisForLFunctions.RHTower.Sieve.HalaszGhsSharpCutoff
import GaloisForLFunctions.RHTower.Sieve.MoebiusUniformFrequency

/-!
# The Liouville function through the chain

The corpus's uniform frequency estimate is stated for *any* sequence taking the value `−1` at every prime
up to `z`, so it applies verbatim to the Liouville function `λ(n) = (−1)^{Ω(n)}`, which unlike the Möbius
function is completely multiplicative and therefore admissible in the logarithmic recursion.

That gives the first bound produced by the whole chain with no hypothesis left open beyond the choice of
parameters: the distance is supplied by the zero-free strip through
`exists_mulDistSqPair_ge_uniform`, complete multiplicativity by `liouvilleC_mul`, and the analytic side by
the sharp Perron formula, the dyadic height split and the Selberg-sieve mean squares.
-/

noncomputable section
namespace RHTower.Sieve
open Complex

/-- The Liouville function `(−1)^{Ω(n)}`, as a complex sequence vanishing at `0`. -/
def liouvilleC : ℕ → ℂ := fun n =>
  if n = 0 then 0 else (-1) ^ (ArithmeticFunction.cardFactors n)

theorem liouvilleC_zero : liouvilleC 0 = 0 := by
  rw [liouvilleC, if_pos rfl]

theorem liouvilleC_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    liouvilleC n = (-1) ^ (ArithmeticFunction.cardFactors n) := by
  rw [liouvilleC, if_neg hn]

theorem liouvilleC_one : liouvilleC 1 = 1 := by
  rw [liouvilleC_of_ne_zero one_ne_zero, ArithmeticFunction.cardFactors_one, pow_zero]

/-- The Liouville function is `−1` at every prime. -/
theorem liouvilleC_prime {p : ℕ} (hp : p.Prime) : liouvilleC p = -1 := by
  rw [liouvilleC_of_ne_zero hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp, pow_one]

theorem norm_liouvilleC_le (n : ℕ) : ‖liouvilleC n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [liouvilleC_zero, norm_zero]
    norm_num
  · rw [liouvilleC_of_ne_zero hn, norm_pow, norm_neg, norm_one, one_pow]

/-- **The Liouville function is completely multiplicative.**  `Ω` is additive on nonzero arguments, and the
value at `0` is `0`. -/
theorem liouvilleC_mul (a b : ℕ) : liouvilleC (a * b) = liouvilleC a * liouvilleC b := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul, liouvilleC_zero, zero_mul]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [mul_zero, liouvilleC_zero, mul_zero]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [liouvilleC_of_ne_zero hab, liouvilleC_of_ne_zero ha, liouvilleC_of_ne_zero hb,
    ArithmeticFunction.cardFactors_mul ha hb, pow_add]

/-- The distance of the Liouville function from a character, bounded below uniformly over a frequency
range: the corpus's estimate at the sequence which is `−1` on the primes. -/
theorem exists_liouvilleC_mulDistSqPair_ge_uniform :
    ∃ C : ℝ, ∀ (z : ℕ) (T t : ℝ), 3 ≤ z → 9 ≤ T → |t| ≤ T →
      1 / Real.log z ≤ zetaLowerA / Real.log T ^ (9 : ℕ) →
      logLog z - 7 * Real.log (Real.log T) - C
        ≤ mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z) := by
  obtain ⟨C, hC⟩ := exists_mulDistSqPair_ge_uniform
  refine ⟨C, fun z T t hz hT htT hzt => ?_⟩
  refine hC liouvilleC z T t hz hT htT hzt ?_
  intro p hp
  exact liouvilleC_prime (Nat.prime_of_mem_primesLE hp)

/-- The distance the chain consumes, as a square root. -/
def liouvilleDelta (C : ℝ) (z : ℕ) (T : ℝ) : ℝ :=
  Real.sqrt (logLog z - 7 * Real.log (Real.log T) - C)

/-- **The Liouville partial sum through the whole chain.**  Every hypothesis of the mean value bound is
discharged: complete multiplicativity and the value `−1` at the primes by the definition of `λ`, the
uniform distance by the zero-free strip, the analytic side by the sharp Perron formula with the
Selberg-sieve mean squares.  Only the parameters remain free. -/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_le :
    ∃ C : ℝ, ∀ (N z K zA YA zB YB : ℕ) (σ t₀ : ℝ), 2 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K → 1 / Real.log z ≤ zetaLowerA / Real.log (t₀ * 2 ^ K) ^ (9 : ℕ) →
      1 ≤ YA → YA ≤ zA → 2 ≤ zA → 0 < Real.log YA →
      1 ≤ YB → YB ≤ zB → 2 ≤ zB → 0 < Real.log YB →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (2 * ((N : ℝ) + 1) * ((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ (4 : ℕ) / (Real.log 2) ^ (3 : ℕ))
                  * (((N : ℝ) + 1 / 2)) ^ σ
                  * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                  * (2 * perronVerticalProductBound (ghsOuter liouvilleC N) (ghsInner liouvilleC N)
                        (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀
                        (dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N) zA YA zB YB K
                      + ((dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N)
                            * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt
                                (sieveMeanSquareConst (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ YA
                                  + sieveMeanSquareRate (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ
                                      zA YA * t₀)
                              * Real.sqrt
                                (sieveMeanSquareConst (ghsInner liouvilleC N) (Finset.Icc 1 N) σ YB
                                  + sieveMeanSquareRate (ghsInner liouvilleC N) (Finset.Icc 1 N) σ
                                      zB YB * t₀)))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_mulDistSqPair_ge_uniform
  refine ⟨C, fun N z K zA YA zB YB σ t₀ hN hz hσ ht₀ hT hzt hYA hYzA hzA hlogA hYB hYzB hzB
    hlogB => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDelta C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    rw [liouvilleDelta]
    exact Real.sqrt_le_sqrt (hC z (t₀ * 2 ^ K) t hz hT ht hzt)
  exact norm_sum_Icc_mul_log_le_damped liouvilleC_mul norm_liouvilleC_le liouvilleC_one hN hσ ht₀
    (Real.sqrt_nonneg _) hz1 K hunif zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB

/-- **The Liouville partial sum with the near-diagonal truncation error.**  The same chain, with the
truncation error freed of its factor `N`: the only place the length of the sum now enters the error is
logarithmically, so the height is free to be chosen against the distance rather than against `N`. -/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_near_le :
    ∃ C : ℝ, ∀ (N z K zA YA zB YB : ℕ) (σ t₀ : ℝ), 2 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K → 1 / Real.log z ≤ zetaLowerA / Real.log (t₀ * 2 ^ K) ^ (9 : ℕ) →
      1 ≤ YA → YA ≤ zA → 2 ≤ zA → 0 < Real.log YA →
      1 ≤ YB → YB ≤ zB → 2 ≤ zB → 0 < Real.log YB →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ (4 : ℕ) / (Real.log 2) ^ (3 : ℕ))
                  * (((N : ℝ) + 1 / 2)) ^ σ
                  * (5 * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                  / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                  * (2 * perronVerticalProductBound (ghsOuter liouvilleC N) (ghsInner liouvilleC N)
                        (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀
                        (dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N) zA YA zB YB K
                      + ((dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N)
                            * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt
                                (sieveMeanSquareConst (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ YA
                                  + sieveMeanSquareRate (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ
                                      zA YA * t₀)
                              * Real.sqrt
                                (sieveMeanSquareConst (ghsInner liouvilleC N) (Finset.Icc 1 N) σ YB
                                  + sieveMeanSquareRate (ghsInner liouvilleC N) (Finset.Icc 1 N) σ
                                      zB YB * t₀)))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_mulDistSqPair_ge_uniform
  refine ⟨C, fun N z K zA YA zB YB σ t₀ hN hz hσ ht₀ hT hzt hYA hYzA hzA hlogA hYB hYzB hzB
    hlogB => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDelta C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    rw [liouvilleDelta]
    exact Real.sqrt_le_sqrt (hC z (t₀ * 2 ^ K) t hz hT ht hzt)
  exact norm_sum_Icc_mul_log_le_damped_near liouvilleC_mul norm_liouvilleC_le liouvilleC_one hN hσ
    ht₀ (Real.sqrt_nonneg _) hz1 K hunif zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB

/-- **The Liouville partial sum at per-block sieve levels and the near-diagonal truncation error.**  The
whole chain in its current strongest form: the level grows with the dyadic block of the support, the
truncation error depends on the length of the sum only logarithmically, and the distance comes from the
zero-free strip. -/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_block_near_le :
    ∃ C : ℝ, ∀ (N z K : ℕ) (ZA YlA ZB YlB : ℕ → ℕ) (σ t₀ : ℝ), 2 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K → 1 / Real.log z ≤ zetaLowerA / Real.log (t₀ * 2 ^ K) ^ (9 : ℕ) →
      (∀ j, 1 ≤ YlA j) → (∀ j, YlA j ≤ ZA j) → (∀ j, 2 ≤ ZA j) →
      (∀ j, 0 < Real.log (YlA j)) →
      (∀ j, 1 ≤ YlB j) → (∀ j, YlB j ≤ ZB j) → (∀ j, 2 ≤ ZB j) →
      (∀ j, 0 < Real.log (YlB j)) →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ (4 : ℕ) / (Real.log 2) ^ (3 : ℕ))
                  * (((N : ℝ) + 1 / 2)) ^ σ
                  * (5 * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                  / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                  * (2 * perronVerticalAffineProductBound σ ((N : ℝ) + 1 / 2) t₀
                        (dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N)
                        (blockAffineConst (ghsOuter liouvilleC N) N σ ZA YlA)
                        (blockAffineRate (ghsOuter liouvilleC N) N σ ZA YlA)
                        (blockAffineConst (ghsInner liouvilleC N) N σ ZB YlB)
                        (blockAffineRate (ghsInner liouvilleC N) N σ ZB YlB) K
                      + ((dampedSize σ (liouvilleDelta C z (t₀ * 2 ^ K)) z N)
                            * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt (blockAffineConst (ghsOuter liouvilleC N) N σ ZA YlA
                                + blockAffineRate (ghsOuter liouvilleC N) N σ ZA YlA * t₀)
                              * Real.sqrt (blockAffineConst (ghsInner liouvilleC N) N σ ZB YlB
                                + blockAffineRate (ghsInner liouvilleC N) N σ ZB YlB * t₀)))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_mulDistSqPair_ge_uniform
  refine ⟨C, fun N z K ZA YlA ZB YlB σ t₀ hN hz hσ ht₀ hT hzt hYA hYzA hzA hlogA hYB hYzB hzB
    hlogB => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDelta C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    rw [liouvilleDelta]
    exact Real.sqrt_le_sqrt (hC z (t₀ * 2 ^ K) t hz hT ht hzt)
  exact norm_sum_Icc_mul_log_le_damped_block_near liouvilleC_mul norm_liouvilleC_le liouvilleC_one
    hN hσ ht₀ (Real.sqrt_nonneg _) hz1 K hunif
    ZA YlA ZB YlB hYA hYzA hzA hlogA hYB hYzB hzB hlogB

end RHTower.Sieve
end
