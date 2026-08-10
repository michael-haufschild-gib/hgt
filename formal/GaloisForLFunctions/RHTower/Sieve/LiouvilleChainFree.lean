import GaloisForLFunctions.RHTower.Sieve.LiouvilleChain
import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceSharp

/-!
# The Liouville chain without a smoothness gate

Every capstone of `LiouvilleChain` carries the hypothesis
`1/log z ≤ zetaLowerA / log⁹(t₀·2^K)`, inherited from the zero-free strip that supplies the uniform
distance: the smoothness parameter has to exceed `exp(log⁹T/A)`.

The three-four-one lower bound for `|ζ|` right of the abscissa supplies a distance with no such
gate (`exists_mulDistSqPair_ge_free`), at the cost of a self-loss `(3/4) log log z`.  Substituting
it removes the hypothesis from all three capstones, so the chain applies at every smoothness
parameter and every height.
-/

noncomputable section
namespace RHTower.Sieve

open Complex

/-- The gate-free distance the chain consumes, as a square root. -/
def liouvilleDeltaFree (C : ℝ) (z : ℕ) (T : ℝ) : ℝ :=
  Real.sqrt (logLog z - 3 / 4 * Real.log (1 + Real.log (z : ℝ))
    - 1 / 4 * Real.log (3 + Real.log (4 + 2 * T)) - C)

/-- **The uniform distance with no gate.**  Valid for every truncation and every frequency range. -/
theorem exists_liouvilleC_delta_free :
    ∃ C : ℝ, ∀ (z : ℕ) (T : ℝ), 3 ≤ z → 0 ≤ T → ∀ t : ℝ, |t| ≤ T →
      liouvilleDeltaFree C z T
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
  obtain ⟨C, hC⟩ := exists_mulDistSqPair_ge_free
  refine ⟨C, fun z T hz hT t ht => ?_⟩
  rw [liouvilleDeltaFree]
  refine Real.sqrt_le_sqrt (le_trans ?_ (hC liouvilleC z t hz
    (fun p hp => liouvilleC_prime (Nat.prime_of_mem_primesLE hp))))
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h1 : Real.log (4 + 2 * |t|) ≤ Real.log (4 + 2 * T) :=
    Real.log_le_log (by linarith) (by linarith)
  have hnn : (0 : ℝ) ≤ Real.log (4 + 2 * |t|) := Real.log_nonneg (by linarith)
  have h2 : Real.log (3 + Real.log (4 + 2 * |t|)) ≤ Real.log (3 + Real.log (4 + 2 * T)) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-- **The Liouville partial sum through the whole chain, with no smoothness gate.**  The statement
of `exists_norm_sum_Icc_liouvilleC_mul_log_le` with the hypothesis
`1/log z ≤ zetaLowerA/log⁹(t₀2^K)` removed.
-/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_free :
    ∃ C : ℝ, ∀ (N z K zA YA zB YB : ℕ) (σ t₀ : ℝ), 2 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K →
      1 ≤ YA → YA ≤ zA → 2 ≤ zA → 0 < Real.log YA →
      1 ≤ YB → YB ≤ zB → 2 ≤ zB → 0 < Real.log YB →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (2 * ((N : ℝ) + 1) * ((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
                  * (((N : ℝ) + 1 / 2)) ^ σ
                  * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                  * (2 * perronVerticalProductBound (ghsOuter liouvilleC N) (ghsInner liouvilleC N)
                        (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀
                        (dampedSize σ (liouvilleDeltaFree C z (t₀ * 2 ^ K)) z N) zA YA zB YB K
                      + ((dampedSize σ (liouvilleDeltaFree C z (t₀ * 2 ^ K)) z N)
                            * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt
                                (sieveMeanSquareConst (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ YA
                                  + sieveMeanSquareRate (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ
                                      zA YA * t₀)
                              * Real.sqrt
                                (sieveMeanSquareConst (ghsInner liouvilleC N) (Finset.Icc 1 N) σ YB
                                  + sieveMeanSquareRate (ghsInner liouvilleC N) (Finset.Icc 1 N) σ
                                      zB YB * t₀)))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_delta_free
  refine ⟨C, fun N z K zA YA zB YB σ t₀ hN hz hσ ht₀ hT hYA hYzA hzA hlogA hYB hYzB hzB
    hlogB => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDeltaFree C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    exact hC z (t₀ * 2 ^ K) hz (by positivity) t ht
  exact norm_sum_Icc_mul_log_le_damped liouvilleC_mul norm_liouvilleC_le liouvilleC_one hN hσ ht₀
    (Real.sqrt_nonneg _) hz1 K hunif zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB


/-- **The Liouville partial sum with the near-diagonal truncation error and no smoothness gate.**
The statement of `exists_norm_sum_Icc_liouvilleC_mul_log_near_le` with the hypothesis
`1/log z ≤ zetaLowerA/log⁹(t₀2^K)` removed.
-/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_near_free :
    ∃ C : ℝ, ∀ (N z K zA YA zB YB : ℕ) (σ t₀ : ℝ), 2 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K →
      1 ≤ YA → YA ≤ zA → 2 ≤ zA → 0 < Real.log YA →
      1 ≤ YB → YB ≤ zB → 2 ≤ zB → 0 < Real.log YB →
      ‖∑ n ∈ Finset.Icc 1 N, liouvilleC n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
                  * (((N : ℝ) + 1 / 2)) ^ σ
                  * (5 * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                  / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                  * (2 * perronVerticalProductBound (ghsOuter liouvilleC N) (ghsInner liouvilleC N)
                        (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀
                        (dampedSize σ (liouvilleDeltaFree C z (t₀ * 2 ^ K)) z N) zA YA zB YB K
                      + ((dampedSize σ (liouvilleDeltaFree C z (t₀ * 2 ^ K)) z N)
                            * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt
                                (sieveMeanSquareConst (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ YA
                                  + sieveMeanSquareRate (ghsOuter liouvilleC N) (Finset.Icc 1 N) σ
                                      zA YA * t₀)
                              * Real.sqrt
                                (sieveMeanSquareConst (ghsInner liouvilleC N) (Finset.Icc 1 N) σ YB
                                  + sieveMeanSquareRate (ghsInner liouvilleC N) (Finset.Icc 1 N) σ
                                      zB YB * t₀)))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_delta_free
  refine ⟨C, fun N z K zA YA zB YB σ t₀ hN hz hσ ht₀ hT hYA hYzA hzA hlogA hYB hYzB hzB
    hlogB => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDeltaFree C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    exact hC z (t₀ * 2 ^ K) hz (by positivity) t ht
  exact norm_sum_Icc_mul_log_le_damped_near liouvilleC_mul norm_liouvilleC_le liouvilleC_one hN hσ
    ht₀ (Real.sqrt_nonneg _) hz1 K hunif zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB


/-- **The Liouville partial sum at per-block sieve levels, near-diagonal truncation error, no
smoothness gate.**  The statement of `exists_norm_sum_Icc_liouvilleC_mul_log_block_near_le` with the
hypothesis `1/log z ≤ zetaLowerA/log⁹(t₀2^K)` removed.
-/
theorem exists_norm_sum_Icc_liouvilleC_mul_log_block_near_free :
    ∃ C : ℝ, ∀ (N z K : ℕ) (ZA YlA ZB YlB : ℕ → ℕ) (σ t₀ : ℝ), 2 ≤ N → 3 ≤ z → 1 < σ → 1 ≤ t₀ →
      9 ≤ t₀ * 2 ^ K →
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
          + (((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
                  * (((N : ℝ) + 1 / 2)) ^ σ
                  * (5 * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                  / (Real.pi * (t₀ * 2 ^ K))
              + (1 / (2 * Real.pi))
                  * (2 * perronVerticalAffineProductBound σ ((N : ℝ) + 1 / 2) t₀
                        (dampedSize σ (liouvilleDeltaFree C z (t₀ * 2 ^ K)) z N)
                        (blockAffineConst (ghsOuter liouvilleC N) N σ ZA YlA)
                        (blockAffineRate (ghsOuter liouvilleC N) N σ ZA YlA)
                        (blockAffineConst (ghsInner liouvilleC N) N σ ZB YlB)
                        (blockAffineRate (ghsInner liouvilleC N) N σ ZB YlB) K
                      + ((dampedSize σ (liouvilleDeltaFree C z (t₀ * 2 ^ K)) z N)
                            * ((N : ℝ) + 1 / 2) ^ σ / σ)
                          * (Real.sqrt (blockAffineConst (ghsOuter liouvilleC N) N σ ZA YlA
                                + blockAffineRate (ghsOuter liouvilleC N) N σ ZA YlA * t₀)
                              * Real.sqrt (blockAffineConst (ghsInner liouvilleC N) N σ ZB YlB
                                + blockAffineRate (ghsInner liouvilleC N) N σ ZB YlB * t₀)))) := by
  obtain ⟨C, hC⟩ := exists_liouvilleC_delta_free
  refine ⟨C, fun N z K ZA YlA ZB YlB σ t₀ hN hz hσ ht₀ hT hYA hYzA hzA hlogA hYB hYzB hzB
    hlogB => ?_⟩
  have hz1 : 1 ≤ z := by omega
  have hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      liouvilleDeltaFree C z (t₀ * 2 ^ K)
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
    intro t ht
    exact hC z (t₀ * 2 ^ K) hz (by positivity) t ht
  exact norm_sum_Icc_mul_log_le_damped_block_near liouvilleC_mul norm_liouvilleC_le liouvilleC_one
    hN hσ ht₀ (Real.sqrt_nonneg _) hz1 K hunif
    ZA YlA ZB YlB hYA hYzA hzA hlogA hYB hYzB hzB hlogB

/-- The distance at strip quality: only `log log T` is lost, at the cost of `z ≤ T`. -/
def liouvilleDeltaHeight (C : ℝ) (z : ℕ) (T : ℝ) : ℝ :=
  Real.sqrt (logLog z - Real.log (Real.log T) - C)

/-- **The uniform distance at strip quality with no gate.**  A drop-in `hunif` for
`norm_sum_Icc_mul_log_le_damped(_near)`: where `exists_liouvilleC_mulDistSqPair_ge_uniform` loses
`7 log log T` and demands `log⁹T/A ≤ log z`, this loses `log log T + C` and demands only `z ≤ T`. -/
theorem exists_liouvilleC_delta_height :
    ∃ C : ℝ, ∀ (z : ℕ) (T : ℝ), 3 ≤ z → 3 ≤ T → (z : ℝ) ≤ T → ∀ t : ℝ, |t| ≤ T →
      liouvilleDeltaHeight C z T
        ≤ Real.sqrt (mulDistSqPair liouvilleC (charFn t) (Nat.primesLE z)) := by
  obtain ⟨C, hC⟩ := exists_mulDistSqPair_ge_height
  refine ⟨C, fun z T hz hT hzT t ht => ?_⟩
  rw [liouvilleDeltaHeight]
  exact Real.sqrt_le_sqrt (hC liouvilleC z T t hz hT hzT ht
    (fun p hp => liouvilleC_prime (Nat.prime_of_mem_primesLE hp)))

end RHTower.Sieve
