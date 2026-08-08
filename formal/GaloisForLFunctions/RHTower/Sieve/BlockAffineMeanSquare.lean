import GaloisForLFunctions.RHTower.Sieve.PrimeSieveAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.TruncatedBlockMeanSquare

/-!
# The affine mean square with a sieve level per dyadic block

A single global sieve level is capped by the sieve's own error: `selbergFibreError z Y = Y²e^{4c}(log z)^4`
must stay under the count it estimates, and that count is `O(1)` per prime pair, so a *global* level buys
nothing — `log Y = O(1)`.  Block by block the constraint is different: the primes of the `j`-th dyadic
block live in a multiplicative window carrying `≍ 2^j` integers, so the admissible level there grows with
the block, and the leading term of the mean square is divided by `log Y_j ≍ j log 2` rather than by a
constant.

Minkowski over the coefficient blocks turns that into an affine bound for the whole mean square: with
`A = ∑_j √Q_j` and `B = ∑_j √κ_j` from the per-block constants,

`∫_{|y| ≤ U} ‖L(a,σ+iy)‖² dy ≤ (A² + AB) + (AB + B²)U`.

This is the same shape the dyadic height split consumes, so the whole analytic chain runs unchanged with
per-block levels in place of a single one.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The height-independent part of the block-sieve mean square. -/
def blockMeanSquareConst (a : ℕ → ℂ) (M : ℕ) (σ : ℝ) (Yl : ℕ → ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 M + 1),
    Real.sqrt (sieveMeanSquareConst (coeffBlock a (fun n => Nat.log 2 n) j)
      (Finset.Icc 1 M) σ (Yl j))

/-- The height-linear part of the block-sieve mean square. -/
def blockMeanSquareRate (a : ℕ → ℂ) (M : ℕ) (σ : ℝ) (Z Yl : ℕ → ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 M + 1),
    Real.sqrt (sieveMeanSquareRate (coeffBlock a (fun n => Nat.log 2 n) j)
      (Finset.Icc 1 M) σ (Z j) (Yl j))

theorem blockMeanSquareConst_nonneg (a : ℕ → ℂ) (M : ℕ) (σ : ℝ) (Yl : ℕ → ℕ) :
    0 ≤ blockMeanSquareConst a M σ Yl :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem blockMeanSquareRate_nonneg (a : ℕ → ℂ) (M : ℕ) (σ : ℝ) (Z Yl : ℕ → ℕ) :
    0 ≤ blockMeanSquareRate a M σ Z Yl :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- **The root mean square from per-block sieve levels.**  Minkowski over the coefficient blocks, each
block's mean square in affine form. -/
theorem sqrt_integral_Icc_normSq_LSeries_le_block_affine {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n ∈ Finset.Icc 1 M, a n ≠ 0 → n.Prime) (σ : ℝ) (Z Yl : ℕ → ℕ)
    (hY : ∀ j, 1 ≤ Yl j) (hYz : ∀ j, Yl j ≤ Z j) (hz : ∀ j, 2 ≤ Z j)
    (hlog : ∀ j, 0 < Real.log (Yl j)) {U : ℝ} (hU : 1 ≤ U) :
    Real.sqrt (∫ y in Set.Icc (-U) U, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ blockMeanSquareConst a M σ Yl + blockMeanSquareRate a M σ Z Yl * Real.sqrt U := by
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  refine le_trans (sqrt_integral_Icc_normSq_LSeries_le_sum_blocks hsupp σ U) ?_
  rw [blockMeanSquareConst, blockMeanSquareRate, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  set b : ℕ → ℂ := coeffBlock a (fun n => Nat.log 2 n) j with hb
  have hbsupp : ∀ n : ℕ, b n ≠ 0 → n ∈ Finset.Icc 1 M := coeffBlock_support hsupp
  have hbprime : ∀ n ∈ Finset.Icc 1 M, b n ≠ 0 → n.Prime := coeffBlock_prime hprime
  have haff := integral_Icc_normSq_LSeries_le_affine hs0 hbsupp hbprime σ hU (Z j) (Yl j)
    (hY j) (hYz j) (hz j) (hlog j)
  have hQ0 : (0 : ℝ) ≤ sieveMeanSquareConst b (Finset.Icc 1 M) σ (Yl j) :=
    sieveMeanSquareConst_nonneg b (Finset.Icc 1 M) σ (hlog j)
  have hκ0 : (0 : ℝ) ≤ sieveMeanSquareRate b (Finset.Icc 1 M) σ (Z j) (Yl j) :=
    sieveMeanSquareRate_nonneg b (Finset.Icc 1 M) σ (hz j) (hlog j)
  calc Real.sqrt (∫ y in Set.Icc (-U) U, ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ Real.sqrt (sieveMeanSquareConst b (Finset.Icc 1 M) σ (Yl j)
          + sieveMeanSquareRate b (Finset.Icc 1 M) σ (Z j) (Yl j) * U) := Real.sqrt_le_sqrt haff
    _ ≤ Real.sqrt (sieveMeanSquareConst b (Finset.Icc 1 M) σ (Yl j))
          + Real.sqrt (sieveMeanSquareRate b (Finset.Icc 1 M) σ (Z j) (Yl j) * U) :=
        GaloisForLFunctions.HTGeometry.sqrt_add_le_sqrt_add_sqrt' hQ0 (by positivity)
    _ = Real.sqrt (sieveMeanSquareConst b (Finset.Icc 1 M) σ (Yl j))
          + Real.sqrt (sieveMeanSquareRate b (Finset.Icc 1 M) σ (Z j) (Yl j)) * Real.sqrt U := by
        rw [Real.sqrt_mul hκ0]

/-- **The affine mean square with per-block sieve levels.**  The level is no longer forced to be bounded:
each dyadic block of the support carries its own modulus and level, and the mean square is affine in the
height with constants built from them. -/
theorem integral_Icc_normSq_LSeries_le_block_affine {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n ∈ Finset.Icc 1 M, a n ≠ 0 → n.Prime) (σ : ℝ) (Z Yl : ℕ → ℕ)
    (hY : ∀ j, 1 ≤ Yl j) (hYz : ∀ j, Yl j ≤ Z j) (hz : ∀ j, 2 ≤ Z j)
    (hlog : ∀ j, 0 < Real.log (Yl j)) {U : ℝ} (hU : 1 ≤ U) :
    (∫ y in Set.Icc (-U) U, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ ((blockMeanSquareConst a M σ Yl) ^ 2
            + blockMeanSquareConst a M σ Yl * blockMeanSquareRate a M σ Z Yl)
          + (blockMeanSquareConst a M σ Yl * blockMeanSquareRate a M σ Z Yl
              + (blockMeanSquareRate a M σ Z Yl) ^ 2) * U := by
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hMS0 : (0 : ℝ) ≤ ∫ y in Set.Icc (-U) U, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun y _ => by positivity
  exact le_affine_of_sqrt_le (blockMeanSquareConst_nonneg a M σ Yl)
    (blockMeanSquareRate_nonneg a M σ Z Yl) hMS0 (by linarith)
    (sqrt_integral_Icc_normSq_LSeries_le_block_affine hsupp hprime σ Z Yl hY hYz hz hlog hU)

end RHTower.Sieve
end
