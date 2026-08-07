import GaloisForLFunctions.RHTower.Sieve.BlockSieveMeanSquare
import GaloisForLFunctions.RHTower.Sieve.BlockMeanSquare
/-!
# The sieve level chosen per dyadic block

On the block `2^j ≤ n < 2^{j+1}` the level is `max 2 (2^{⌊j/4⌋})` and the modulus is the block's right
endpoint `2^{j+1}`.  The fourth of the block's logarithm is what keeps the Selberg fibre error
`E = Y²e^{4c}(log z)⁴` below the block's main term `2^{j+1}·2 sinh δ/log Y`, and the floor at `2` keeps
`log Y` positive so that the count is meaningful on every block, including the first.

With these levels the mean square of a prime-supported polynomial is an explicit sum over the blocks: the
first block is left as it stands and every later block is replaced by the closed-form estimate, so the
right-hand side is a function of `j`, `σ` and the coefficient constant `A` alone.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The sieve level on the dyadic block `2^j ≤ n < 2^{j+1}`: an eighth of the block's logarithm, kept at least
`2` so that its logarithm is positive.  The eighth is what keeps the Selberg fibre error `Y²e^{4c}(log z)⁴`
below the block's main term `2^{j+1}·2 sinh δ/log Y`. -/
def blockSieveLevel (j : ℕ) : ℕ := max 2 (2 ^ (j / 8))

/-- The sieve modulus on the block: the square root of the block's length, kept at least `2`.  The modulus
enters the count *additively*, so it must stay far below the block's length — taking it to be the block's right
endpoint would make the count worse than counting every integer of the block. -/
def blockSieveModulus (j : ℕ) : ℕ := max 2 (2 ^ (j / 2))

theorem one_le_blockSieveLevel (j : ℕ) : 1 ≤ blockSieveLevel j := by
  rw [blockSieveLevel]
  exact le_trans (by norm_num) (le_max_left 2 _)

theorem two_le_blockSieveLevel (j : ℕ) : 2 ≤ blockSieveLevel j := le_max_left 2 _

theorem two_le_blockSieveModulus (j : ℕ) : 2 ≤ blockSieveModulus j := le_max_left 2 _

theorem blockSieveLevel_le_blockSieveModulus (j : ℕ) :
    blockSieveLevel j ≤ blockSieveModulus j := by
  rw [blockSieveLevel, blockSieveModulus]
  refine max_le (le_max_left 2 _) ?_
  refine le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : j / 8 ≤ j / 2)) ?_
  exact le_max_right 2 _

theorem log_blockSieveLevel_pos (j : ℕ) : 0 < Real.log (blockSieveLevel j) := by
  have h2 : (2 : ℝ) ≤ ((blockSieveLevel j : ℕ) : ℝ) := by
    have := two_le_blockSieveLevel j
    exact_mod_cast this
  exact Real.log_pos (by linarith)

/-- **The block sum at the chosen levels.**  Each dyadic block is sieved at level `max 2 (2^{⌊j/4⌋})` with
modulus the block's right endpoint, so the mean square of a prime-supported polynomial is bounded by an
explicit sum over the blocks. -/
theorem sqrt_integral_lorentz_normSq_LSeries_le_block_sum {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n ∈ Finset.Icc 1 M, a n ≠ 0 → n.Prime) (σ : ℝ) :
    Real.sqrt (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2 * (1 + y ^ 2)⁻¹)
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          Real.sqrt (25 * Real.pi ^ 2
            * sieveMeanSquare (coeffBlock a (fun n => Nat.log 2 n) j) (Finset.Icc 1 M) σ
                (blockSieveModulus j) (blockSieveLevel j)) :=
  sqrt_integral_lorentz_normSq_LSeries_le_sum_prime_sieve hsupp hprime σ
    blockSieveModulus blockSieveLevel one_le_blockSieveLevel
    blockSieveLevel_le_blockSieveModulus two_le_blockSieveModulus log_blockSieveLevel_pos

/-- **The block sum in closed form.**  Each summand is bounded by the closed-form block estimate at the chosen
level, so the whole quantity is an explicit function of `j`, `σ` and the coefficient constant. -/
theorem sqrt_integral_lorentz_normSq_LSeries_le_block_sum_explicit {a : ℕ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (haB : ∀ n : ℕ, ‖a n‖ ≤ A * Real.log n) {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n : ℕ, a n ≠ 0 → Nat.Prime n) {σ : ℝ} (hσ : 0 < σ) :
    Real.sqrt (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2 * (1 + y ^ 2)⁻¹)
      ≤ Real.sqrt (25 * Real.pi ^ 2
            * sieveMeanSquare (coeffBlock a (fun n => Nat.log 2 n) 0) (Finset.Icc 1 M) σ
                (blockSieveModulus 0) (blockSieveLevel 0))
        + ∑ j ∈ Finset.Ico 1 (Nat.log 2 M + 1),
            Real.sqrt (25 * Real.pi ^ 2
              * ((((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 / ((j : ℝ) * Real.log 2))
                  * ((2 * (((2 ^ (j + 1) : ℕ) : ℝ)
                          * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
                        / Real.log (blockSieveLevel j)
                      + selbergFibreError (blockSieveModulus j) (blockSieveLevel j)
                      + ((blockSieveModulus j : ℕ) : ℝ))
                    * ((A * (((j : ℝ) + 1) * Real.log 2)) ^ 2
                        * (2 : ℝ) ^ (-(2 * σ * (j : ℝ))))))) := by
  classical
  have hstart := sqrt_integral_lorentz_normSq_LSeries_le_block_sum hsupp
    (fun n _ hn => hprime n hn) σ
  refine hstart.trans ?_
  have hsplit : Finset.range (Nat.log 2 M + 1)
      = insert 0 (Finset.Ico 1 (Nat.log 2 M + 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hrest : ∀ j ∈ Finset.Ico 1 (Nat.log 2 M + 1),
      Real.sqrt (25 * Real.pi ^ 2
          * sieveMeanSquare (coeffBlock a (fun n => Nat.log 2 n) j) (Finset.Icc 1 M) σ
              (blockSieveModulus j) (blockSieveLevel j))
        ≤ Real.sqrt (25 * Real.pi ^ 2
            * ((((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 / ((j : ℝ) * Real.log 2))
                * ((2 * (((2 ^ (j + 1) : ℕ) : ℝ)
                        * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
                      / Real.log (blockSieveLevel j)
                    + selbergFibreError (blockSieveModulus j) (blockSieveLevel j)
                    + ((blockSieveModulus j : ℕ) : ℝ))
                  * ((A * (((j : ℝ) + 1) * Real.log 2)) ^ 2
                      * (2 : ℝ) ^ (-(2 * σ * (j : ℝ))))))) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine Real.sqrt_le_sqrt ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact sieveMeanSquare_coeffBlock_le hA haB hprime M hj.1 hσ (blockSieveModulus j)
      (blockSieveLevel j) (two_le_blockSieveModulus j) (log_blockSieveLevel_pos j)
  linarith [Finset.sum_le_sum hrest]

end RHTower.Sieve
end

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The level's logarithm grows linearly in the block index: `log Y_j ≥ ((j−7)/8)·log 2`, and it is never
below `log 2`. -/
theorem log_blockSieveLevel_ge (j : ℕ) :
    ((j : ℝ) - 7) / 8 * Real.log 2 ≤ Real.log (blockSieveLevel j) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℕ) ^ (j / 8) ≤ blockSieveLevel j := by
    rw [blockSieveLevel]
    exact le_max_right 2 _
  have hR : ((2 : ℝ) ^ (j / 8 : ℕ)) ≤ ((blockSieveLevel j : ℕ) : ℝ) := by
    have : ((2 ^ (j / 8) : ℕ) : ℝ) ≤ ((blockSieveLevel j : ℕ) : ℝ) := by exact_mod_cast hpow
    simpa using this
  have hlg := Real.log_le_log (by positivity) hR
  rw [Real.log_pow] at hlg
  refine le_trans ?_ hlg
  have hdiv : ((j : ℝ) - 7) / 8 ≤ ((j / 8 : ℕ) : ℝ) := by
    have hmul : j ≤ 8 * (j / 8) + 7 := by omega
    have hmulR : (j : ℝ) ≤ 8 * ((j / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast hmul
    linarith
  exact mul_le_mul_of_nonneg_right hdiv hlog2.le

/-- The level is at most twice the eighth power root of the block's length, so its square is at most
`4·2^{j/4}`: the fibre error `Y²e^{4c}(log z)⁴` is therefore `O(2^{j/4}·j⁴)`, far below the block's main term. -/
theorem blockSieveLevel_le_two_mul (j : ℕ) :
    ((blockSieveLevel j : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (j / 8 : ℕ) := by
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (j / 8 : ℕ) := one_le_pow₀ (by norm_num)
  rw [blockSieveLevel]
  rcases le_total ((2 : ℕ) ^ (j / 8)) 2 with h | h
  · rw [max_eq_left h]
    norm_num
    linarith
  · rw [max_eq_right h]
    have hR : ((2 ^ (j / 8) : ℕ) : ℝ) = (2 : ℝ) ^ (j / 8 : ℕ) := by push_cast; ring
    rw [hR]
    linarith

/-- The modulus is at most twice the square root of the block's length. -/
theorem blockSieveModulus_le_two_mul (j : ℕ) :
    ((blockSieveModulus j : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (j / 2 : ℕ) := by
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (j / 2 : ℕ) := one_le_pow₀ (by norm_num)
  rw [blockSieveModulus]
  rcases le_total ((2 : ℕ) ^ (j / 2)) 2 with h | h
  · rw [max_eq_left h]
    norm_num
    linarith
  · rw [max_eq_right h]
    have hR : ((2 ^ (j / 2) : ℕ) : ℝ) = (2 : ℝ) ^ (j / 2 : ℕ) := by push_cast; ring
    rw [hR]
    linarith

end RHTower.Sieve
end
