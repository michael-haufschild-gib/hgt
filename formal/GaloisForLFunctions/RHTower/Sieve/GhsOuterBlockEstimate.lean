import GaloisForLFunctions.RHTower.Sieve.GhsOuterBlockDamping
import GaloisForLFunctions.RHTower.Sieve.BlockSieveMeanSquare
/-!
# The outer weight's block estimate, with its damping kept

The block estimate of a prime weight's sieve mean square accepts any uniform bound on the block's coefficients.
For the outer weight of the Granville–Harper–Soundararajan convolution that bound is
`(j+1)log 2/log⌊N/2^{j+1}⌋`, its own damping evaluated at the block's endpoint, rather than the constant
`(1/log 2)(j+1)log 2` that a global bound gives.  Since `log⌊N/2^{j+1}⌋ ≥ (⌊log₂N⌋ − j − 1)log 2`, the `j`-th
block's constant is `≍ (j+1)/(log₂N − j)`, so the blocks near `N` — where the geometric weight `2^{−2σj}` puts
the mass — are damped by the factor a constant bound discards.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The outer weight's block, bounded with its own damping kept. -/
theorem norm_coeffBlock_ghsOuter_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {j : ℕ}
    (h2 : 2 ≤ N / 2 ^ (j + 1)) (n : ℕ) :
    ‖coeffBlock (ghsOuter f N) (fun m => Nat.log 2 m) j n‖
      ≤ (((j : ℝ) + 1) * Real.log 2) / Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hblockR : (2 : ℝ) ≤ ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h2
  have hden : 0 < Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) := Real.log_pos (by linarith)
  rw [coeffBlock]
  by_cases hk : Nat.log 2 n = j
  · rw [if_pos hk]
    exact norm_ghsOuter_le_block hf N hk h2
  · rw [if_neg hk, norm_zero]
    positivity

/-- **The outer weight's block estimate, with its damping.**  The block's coefficient constant is
`(j+1)log 2/log⌊N/2^{j+1}⌋`, which decays as the block approaches `N`, instead of the constant
`(1/log 2)(j+1)log 2` a global bound would give. -/
theorem sieveMeanSquare_coeffBlock_ghsOuter_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N M : ℕ)
    {j : ℕ} (hj : 1 ≤ j) (h2 : 2 ≤ N / 2 ^ (j + 1)) {σ : ℝ} (hσ : 0 < σ) (z Y : ℕ)
    (hz : 2 ≤ z) (hlogY : 0 < Real.log Y) :
    sieveMeanSquare (coeffBlock (ghsOuter f N) (fun m => Nat.log 2 m) j) (Finset.Icc 1 M) σ z Y
      ≤ (((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 / ((j : ℝ) * Real.log 2))
          * ((2 * (((2 ^ (j + 1) : ℕ) : ℝ)
                  * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
                / Real.log Y + selbergFibreError z Y + (z : ℝ))
              * (((((j : ℝ) + 1) * Real.log 2)
                    / Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ)) ^ 2
                  * (2 : ℝ) ^ (-(2 * σ * (j : ℝ))))) :=
  sieveMeanSquare_coeffBlock_le_of_bound (norm_coeffBlock_ghsOuter_le hf N h2)
    (fun _ hn => ghsOuter_support hn) M hj hσ z Y hz hlogY

end RHTower.Sieve
end
