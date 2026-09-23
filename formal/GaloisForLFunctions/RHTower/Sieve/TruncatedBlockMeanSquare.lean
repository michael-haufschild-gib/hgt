import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
import GaloisForLFunctions.HTGeometry.WeightedHolder
import GaloisForLFunctions.RHTower.Sieve.TruncatedPrimeSieveMeanSquare
import GaloisForLFunctions.RHTower.Sieve.GhsStepFourTruncated
/-!
# The truncated mean square, block by block

Minkowski over the restricted measure splits a Dirichlet polynomial's truncated mean square into its dyadic
blocks,

`(∫_{|y| ≤ T} ‖L(a,σ+iy)‖²)^{1/2} ≤ ∑_j (∫_{|y| ≤ T} ‖L(a_j,σ+iy)‖²)^{1/2}`,

and each block's mean square is then discharged by the Selberg sieve at a level free to depend on the block.
This is the truncated counterpart of the Lorentzian block sum, and it is the form the argument needs: the
Selberg count is sharp only when `log Y` matches the logarithm of the primes in play, which on the `j`-th block
is `j log 2`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- **The truncated mean square against the dyadic blocks.**  Minkowski over the restricted measure. -/
theorem sqrt_integral_Icc_normSq_LSeries_le_sum_blocks {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M) (σ T : ℝ) :
    Real.sqrt (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          Real.sqrt (∫ y in Set.Icc (-T) T,
            ‖LSeries (coeffBlock a (fun n => Nat.log 2 n) j) ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ)) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  set g : ℕ → ℝ → ℂ := fun j y =>
    LSeries (coeffBlock a (fun n => Nat.log 2 n) j) ((σ : ℂ) + (y : ℝ) * I) with hg
  have hcont : ∀ j : ℕ, Continuous (g j) := by
    intro j
    exact continuous_LSeries_line_of_support hs0 (coeffBlock_support hsupp) σ
  have hmg : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      AEStronglyMeasurable (g j) (volume.restrict (Set.Icc (-T) T)) :=
    fun j _ => (hcont j).aestronglyMeasurable.restrict
  have hig : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      Integrable (fun y => ‖g j y‖ ^ (2 : ℕ)) (volume.restrict (Set.Icc (-T) T)) :=
    fun j _ => ((hcont j).norm.pow 2).integrableOn_Icc
  have hpt : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ)
      = ‖∑ j ∈ Finset.range (Nat.log 2 M + 1), g j y‖ ^ (2 : ℕ) := by
    intro y
    rw [hg, LSeries_eq_sum_dyadic_blocks hsupp ((σ : ℂ) + (y : ℝ) * I)]
  rw [setIntegral_congr_fun measurableSet_Icc (fun y _ => hpt y)]
  exact GaloisForLFunctions.HTGeometry.sqrt_integral_normSq_sum_le_measure _ g hmg hig

/-- **The truncated mean square, block by block, each block at its own sieve level.**  The truncated analogue of
the Lorentzian block sum: Minkowski over the restricted measure splits the polynomial, and each block's mean
square is discharged by the Selberg sieve at a level free to depend on the block. -/
theorem sqrt_integral_Icc_normSq_LSeries_le_sum_block_sieve {a : ℕ → ℂ} {M : ℕ}
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 M)
    (hprime : ∀ n ∈ Finset.Icc 1 M, a n ≠ 0 → n.Prime) (σ : ℝ) {T : ℝ} (hT : 0 < T)
    (Z Yl : ℕ → ℕ) (hY : ∀ j, 1 ≤ Yl j) (hYz : ∀ j, Yl j ≤ Z j) (hz : ∀ j, 2 ≤ Z j)
    (hlog : ∀ j, 0 < Real.log (Yl j)) :
    Real.sqrt (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ (2 : ℕ))
      ≤ ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          Real.sqrt (truncSieveSum (coeffBlock a (fun n => Nat.log 2 n) j) (Finset.Icc 1 M) σ T
            (Z j) (Yl j)) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  refine le_trans (sqrt_integral_Icc_normSq_LSeries_le_sum_blocks hsupp σ T) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine Real.sqrt_le_sqrt ?_
  rw [truncSieveSum]
  exact integral_Icc_normSq_LSeries_le_prime_sieve hs0
    (coeffBlock_support (κ := fun n => Nat.log 2 n) (j := j) hsupp)
    (coeffBlock_prime (κ := fun n => Nat.log 2 n) (j := j) hprime) σ hT (Z j) (Yl j)
    (hY j) (hYz j) (hz j) (hlog j)

end RHTower.Sieve
end
