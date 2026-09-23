import GaloisForLFunctions.RHTower.Sieve.BlockProductAnnulus
import GaloisForLFunctions.RHTower.Sieve.MeanSquareLevelSplit
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromAnnulus

/-!
# One bilinear block split by the level sets of its prime factor

A sup bound for a prime polynomial on a whole frequency annulus is false once the block is short:
by Kronecker the phases `p^{-2πiw}` align somewhere in every long enough range, so
`‖∑_{p ∈ B} μ(p) p^{-2πiw}‖` reaches `#B`.  What survives is that such frequencies are rare, and the
form that consumes rarity rather than a sup bound is the dyadic level split: the mean square of the
product is the base level times the cofactor's mean square, plus one term per dyadic level carrying
the cofactor's mean square over the set where the prime polynomial is that large.

This is the interface the Halász--Montgomery large-values estimates plug into.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

theorem measurable_norm_primeBlockPoly (B : Finset ℕ) :
    Measurable fun w : ℝ => ‖primeBlockPoly B w‖ :=
  (continuous_primeBlockPoly B).norm.measurable

/-- **One block, split by the level sets of the prime polynomial.** -/
theorem integral_normSq_blockProduct_levelSplit (a : ℕ → ℂ) (B D : Finset ℕ) {G : ℝ}
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ} (hJ : ((B.card : ℕ) : ℝ) ≤ 2 ^ J * V₀) :
    (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      ≤ V₀ ^ (2 : ℕ) * (∫ w in Set.Icc (-G) G, ‖logPoly a D w‖ ^ (2 : ℕ))
        + ∑ j ∈ Finset.range J,
            (2 ^ (j + 1) * V₀) ^ (2 : ℕ)
              * ∫ w in Set.Icc (-G) G ∩ {w | 2 ^ j * V₀ ≤ ‖primeBlockPoly B w‖},
                  ‖logPoly a D w‖ ^ (2 : ℕ) := by
  classical
  have hcontP : Continuous fun w : ℝ => ‖primeBlockPoly B w‖ :=
    (continuous_primeBlockPoly B).norm
  have hcontC : Continuous fun w : ℝ => ‖logPoly a D w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly a D).norm).pow 2
  have hrw : (∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (-G) G, ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [norm_mul, mul_pow]
  rw [hrw]
  exact integral_sq_mul_le_levelSplit measurableSet_Icc hcontP.measurable
    ((hcontP.pow 2).mul hcontC).integrableOn_Icc hcontC.integrableOn_Icc
    (fun w => norm_nonneg _) (fun w => by positivity) hV₀
    (fun w => norm_primeBlockPoly_le_card B w) hJ

end

end RHTower.Sieve
