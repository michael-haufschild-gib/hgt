import GaloisForLFunctions.RHTower.Sieve.VaughanIdentity
import GaloisForLFunctions.RHTower.Sieve.ZetaConvolutionTypeI

/-!
# Vaughan's identity on a block above the truncation

Above `U` the first term of Vaughan's identity drops out, so a von Mangoldt sum against any weight
splits into exactly three convolution sums: two type-I and one type-II.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **Vaughan's identity, summed against a weight over a block above `U`.** -/
theorem sum_vonMangoldt_block_decomp {U V A B : ℕ} (hUA : U < A) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * w n)
      = -(∑ n ∈ Finset.Ico A B,
            ((((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U
                * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ) * w n)
        + (∑ n ∈ Finset.Ico A B,
            (((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) n : ℝ) : ℂ)
              * w n)
        + ∑ n ∈ Finset.Ico A B,
            ((((vonMangoldt - truncAF vonMangoldt U)
                * (1 - (zeta : ArithmeticFunction ℝ)
                    * truncAF (moebius : ArithmeticFunction ℝ) V)) n : ℝ) : ℂ) * w n := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  have hUn : U < n := lt_of_lt_of_le hUA hn.1
  have hval := vaughan_apply_of_gt (U := U) (V := V) hUn
  rw [hval]
  push_cast
  ring

end

end RHTower.Sieve
