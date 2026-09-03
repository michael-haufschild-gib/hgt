import GaloisForLFunctions.RHTower.PrimeCpowAbsoluteAbscissa
import GaloisForLFunctions.RHTower.SquarefreeConvolutionDyadicTower

/-!
# Absolute-convergence wall for convolution dyadic roots

Every finite stage of the canonical dyadic convolution-root tower has prime coefficient
`2⁻ⁿ`. Therefore its norm Dirichlet series cannot be summable on or to the left of
`Re s = 1`: restriction to prime indices and rescaling would make the prime complex-power
series summable there.

In particular, the canonical convolution half cannot itself define the requested analytic
half-divisor on `Re s > 1/2` by an absolutely convergent Dirichlet series. Any successful
construction must supply genuine continuation or renormalization beyond the Euler chamber.
-/

open ArithmeticFunction
open scoped Moebius ArithmeticFunction.zeta

noncomputable section

namespace RHTower

open Complex

/-- Every finite dyadic coefficient-root stage fails absolute Dirichlet summability when
`Re s ≤ 1`. The prime subseries already gives the obstruction. -/
theorem
    not_summable_norm_squarefreeConvolutionDyadicRootTower_cpow_of_re_le_one
    (n : ℕ) {s : ℂ} (hs : s.re ≤ 1) :
    ¬ Summable (fun m : ℕ =>
      ‖squarefreeConvolutionDyadicRootTower n m * (m : ℂ) ^ (-s)‖) := by
  intro hsum
  apply
    GaloisForLFunctions.RHTower.not_summable_norm_primeCpow_neg_of_re_le_one hs
  have hprime := hsum.subtype Nat.Prime
  have hscaled := hprime.mul_left ((2 : ℝ) ^ n)
  refine hscaled.congr ?_
  intro p
  change (2 : ℝ) ^ n *
      ‖squarefreeConvolutionDyadicRootTower n (p : ℕ) *
        ((p : ℕ) : ℂ) ^ (-s)‖ =
    ‖((p : ℕ) : ℂ) ^ (-s)‖
  rw [squarefreeConvolutionDyadicRootTower_apply_prime p.property n,
    norm_mul, norm_div, norm_one, norm_pow]
  norm_num

/-- The report's canonical convolution half already meets the same absolute-convergence wall. -/
theorem not_summable_norm_squarefreeConvolutionHalf_cpow_of_re_le_one
    {s : ℂ} (hs : s.re ≤ 1) :
    ¬ Summable (fun m : ℕ =>
      ‖squarefreeConvolutionHalf m * (m : ℂ) ^ (-s)‖) := by
  simpa [squarefreeConvolutionDyadicRootTower, convolutionDyadicRootTower,
    squarefreeConvolutionHalf] using
    not_summable_norm_squarefreeConvolutionDyadicRootTower_cpow_of_re_le_one 1 hs

end RHTower
