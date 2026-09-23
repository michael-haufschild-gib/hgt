import GaloisForLFunctions.RHTower.Sieve.FibreBilinearCapstone
import GaloisForLFunctions.RHTower.Sieve.RamareBilinearMeanSquare

/-!
# The fibre capstone in the corpus's `ramareBilinear` notation

`fibreIndex x h` is `Finset.Icc 1 ⌊√x + h⌋₊`, which is exactly the index range
`Sieve/RamareBilinearMeanSquare.ramareBilinear` is defined over.  The capstone's integrand is
therefore literally `‖ramareBilinear (primesLE z) ⌊√x + h⌋₊ w‖²`, so the block-splitting and
geometric-ladder machinery of `Sieve/RamareBlockSplit` applies to it unchanged.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The Route E fibre mean square against `ramareBilinear`.** -/
theorem sum_sq_fibreSum_moebius_le_ramareBilinear_ladder {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ (2 : ℕ)
                * ‖ramareBilinear (Nat.primesLE z) ⌊Real.sqrt x + h⌋₊ w‖ ^ (2 : ℕ))
        + 204 * (Real.sqrt x + 1)
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ (2 : ℕ) := by
  have hbase := sum_sq_fibreSum_moebius_le_bilinear_kernel_exact hx hh0 hhx hz hr hlam
  have hid : ∀ w : ℝ,
      (∑ p ∈ Nat.primesLE z, moebiusPhase w p
          * logPoly (ramareCofactorCoeff (Nat.primesLE z))
              {m ∈ ramareCofactorSet (fibreIndex x h) p | ¬ p ∣ m} w)
        = ramareBilinear (Nat.primesLE z) ⌊Real.sqrt x + h⌋₊ w := by
    intro w
    rw [ramareBilinear, fibreIndex]
  simp only [hid] at hbase
  exact hbase

end

end RHTower.Sieve
