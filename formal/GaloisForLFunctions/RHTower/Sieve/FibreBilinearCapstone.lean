import GaloisForLFunctions.RHTower.Sieve.NonRoughBilinearExact
import GaloisForLFunctions.RHTower.Sieve.FibreNonRoughKernel

/-!
# The Route E fibre mean square on a genuine bilinear form

Assembling the exact Ramaré factorisation with the rough split and Plancherel: the short-interval
input of the Route E cards is bounded by the kernel-weighted mean square of a designated-prime times
cofactor bilinear form, plus a sieve error that appears squared.

Against `Sieve/OmegaSpectralFibre.sum_sq_fibreSum_moebius_le_omegaSpectral` there is no
`(mertensS z − mertensS z₀)²` dividing the left side and no Turán–Kubilius variance on the right,
so the achievable rate is no longer capped at `1/log log x`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The Route E fibre mean square against the Ramaré bilinear form.** -/
theorem sum_sq_fibreSum_moebius_le_bilinear_kernel_exact {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
                * ‖∑ p ∈ Nat.primesLE z, moebiusPhase w p
                    * logPoly (ramareCofactorCoeff (Nat.primesLE z))
                        {m ∈ ramareCofactorSet (fibreIndex x h) p | ¬ p ∣ m} w‖ ^ 2)
        + 204 * (Real.sqrt x + 1)
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ 2 := by
  have hPprime : ∀ q ∈ Nat.primesLE z, q.Prime := fun q hq => Nat.prime_of_mem_primesLE hq
  have hbase := sum_sq_fibreSum_moebius_le_nonRough_kernel hx hh0 hhx hz hr hlam
  have hpoly : ∀ w : ℝ,
      ‖logPoly (fun n => ((nonRoughMoebius (Nat.primesLE z) n : ℝ) : ℂ))
          (fibreIndex x h) w‖ ^ 2
        = ‖∑ p ∈ Nat.primesLE z, moebiusPhase w p
            * logPoly (ramareCofactorCoeff (Nat.primesLE z))
                {m ∈ ramareCofactorSet (fibreIndex x h) p | ¬ p ∣ m} w‖ ^ 2 := by
    intro w
    rw [logPoly_nonRoughMoebius_eq_ramare_bilinear hPprime]
  simp only [hpoly] at hbase
  exact hbase

end

end RHTower.Sieve
