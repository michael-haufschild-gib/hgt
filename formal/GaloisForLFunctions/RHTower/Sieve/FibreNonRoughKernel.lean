import GaloisForLFunctions.RHTower.Sieve.FibreNonRoughSpectral
import GaloisForLFunctions.RHTower.Sieve.LogWindowPlancherel

/-!
# The Turán–Kubilius-free bound in kernel form

Plancherel turns the window `L²` norm into the kernel-weighted mean square of the Dirichlet
polynomial, which is the shape the corpus's majorant machinery consumes.  Against
`Sieve/OmegaSpectralFibre.sum_sq_fibreSum_moebius_le_omegaSpectral` the differences are that the
polynomial carries the unit-bounded weight `nonRoughMoebius` rather than `μ·ω_P`, that there is no
`(mertensS z − mertensS z₀)²` dividing the left side, and that the sieve error appears squared
instead of a Turán–Kubilius variance appearing linearly.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The fibre mean square against the kernel-weighted polynomial, with no `1/W²`.** -/
theorem sum_sq_fibreSum_moebius_le_nonRough_kernel {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z r : ℕ} (hz : 2 ≤ z) (hr : Even r) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
                * ‖logPoly (fun n => ((nonRoughMoebius (Nat.primesLE z) n : ℝ) : ℂ))
                    (fibreIndex x h) w‖ ^ 2)
        + 204 * (Real.sqrt x + 1)
        + 2 * ((outerBlock x h).card : ℝ) * (fibreRamareSieveError h z r lam) ^ 2 := by
  have hbase := sum_sq_fibreSum_moebius_le_nonRough_spectral hx hh0 hhx hz hr hlam
  have hplanch : (∫ u : ℝ, ‖logWindowSum
        (fun n => ((nonRoughMoebius (Nat.primesLE z) n : ℝ) : ℂ))
        (fibreIndex x h) (fibreWidth x h) u‖ ^ 2)
      = ∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
          * ‖logPoly (fun n => ((nonRoughMoebius (Nat.primesLE z) n : ℝ) : ℂ))
              (fibreIndex x h) w‖ ^ 2 :=
    integral_normSq_logWindowSum_eq _ _ (fibreWidth_nonneg hx hh0)
  rw [hplanch] at hbase
  linarith [hbase]

end

end RHTower.Sieve
