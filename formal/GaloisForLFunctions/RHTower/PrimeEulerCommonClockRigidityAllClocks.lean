import GaloisForLFunctions.RHTower.PrimeEulerCommonClockRigidity
import GaloisForLFunctions.RHTower.WindowBudgetUnconditionalSupply

/-!
# Common-clock primewise reflection rigidity at every clock

`PrimeEulerCommonClockRigidity` pins the strip displacement to zero from primewise
reflected-modulus neutrality under one common clock, against the window-supply interface;
its unconditional form was restricted to clocks below `π/(2·log 2)` (Bertrand).  The
unconditional every-length window supply discharges the interface at every positive clock:
common-clock primewise reflection rigidity holds unconditionally for EVERY `τ > 0`.
-/

namespace RHTower

/-- **Unconditional common-clock primewise reflection rigidity at every clock.**  If every
prime Euler denominator is reflected-modulus neutral under one common clock `τ > 0`, the
strip displacement is zero — with no restriction on the clock. -/
theorem epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral_all_clocks
    {epsilon tau : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (htau : 0 < tau)
    (hneutral : ∀ p : ℕ, Nat.Prime p →
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 + epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 - epsilon) : ℝ) : ℂ) *
          Complex.exp (((tau * Real.log p : ℝ) : ℂ) * Complex.I)‖) :
    epsilon = 0 :=
  epsilon_eq_zero_of_cofinal_prime_reflected_modulus_neutral hepsilon0 hepsilonHalf htau
    (primeWindowSupply_of_pos (by positivity)) hneutral

end RHTower
