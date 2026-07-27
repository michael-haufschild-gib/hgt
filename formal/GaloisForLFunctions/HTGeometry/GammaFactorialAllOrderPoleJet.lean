import GaloisForLFunctions.HTGeometry.GammaFactorialExponentialEnvelopeEscape

/-!
# Exact all-order pole jets of the Gamma factorial microscope

The first three pole-jet layers were previously expanded separately.  This file closes the exact
finite-order ladder.  For every polygamma order `m`, the scaled jet at `-n+sₙx` is the reciprocal
principal jet plus `sₙ^(m+1)` times a regular local polygamma value and a shifted generalized
harmonic sum.

This is the algebraic source of the harmonic-zeta bifiltration: at `z=0`, the local value is
`(-1)^(m+1)m!ζ(m+1)` while the shifted sum tends `m!ζ(m+1)`.  They reinforce in odd polygamma order
and cancel in even order, where the finite Euler-product tail becomes the next datum.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

open scoped BigOperators

theorem shiftedHarmonicPowerSum_two (n : ℕ) (z : ℂ) :
    shiftedHarmonicPowerSum 2 n z = shiftedHarmonicSquareSum n z := by
  rw [shiftedHarmonicPowerSum, shiftedHarmonicSquareSum]

theorem shiftedHarmonicPowerSum_three (n : ℕ) (z : ℂ) :
    shiftedHarmonicPowerSum 3 n z = shiftedHarmonicCubeSum n z := by
  rw [shiftedHarmonicPowerSum, shiftedHarmonicCubeSum]

/-- Exact all-order decomposition into the reciprocal principal jet and the regular shifted tail. -/
theorem gammaFactorialScaledPolygamma_eq_principal_add
    (m n : ℕ) {x : ℂ} (hx : x ≠ 0)
    (hregular : ∀ k : ℤ,
      reciprocalGammaFactorialScale n * x ≠ (k : ℂ)) :
    gammaFactorialScaledPolygamma m n x =
      (-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) / x ^ (m + 1) +
        reciprocalGammaFactorialScale n ^ (m + 1) *
          (iteratedDeriv m Complex.digamma
              (1 + reciprocalGammaFactorialScale n * x) +
            (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n
              (reciprocalGammaFactorialScale n * x)) := by
  rw [gammaFactorialScaledPolygamma]
  rw [iteratedDeriv_digamma_neg_nat_add_of_ne_int m
    (reciprocalGammaFactorialScale n * x) hregular n]
  have hs : reciprocalGammaFactorialScale n ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  have hscale :
      reciprocalGammaFactorialScale n ^ (m + 1) *
          (reciprocalGammaFactorialScale n * x)⁻¹ ^ (m + 1) =
        x⁻¹ ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp [hs, hx]
  rw [mul_add, mul_add]
  rw [show reciprocalGammaFactorialScale n ^ (m + 1) *
          ((-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) *
            (reciprocalGammaFactorialScale n * x)⁻¹ ^ (m + 1)) =
        (-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) * x⁻¹ ^ (m + 1) by
      rw [← hscale]
      ring]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem gammaFactorialScaledPolygamma_one
    (n : ℕ) (x : ℂ) :
    gammaFactorialScaledPolygamma 1 n x =
      gammaFactorialScaledTrigamma n x := by
  rw [gammaFactorialScaledPolygamma, gammaFactorialScaledTrigamma]

theorem gammaFactorialScaledPolygamma_two
    (n : ℕ) (x : ℂ) :
    gammaFactorialScaledPolygamma 2 n x =
      gammaFactorialScaledSecondPolygamma n x := by
  rw [gammaFactorialScaledPolygamma, gammaFactorialScaledSecondPolygamma]

end

end GaloisForLFunctions
