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

def shiftedHarmonicPowerSum (p n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ p)⁻¹

theorem shiftedHarmonicPowerSum_two (n : ℕ) (z : ℂ) :
    shiftedHarmonicPowerSum 2 n z = shiftedHarmonicSquareSum n z := by
  rw [shiftedHarmonicPowerSum, shiftedHarmonicSquareSum]

theorem shiftedHarmonicPowerSum_three (n : ℕ) (z : ℂ) :
    shiftedHarmonicPowerSum 3 n z = shiftedHarmonicCubeSum n z := by
  rw [shiftedHarmonicPowerSum, shiftedHarmonicCubeSum]

theorem neg_negOnePow_factorial_div_negPow
    (m : ℕ) {u : ℂ} (hu : u ≠ 0) :
    -((-1 : ℂ) ^ m * (m.factorial : ℂ) / (-u) ^ (m + 1)) =
      (m.factorial : ℂ) / u ^ (m + 1) := by
  rw [show (-u) ^ (m + 1) = (-1 : ℂ) ^ (m + 1) * u ^ (m + 1) by
    rw [neg_pow]]
  field_simp [hu]
  rw [pow_succ]
  ring

/-- Exact all-order differentiated-digamma shift from `-n+z` to `1+z`. -/
theorem iteratedDeriv_digamma_neg_nat_add_of_ne_int
    (m : ℕ) (z : ℂ) (hz : ∀ k : ℤ, z ≠ (k : ℂ)) (n : ℕ) :
    iteratedDeriv m Complex.digamma (-(n : ℂ) + z) =
      iteratedDeriv m Complex.digamma (1 + z) +
        (-1 : ℂ) ^ (m + 1) * (m.factorial : ℂ) / z ^ (m + 1) +
        (m.factorial : ℂ) * shiftedHarmonicPowerSum (m + 1) n z := by
  induction n with
  | zero =>
      have hzOff : ∀ k : ℕ, z ≠ -(k : ℂ) := by
        intro k
        simpa using hz (-(k : ℤ))
      have hstep := digammaJet_shift m hzOff
      simp only [Nat.cast_zero, neg_zero, zero_add, shiftedHarmonicPowerSum,
        Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      rw [show (1 + z : ℂ) = z + 1 by ring, hstep]
      have hsign : -((-1 : ℂ) ^ m) = (-1 : ℂ) ^ (m + 1) := by
        rw [pow_succ]
        ring
      rw [← hsign]
      ring
  | succ n ih =>
      let w : ℂ := -((n + 1 : ℕ) : ℂ) + z
      have hw : ∀ k : ℕ, w ≠ -(k : ℂ) := by
        intro k hwk
        apply hz ((n : ℤ) + 1 - (k : ℤ))
        dsimp [w] at hwk
        norm_num [Int.cast_sub, Int.cast_add]
        push_cast at hwk ⊢
        linear_combination hwk
      have hstep := digammaJet_shift m hw
      have hwadd : w + 1 = -(n : ℂ) + z := by
        dsimp [w]
        push_cast
        ring
      let u : ℂ := ((n + 1 : ℕ) : ℂ) - z
      have hwu : w = -u := by
        dsimp [w, u]
        ring
      have hu : u ≠ 0 := by
        intro h
        apply hz (n + 1)
        exact (sub_eq_zero.mp h).symm
      change iteratedDeriv m Complex.digamma w = _
      have hsolve : iteratedDeriv m Complex.digamma w =
          iteratedDeriv m Complex.digamma (w + 1) +
            (m.factorial : ℂ) / u ^ (m + 1) := by
        have hbase : iteratedDeriv m Complex.digamma w =
            iteratedDeriv m Complex.digamma (w + 1) -
              (-1 : ℂ) ^ m * (m.factorial : ℂ) / w ^ (m + 1) := by
          linear_combination -hstep
        rw [hbase, hwu, sub_eq_add_neg,
          neg_negOnePow_factorial_div_negPow m hu]
      rw [hsolve, hwadd, ih]
      simp only [shiftedHarmonicPowerSum, Finset.sum_range_succ]
      dsimp [u]
      ring

def gammaFactorialScaledPolygamma (m n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n ^ (m + 1) *
    iteratedDeriv m Complex.digamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

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
  field_simp [hs, hx]
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
