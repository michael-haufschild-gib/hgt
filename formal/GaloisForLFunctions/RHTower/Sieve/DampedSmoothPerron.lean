import GaloisForLFunctions.RHTower.Sieve.DampedEulerIdentity
import GaloisForLFunctions.HTGeometry.SmoothWeightPerron

/-!
# The smoothed Perron formula for the damped Möbius series

`HTGeometry.SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral` is already generic in the
coefficients: it needs only that they are unit-bounded and vanish at `0`.  The damped Möbius
coefficients satisfy both, so the smoothed damped sum is the vertical integral of the damped
Dirichlet series against the Mellin transform of the cutoff.

This is the first of the two `μ`-specific inputs of
`Sieve/PerronEdgeAssembly.norm_tsum_moebius_smoothWeight_le_edges`; the other is the rectangle
identity, which follows for the damped series because
`Sieve/DampedEulerIdentity.tsum_damped_eq_prod_mul_tsum_moebius` exhibits it as `invZeta` times a
finite product of factors holomorphic on `Re s > 0`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex GaloisForLFunctions.HTGeometry

noncomputable section

/-- The damped coefficient vanishes at zero. -/
theorem dampedOmegaMoebius_zero (P : Finset ℕ) (t : ℝ) : dampedOmegaMoebius P t 0 = 0 := by
  rw [dampedOmegaMoebius, ArithmeticFunction.map_zero]
  push_cast
  ring

/-- **The smoothed Perron formula for the damped series.** -/
theorem tsum_dampedOmegaMoebius_smoothWeight_eq_integral {P : Finset ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        dampedOmegaMoebius P t n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (∑' n : ℕ,
            dampedOmegaMoebius P t n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)))
          * mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) :=
  tsum_mul_smoothWeight_eq_integral (a := dampedOmegaMoebius P t)
    (fun n => norm_dampedOmegaMoebius_le_one ht0 ht1 n) (dampedOmegaMoebius_zero P t) hN hH hσ

end

end RHTower.Sieve
