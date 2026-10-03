import GaloisForLFunctions.RHTower.QuadraticResidueHalfExcess
import GaloisForLFunctions.HTGeometry.StonehamPrimeDriftLaw

/-!
# The parity drift of the Stoneham constants `α_{2,p}`, `p ≡ 3 (mod 8)`, is unbounded

For a prime `p ≡ 3 (mod 8)` such that `2` is a primitive root modulo `p²`, the parity drift of
`α_p = Σ_{j ≥ 1} p^{−j} 2^{−p^j}` at the window ends is `p k Σ_{0<r<p/2} (r/p)`
(`drift_stonehamP_windowEnd`), and Dirichlet's theorem `Σ_{0<r<p/2} (r/p) > 0`
(`sum_legendreSym_half_pos`) makes the slope positive.  Hence the drift tends to `+∞` along the
window ends, although `α_p` is normal in base `2`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.RHTower.QuadraticResidueExcess

open GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
open GaloisForLFunctions.HTGeometry.BinaryParityDrift

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Linear lower bound.**  `D_{α_p}((p^{k+1} + 1)/2) ≥ p k`. -/
theorem le_drift_stonehamP_windowEnd (hp8 : p % 8 = 3)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) (k : ℕ) :
    (p * k : ℤ) ≤ drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) := by
  rw [drift_stonehamP_windowEnd hp8 hord hwief k]
  have hS := sum_legendreSym_half_pos (p := p) (by omega)
  have : (0 : ℤ) ≤ p * k := by positivity
  nlinarith

/-- **The drift of `α_p` is unbounded.** -/
theorem tendsto_drift_stonehamP_windowEnd (hp8 : p % 8 = 3)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) :
    Tendsto (fun k => drift (stonehamP p) ((p ^ (k + 1) + 1) / 2)) atTop atTop := by
  refine tendsto_atTop_mono (fun k => le_drift_stonehamP_windowEnd hp8 hord hwief k) ?_
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
  have : (0 : ℤ) ≤ k := by positivity
  nlinarith

end GaloisForLFunctions.RHTower.QuadraticResidueExcess
