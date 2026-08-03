import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport

/-!
# The transport cost of a bounded-displacement matching

The damped displacement cost of a family of edges is at most `#s · x · H` once every edge moves no
further than `H`, because the damping factor `exp(-min(u,v)·x)` never exceeds one on nonnegative
data:

`finiteDampedLaplaceTransportCost s u v x ≤ #s · (x · H)`.

With `#s = O(X)` edges across a dyadic shell and `x ≍ X⁻¹` this is `O(H)`, the card's cost claim.
-/

namespace RHTower.Sieve

open Finset

/-- **The aggregate transport cost of a bounded-displacement matching.** -/
theorem finiteDampedLaplaceTransportCost_le {ι : Type*} (s : Finset ι) (u v : ι → ℝ) {x H : ℝ}
    (hx : 0 ≤ x) (hH : ∀ i ∈ s, |u i - v i| ≤ H) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hv : ∀ i ∈ s, 0 ≤ v i) :
    RHTower.finiteDampedLaplaceTransportCost s u v x ≤ (s.card : ℝ) * (x * H) := by
  classical
  rw [RHTower.finiteDampedLaplaceTransportCost]
  have hterm : ∀ i ∈ s,
      x * |u i - v i| * Real.exp (-(min (u i) (v i) * x)) ≤ x * H := by
    intro i hi
    have hmin : 0 ≤ min (u i) (v i) := le_min (hu i hi) (hv i hi)
    have hexp : Real.exp (-(min (u i) (v i) * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ min (u i) (v i) * x := mul_nonneg hmin hx
      linarith
    have hxd : 0 ≤ x * |u i - v i| := by positivity
    calc x * |u i - v i| * Real.exp (-(min (u i) (v i) * x))
        ≤ x * |u i - v i| * 1 := mul_le_mul_of_nonneg_left hexp hxd
      _ = x * |u i - v i| := by ring
      _ ≤ x * H := mul_le_mul_of_nonneg_left (hH i hi) hx
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

end RHTower.Sieve
