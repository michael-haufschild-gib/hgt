import GaloisForLFunctions.RHTower.Sieve.GapWeightedPairSum
import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.RHTower.HarmonicTriangularProjection
import GaloisForLFunctions.RHTower.FloorTransformWienerClass

/-!
# The three gap sums

The off-diagonal total is fed by `Σ_{h ≤ H} √h`, `Σ_{h ≤ H} h^{-1/2}` and `Σ_{h ≤ H} h^{-1}`.  The
last two are corpus-owned (`SqrtTelescopeSums`, `FloorTransformWienerClass`); only the first is new,
and it is trivial.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- `invSum` of `DivisorSquareMoment.lean` is the corpus's `harmonicSum`. -/
theorem invSum_eq_harmonicSum (N : ℕ) : invSum N = RHTower.harmonicSum N := rfl

/-- The harmonic gap sum. -/
theorem invSum_le_one_add_log {N : ℕ} (hN : 1 ≤ N) :
    invSum N ≤ 1 + Real.log N := by
  rw [invSum_eq_harmonicSum]
  exact RHTower.harmonicSum_le_one_add_log hN

/-- The square-root gap sum. -/
theorem sum_sqrt_le (H : ℕ) :
    (∑ h ∈ Finset.Icc 1 H, Real.sqrt h) ≤ (H : ℝ) * Real.sqrt H := by
  have hstep : ∀ h ∈ Finset.Icc 1 H, Real.sqrt h ≤ Real.sqrt H := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact Real.sqrt_le_sqrt (by exact_mod_cast hh.2)
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcast : ((H + 1 - 1 : ℕ) : ℝ) = (H : ℝ) := by push_cast; ring
  rw [hcast]

/-- The reciprocal square-root gap sum, from the corpus's telescope. -/
theorem sum_inv_sqrt_gap_le (H : ℕ) :
    (∑ h ∈ Finset.Icc 1 H, 1 / Real.sqrt h) ≤ 2 * Real.sqrt H :=
  RHTower.sum_inv_sqrt_le H

end

end RHTower.Sieve
