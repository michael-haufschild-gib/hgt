/-
The hierarchical small-ball interface for the Steinhaus field: the
block-conditional anti-concentration predicate that the graded induction
consumes, with `three_phase_sublevel_r2log` as its three-phase floor.
`BlockSmallBall a s bound` asserts anti-concentration of the block sum
`w + Σ_{n ∈ s} a n · X n` uniformly in the conditioning value `w`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.SteinhausModel
import GaloisForLFunctions.RHTower.RouteBThreePhaseLog

namespace RHTower

open MeasureTheory

/-- Block-conditional small-ball bound: uniformly over the conditioned
value `w` of all other blocks, the block sum concentrates no mass in any
ball of radius `t` beyond `bound t`. -/
def BlockSmallBall (a : ℕ → ℝ) (s : Finset ℕ) (bound : ℝ → ℝ) : Prop :=
  ∀ w : ℂ, ∀ t : ℝ, 0 < t →
    steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t}
      ≤ ENNReal.ofReal (bound t)

/-- Monotonicity in the rate function. -/
theorem BlockSmallBall.mono {a : ℕ → ℝ} {s : Finset ℕ}
    {bound bound' : ℝ → ℝ} (h : BlockSmallBall a s bound)
    (hb : ∀ t, 0 < t → bound t ≤ bound' t) :
    BlockSmallBall a s bound' := fun w t ht =>
  le_trans (h w t ht) (ENNReal.ofReal_le_ofReal (hb t ht))

/-- Small-ball bounds transfer along subset targets. -/
theorem BlockSmallBall.of_le {a : ℕ → ℝ} {s : Finset ℕ}
    {bound : ℝ → ℝ} (h : BlockSmallBall a s bound)
    {w : ℂ} {t t' : ℝ} (ht : 0 < t) (htt : t' ≤ t) :
    steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t'}
      ≤ ENNReal.ofReal (bound t) :=
  le_trans (measure_mono (fun ω hω => le_trans hω htt)) (h w t ht)

end RHTower
