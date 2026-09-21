import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalBidirectionalTransportRangeNoGo

/-!
# Exact multiplicative locality wall for the critical CCM-FU source

The literal completed Mertens--polar source has a positive prime impulse. A
contiguous two-sided block can offset it only by logarithmic polar drift. This
module retains that drift in its exact multiplicative form, rather than the
coarser additive radius estimate. Every source-faithful growing-memory
producer must satisfy this wall before it can attempt the RH-bearing uniform
triangular bound.
-/

open Filter

namespace RHTower

noncomputable section

/-- Exact multiplicative locality wall for a nonpositive literal critical block. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_exact_log_wall
    {p L R : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) (hleft : L + 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0) :
    Real.exp (Real.log (p : ℝ) / (2 * p)) ≤
      (((p - 1 : ℕ) : ℝ) * ((p + R : ℕ) : ℝ)) /
        (((p - L - 1 : ℕ) : ℝ) * (p : ℝ)) := by
  have hspan :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_log_span
      hp hp27 hleft hblock
  have hp0 : (0 : ℝ) < p := by positivity
  have hpm1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hpLm1 : (0 : ℝ) < ((p - L - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - L - 1 by omega)
  have hpR : (0 : ℝ) < ((p + R : ℕ) : ℝ) := by positivity
  have hexp := Real.exp_le_exp.mpr hspan
  rw [Real.exp_add, Real.exp_sub, Real.exp_sub,
    Real.exp_log hpm1, Real.exp_log hpLm1,
    Real.exp_log hpR, Real.exp_log hp0] at hexp
  calc
    Real.exp (Real.log (p : ℝ) / (2 * p)) ≤
        ((p - 1 : ℕ) : ℝ) / ((p - L - 1 : ℕ) : ℝ) *
          (((p + R : ℕ) : ℝ) / (p : ℝ)) := hexp
    _ = (((p - 1 : ℕ) : ℝ) * ((p + R : ℕ) : ℝ)) /
        (((p - L - 1 : ℕ) : ℝ) * (p : ℝ)) := by ring

end

end RHTower
