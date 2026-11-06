import GaloisForLFunctions.RHTower.Representation.PositiveEndpointCharacter
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMomentDerivatives

/-!
# Endpoint cycle values from the completed arithmetic response

All normalized endpoint power sums are derivatives at `X = 1/4` of
`logDeriv xi (1/2 + sqrt X) / sqrt X`. This defines the prescribed cycle values without using
the zero divisor. The resolvent identities establish their exact agreement with the divisor
moments; they do not establish positivity.
-/

noncomputable section
open Filter Topology

namespace RHTower

theorem xiResolventPoint_endpoint (q : XiZeroCopy) :
    xiResolventPoint (1 / 4) q = xiStripEdgeWeight q := by
  rw [xiResolventPoint, xiStripEdgeWeight_eq_spectral, add_comm]
  push_cast
  rfl

theorem xiEndpointSourceCycle_eq_resolvent (n : ℕ) :
    xiEndpointSourceCycle n =
      (xiResolventMoment n (1 / 4)).re / xiEndpointColorMass ^ (n + 1) := by
  simp only [xiEndpointSourceCycle, xiResolventMoment, xiResolventPoint_endpoint]

/-- The completed Euler-ray response in the squared shift coordinate. -/
def xiEndpointEulerResponse (X : ℝ) : ℂ :=
  logDeriv xi ((1 / 2 : ℂ) + (Real.sqrt X : ℂ)) / (Real.sqrt X : ℂ)

theorem xiEndpointEulerResponse_eq_resolvent {X : ℝ} (hX : 0 < X) :
    xiEndpointEulerResponse X = xiResolventMoment 0 X := by
  have h := xiResolventMoment_zero_eq_logDeriv (Real.sqrt_pos.mpr hX)
  rw [Real.sq_sqrt hX.le] at h
  exact h.symm

/-- Every resolvent moment is recovered from the arithmetic response by differentiation. -/
theorem iteratedDeriv_xiEndpointEulerResponse (n : ℕ) {X : ℝ} (hX : 0 < X) :
    iteratedDeriv n xiEndpointEulerResponse X =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * xiResolventMoment n X := by
  have heq : xiEndpointEulerResponse =ᶠ[𝓝 X] (fun v => xiResolventMoment 0 v) := by
    filter_upwards [Ioi_mem_nhds hX] with v hv
    exact xiEndpointEulerResponse_eq_resolvent hv
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_xiResolventMoment_zero n hX]

/-- The prescribed `(n+1)`-cycle value, defined entirely from completed arithmetic jets. -/
def xiEndpointArithmeticCycle (n : ℕ) : ℝ :=
  (((-1 : ℂ) ^ n / (n.factorial : ℂ)) *
    iteratedDeriv n xiEndpointEulerResponse (1 / 4)).re / poleSharpConstant ^ (n + 1)

/-- Exact arithmetic identification of every normalized endpoint cycle value. -/
theorem xiEndpointArithmeticCycle_eq_source (n : ℕ) :
    xiEndpointArithmeticCycle n = xiEndpointSourceCycle n := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hmoment : ((-1 : ℂ) ^ n / (n.factorial : ℂ)) *
      iteratedDeriv n xiEndpointEulerResponse (1 / 4) = xiResolventMoment n (1 / 4) := by
    rw [iteratedDeriv_xiEndpointEulerResponse n (by positivity)]
    calc
      _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          ((n.factorial : ℂ) / (n.factorial : ℂ)) * xiResolventMoment n (1 / 4) := by ring
      _ = _ := by rw [hsign, div_self hfac, one_mul, one_mul]
  rw [xiEndpointArithmeticCycle, hmoment, ← xiEndpointColorMass_eq,
    xiEndpointSourceCycle_eq_resolvent]

end RHTower
