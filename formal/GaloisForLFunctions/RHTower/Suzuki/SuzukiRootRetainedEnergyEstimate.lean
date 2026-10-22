import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The unweighted boundary-log energy estimate

Pairing the carrier equation with the derivative it solves for turns three separate facts into a
bound on that derivative:

* the position term is coercive — on a terminal ray `2L ≥ 2L₀`;
* the jump multiplier is accretive at the unweighted endpoint — `Re⟪R u, u⟫ ≥ 0`;
* the adjacency is bounded — `‖T u‖ ≤ τ‖u‖`.

Their conjunction gives `(2L₀ − τ)‖E'‖ ≤ ‖forcing‖` with no weight, no compression inverse, and no
sign hypothesis on the adjacency: the jump term is discarded on the correct side of the inequality
and the adjacency is spent against the position gap.  Everything is stated for the three paired
values, so the estimate applies verbatim to a cut-off equation, where the residual simply joins the
forcing.

The forced equation itself is exact algebra: subtracting the prime equation from the carrier
equation leaves the jump applied to the prime derivative as the only source.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The exact forced equation -/

omit [InnerProductSpace ℂ H] in
/-- **The forced Gamma equation.**  If the carrier solves `(2L·I + R − T)F' + F = 0` and the prime
profile solves `(2L·I − T)Π' + Π = 0`, then their difference solves the same equation forced by the
jump applied to the prime derivative alone. -/
theorem forced_difference_equation {carrierPos carrierJump carrierAdj carrier : H}
    {primePos primeAdj prime primeJump : H}
    (hF : carrierPos + carrierJump - carrierAdj + carrier = 0)
    (hPi : primePos - primeAdj + prime = 0) :
    (carrierPos - primePos) + (carrierJump - primeJump) - (carrierAdj - primeAdj)
        + (carrier - prime)
      = -primeJump := by
  have h : carrierPos + carrierJump - carrierAdj + carrier
      - (primePos - primeAdj + prime) = 0 - 0 := by
    rw [hF, hPi]
  linear_combination (norm := module) h

/-! ## The energy estimate -/

/-- **The unweighted energy estimate.**  Coercivity of the position term, accretivity of the jump
term and boundedness of the adjacency give a bound on the paired vector with the explicit constant
`(μ − τ)⁻¹`. -/
theorem energy_estimate {v w positionTerm jumpTerm adjacencyTerm : H} {μ τ : ℝ}
    (hM : μ * ‖v‖ ^ (2 : ℕ) ≤ (inner ℂ positionTerm v).re)
    (hR : 0 ≤ (inner ℂ jumpTerm v).re)
    (hT : ‖adjacencyTerm‖ ≤ τ * ‖v‖)
    (heq : positionTerm + jumpTerm - adjacencyTerm = w) :
    (μ - τ) * ‖v‖ ≤ ‖w‖ := by
  have hsplit : (inner ℂ w v).re
      = (inner ℂ positionTerm v).re + (inner ℂ jumpTerm v).re
        - (inner ℂ adjacencyTerm v).re := by
    rw [← heq, inner_sub_left, inner_add_left]
    simp [Complex.add_re, Complex.sub_re]
  have hadj : (inner ℂ adjacencyTerm v).re ≤ τ * ‖v‖ * ‖v‖ := by
    have h1 : (inner ℂ adjacencyTerm v).re ≤ ‖adjacencyTerm‖ * ‖v‖ :=
      le_trans (Complex.re_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) adjacencyTerm v)
    exact le_trans h1 (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hlow : (μ - τ) * ‖v‖ ^ (2 : ℕ) ≤ (inner ℂ w v).re := by
    rw [hsplit]
    nlinarith [hM, hR, hadj, sq_nonneg ‖v‖]
  have hup : (inner ℂ w v).re ≤ ‖w‖ * ‖v‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) w v)
  have hkey : (μ - τ) * ‖v‖ * ‖v‖ ≤ ‖w‖ * ‖v‖ := by
    have : (μ - τ) * ‖v‖ ^ (2 : ℕ) ≤ ‖w‖ * ‖v‖ := le_trans hlow hup
    nlinarith [this]
  rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
  · rw [← hv]
    simp
  · exact le_of_mul_le_mul_right hkey hv

/-- **The estimate in the card's displayed form.**  Above the threshold `2L₀ > τ` the derivative is
bounded by the forcing divided by the position gap. -/
theorem energy_estimate_div {v w positionTerm jumpTerm adjacencyTerm : H} {L₀ τ : ℝ}
    (hgap : τ < 2 * L₀)
    (hM : (2 * L₀) * ‖v‖ ^ (2 : ℕ) ≤ (inner ℂ positionTerm v).re)
    (hR : 0 ≤ (inner ℂ jumpTerm v).re)
    (hT : ‖adjacencyTerm‖ ≤ τ * ‖v‖)
    (heq : positionTerm + jumpTerm - adjacencyTerm = w) :
    ‖v‖ ≤ (2 * L₀ - τ)⁻¹ * ‖w‖ := by
  have hpos : (0 : ℝ) < 2 * L₀ - τ := by linarith
  have hbase := energy_estimate hM hR hT heq
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  exact hbase

/-! ## The adjacency bound from an operator norm -/

/-- The adjacency hypothesis of the estimate is supplied by the plain operator norm. -/
theorem adjacency_bound_of_opNorm (T : H →L[ℂ] H) (v : H) : ‖T v‖ ≤ ‖T‖ * ‖v‖ :=
  T.le_opNorm v

end GaloisForLFunctions.RHTower
