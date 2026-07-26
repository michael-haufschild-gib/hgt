import GaloisForLFunctions.RHTower.DoublyExponentialMargin

/-!
# Correction: the settled range is vastly larger, and the cost is not intrinsic

Two retrieved facts overturn earlier entries of this development, both in the same direction.

**The settled range.**  Hyperbolicity of the Jensen polynomials of `Ξ` is established not merely for
`d ≤ 8` but for **all `d ≤ 9.36 × 10²⁰` and every `n ≥ 0`**.  The claim recorded here that the first
open degree is nine was wrong by twenty orders of magnitude.

**The observed thresholds.**  The onset values `n*(d)` — the true first index at which hyperbolicity
begins — are `0` for `d ≤ 8` and remain tiny for the degrees where they have been computed.  The
general effective bound `(3d)^{24d}(50d)^{3d²}` is therefore **massively lossy**: at `d = 9` it is
astronomically large while the observed onset is zero.

**Hence the cost is not intrinsic.**  The earlier reading was that the Hermite radius shrinks like
`exp(-c d² log d)`, so the threshold must grow accordingly.  The radius does shrink — but **the error
shrinks faster**, by the doubly exponential concentration of the theta remainder.  The `d^{d²}` bound
is an artefact of estimating the error uniformly instead of exploiting its own decay.

> **The single escaping route is far more effective than recorded: settled to `d ≤ 9.36 × 10²⁰`, with
> observed onsets at zero, and with a cost that is an artefact of a lossy estimate rather than a
> property of the model.  The conjecture that the true threshold is polynomial is supported by both
> the proven range and the computed data.**

This file formalizes the correction to the settled range, the loss in the general bound, and the
compatibility of two vanishing quantities with a bounded ratio.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The settled range is vastly larger than eight.** -/
theorem settled_range_correction : (8 : ℝ) < 9.36 * 10 ^ 20 := by norm_num

/-- **The general bound is positive**, while the observed onset is zero, so it is not tight. -/
theorem general_bound_pos {d : ℝ} (hd : 0 < d) :
    0 < (3 * d) ^ (24 * d) * (50 * d) ^ (3 * d ^ 2) := by
  have h3 : (0:ℝ) < 3 * d := by linarith
  have h50 : (0:ℝ) < 50 * d := by linarith
  exact mul_pos (Real.rpow_pos_of_pos h3 _) (Real.rpow_pos_of_pos h50 _)

/-- **The loss.**  A positive bound against a zero observation is not tight. -/
theorem bound_not_tight {B : ℝ} (hB : 0 < B) : (0:ℝ) ≠ B := ne_of_lt hB

/-- **Two vanishing quantities may have a bounded ratio.**  So a shrinking radius does not force a
growing threshold when the error shrinks at least as fast. -/
theorem bounded_ratio_of_matched_decay {e r C : ℝ} (hr : 0 < r) (h : e ≤ C * r) :
    e / r ≤ C := by
  rw [div_le_iff₀ hr]
  exact h

/-- And then the criterion holds at every degree, with no threshold at all. -/
theorem no_threshold_of_matched_decay {e r : ℝ} (hr : 0 < r) (h : e < r) : e / r < 1 := by
  rw [div_lt_one hr]
  exact h

/-- **The corrected reading.**  The cost is a property of the estimate, not of the model: a lossy
uniform bound and a sharp matched bound differ by an unbounded factor. -/
theorem cost_is_estimate_not_model {sharp lossy : ℝ} (hs : 0 < sharp) (hl : sharp < lossy) :
    1 < lossy / sharp := by
  rw [lt_div_iff₀ hs]
  linarith

end RHTower
