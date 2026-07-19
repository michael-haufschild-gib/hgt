import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Even moments pass to a weak limit as upper bounds

Weak convergence tests against bounded continuous functions, so it does not by itself transport a
moment: `xᵏ` is unbounded.  In one direction it does transport, and that direction is enough to
bound the moments of a limit measure.  The portmanteau inequality for lower semicontinuous
nonnegative
integrands — in mathlib as
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`, which notably does *not*
require the integrand to be bounded — gives

`∫⁻ f dμ ≤ liminf ∫⁻ f dμₙ`

for continuous `f ≥ 0`.  Applied to `x ↦ x^{2k}`, nonnegative because the exponent is even, a
uniform
bound on the even moments of the approximating sequence becomes a bound on the even moments of the
limit.

The hypothesis on open sets is the portmanteau characterisation of weak convergence, stated directly
rather than through a convergence assumption, so the result applies to any limit point however it
was
obtained.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

theorem pow_two_mul_nonneg (k : ℕ) (x : ℝ) : 0 ≤ x ^ (2 * k) := by
  rw [mul_comm, pow_mul]
  exact sq_nonneg _

/-- **A uniform bound on even moments passes to the weak limit.** -/
theorem lintegral_even_pow_le_of_forall_isOpen_le_liminf
    {μ : Measure ℝ} {μs : ℕ → Measure ℝ} (k : ℕ)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G)
    {C : ENNReal} (hC : ∀ᶠ i in atTop, ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μs i) ≤ C) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂μ ≤ C := by
  have hcont : Continuous fun x : ℝ => x ^ (2 * k) := by continuity
  have hnn : (0 : ℝ → ℝ) ≤ fun x : ℝ => x ^ (2 * k) := fun x => pow_two_mul_nonneg k x
  refine le_trans
    (lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure hcont hnn h_opens) ?_
  calc atTop.liminf (fun i => ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(μs i))
      ≤ atTop.liminf (fun _ : ℕ => C) := liminf_le_liminf hC
    _ = C := liminf_const C

end HTGeometry
