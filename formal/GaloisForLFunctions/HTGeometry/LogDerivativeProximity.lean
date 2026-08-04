import GaloisForLFunctions.HTGeometry.LogDerivativeFactor
import GaloisForLFunctions.HTGeometry.PoissonJensenUpperBound

/-!
# The proximity of the logarithmic derivative

Integrating the pointwise bound of `LogDerivativeFactor` over a circle turns each zero term into a
`log 2`, by the exact circle average of `log ‖· - a‖`.  What is left is a constant depending only on
the zero data, plus the proximity of the logarithmic derivative of the zero-free cofactor — and that
is logarithmic in the maximum modulus.

This is Nevanlinna's estimate for the logarithmic derivative, in the form the second main theorem
consumes.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- The proximity integrand of a linear factor is the negative part of its log-modulus. -/
theorem posLog_inv_eq_negPart (z a : ℂ) :
    Real.posLog ‖z - a‖⁻¹ = max 0 (-Real.log ‖z - a‖) := by
  rw [Real.posLog, Real.log_inv]

/-- The proximity integrand of a linear factor is circle integrable. -/
theorem circleIntegrable_posLog_inv_sub (a : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => Real.posLog ‖z - a‖⁻¹) 0 r := by
  have hmero : MeromorphicOn (fun z : ℂ => z - a) (sphere (0 : ℂ) |r|) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  have hfun : (fun z : ℂ => Real.posLog ‖z - a‖⁻¹)
      = (fun z : ℂ => Real.posLog ‖z - a‖) - fun z : ℂ => Real.log ‖z - a‖ := by
    funext z
    rw [Pi.sub_apply, posLog_inv_eq_negPart, posPart_neg, Real.posLog]
  rw [hfun]
  exact hmero.circleIntegrable_posLog_norm.sub hmero.circleIntegrable_log_norm

/-- **Each zero costs `log 2` in proximity.** -/
theorem circleAverage_posLog_inv_sub_le {a : ℂ} {r : ℝ} (hr : 1 ≤ r)
    (ha : a ∈ closedBall (0 : ℂ) r) :
    Real.circleAverage (fun z => Real.posLog ‖z - a‖⁻¹) 0 r ≤ Real.log 2 := by
  have hfun : (fun z : ℂ => Real.posLog ‖z - a‖⁻¹)
      = fun z : ℂ => max 0 (-Real.log ‖z - a‖) := by
    funext z
    exact posLog_inv_eq_negPart z a
  rw [hfun]
  exact circleAverage_negPart_log_norm_sub_le hr ha

/-- **The proximity of the logarithmic derivative.**  Integrating the pointwise split: the zero terms
contribute `log 2` each, and the rest is the proximity of the cofactor's logarithmic derivative. -/
theorem circleAverage_posLog_logDeriv_le {f h : ℂ → ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {r : ℝ}
    (hr : 1 ≤ r) (hTmem : ∀ a ∈ T, a ∈ closedBall (0 : ℂ) r)
    (hpt : ∀ z : ℂ, z ∈ sphere (0 : ℂ) |r| →
      Real.posLog ‖deriv f z / f z‖
        ≤ (Real.log 2 + Real.log (T.card : ℝ) + ∑ a ∈ T, Real.log (m a : ℝ))
          + (∑ a ∈ T, Real.posLog ‖z - a‖⁻¹) + Real.posLog ‖deriv h z / h z‖)
    (hintf : CircleIntegrable (fun z => Real.posLog ‖deriv f z / f z‖) 0 r)
    (hinth : CircleIntegrable (fun z => Real.posLog ‖deriv h z / h z‖) 0 r) :
    Real.circleAverage (fun z => Real.posLog ‖deriv f z / f z‖) 0 r
      ≤ (Real.log 2 + Real.log (T.card : ℝ) + ∑ a ∈ T, Real.log (m a : ℝ))
        + (T.card : ℝ) * Real.log 2
        + Real.circleAverage (fun z => Real.posLog ‖deriv h z / h z‖) 0 r := by
  classical
  set C : ℝ := Real.log 2 + Real.log (T.card : ℝ) + ∑ a ∈ T, Real.log (m a : ℝ) with hC
  have hzero : ∀ a ∈ T, CircleIntegrable (fun z => Real.posLog ‖z - a‖⁻¹) 0 r :=
    fun a _ => circleIntegrable_posLog_inv_sub a r
  have hsumint : CircleIntegrable (fun z => ∑ a ∈ T, Real.posLog ‖z - a‖⁻¹) 0 r :=
    CircleIntegrable.fun_sum T hzero
  have hconstint : CircleIntegrable (fun _ : ℂ => C) 0 r :=
    ContinuousOn.circleIntegrable' continuousOn_const
  have hrhsint : CircleIntegrable
      (fun z => C + (∑ a ∈ T, Real.posLog ‖z - a‖⁻¹) + Real.posLog ‖deriv h z / h z‖) 0 r :=
    (hconstint.add hsumint).add hinth
  have hmono := Real.circleAverage_mono hintf hrhsint hpt
  -- expand the average of the majorant
  have hsplit : Real.circleAverage
      (fun z => C + (∑ a ∈ T, Real.posLog ‖z - a‖⁻¹) + Real.posLog ‖deriv h z / h z‖) 0 r
      = C + Real.circleAverage (fun z => ∑ a ∈ T, Real.posLog ‖z - a‖⁻¹) 0 r
        + Real.circleAverage (fun z => Real.posLog ‖deriv h z / h z‖) 0 r := by
    have h₁ : (fun z : ℂ => C + (∑ a ∈ T, Real.posLog ‖z - a‖⁻¹)
          + Real.posLog ‖deriv h z / h z‖)
        = ((fun _ : ℂ => C) + fun z : ℂ => ∑ a ∈ T, Real.posLog ‖z - a‖⁻¹)
          + fun z : ℂ => Real.posLog ‖deriv h z / h z‖ := rfl
    rw [h₁, Real.circleAverage_add (hconstint.add hsumint) hinth,
      Real.circleAverage_add hconstint hsumint, Real.circleAverage_const]
  have hsumavg : Real.circleAverage (fun z => ∑ a ∈ T, Real.posLog ‖z - a‖⁻¹) 0 r
      ≤ (T.card : ℝ) * Real.log 2 := by
    rw [Real.circleAverage_fun_sum hzero]
    have hbd : ∀ a ∈ T,
        Real.circleAverage (fun z => Real.posLog ‖z - a‖⁻¹) 0 r ≤ Real.log 2 :=
      fun a ha => circleAverage_posLog_inv_sub_le hr (hTmem a ha)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hbd
    rw [nsmul_eq_mul] at hsum
    exact hsum
  rw [hsplit] at hmono
  linarith

/-! ## The shifted logarithmic derivative

The second main theorem needs the proximity of `f'/(f - a)` for several values `a`.  Shifting does
not change the numerator, so the estimate above applies verbatim to the shifted function. -/

/-- Shifting by a constant does not change the numerator of the logarithmic derivative. -/
theorem logDeriv_shift_eq (f : ℂ → ℂ) (a : ℂ) :
    (fun z : ℂ => deriv (fun w => f w - a) z / ((fun w : ℂ => f w - a) z))
      = fun z : ℂ => deriv f z / (f z - a) := by
  funext z
  rw [deriv_sub_const]

/-- **The proximity of `f'/(f - a)`.**  The estimate for the logarithmic derivative, applied to the
shift `f - a` and rewritten through `logDeriv_shift_eq`. -/
theorem circleAverage_posLog_logDeriv_sub_const_le {f h : ℂ → ℂ} {a : ℂ}
    {T : Finset ℂ} {m : ℂ → ℕ} {r : ℝ}
    (hr : 1 ≤ r) (hTmem : ∀ b ∈ T, b ∈ closedBall (0 : ℂ) r)
    (hpt : ∀ z : ℂ, z ∈ sphere (0 : ℂ) |r| →
      Real.posLog ‖deriv f z / (f z - a)‖
        ≤ (Real.log 2 + Real.log (T.card : ℝ) + ∑ b ∈ T, Real.log (m b : ℝ))
          + (∑ b ∈ T, Real.posLog ‖z - b‖⁻¹) + Real.posLog ‖deriv h z / h z‖)
    (hintf : CircleIntegrable (fun z => Real.posLog ‖deriv f z / (f z - a)‖) 0 r)
    (hinth : CircleIntegrable (fun z => Real.posLog ‖deriv h z / h z‖) 0 r) :
    Real.circleAverage (fun z => Real.posLog ‖deriv f z / (f z - a)‖) 0 r
      ≤ (Real.log 2 + Real.log (T.card : ℝ) + ∑ b ∈ T, Real.log (m b : ℝ))
        + (T.card : ℝ) * Real.log 2
        + Real.circleAverage (fun z => Real.posLog ‖deriv h z / h z‖) 0 r := by
  have hbase := circleAverage_posLog_logDeriv_le (f := fun w => f w - a) (h := h)
    (T := T) (m := m) hr hTmem ?_ ?_ hinth
  · simpa [deriv_sub_const] using hbase
  · intro z hz
    have hz' := hpt z hz
    simpa [deriv_sub_const] using hz'
  · simpa [deriv_sub_const] using hintf

end GaloisForLFunctions.HTGeometry
