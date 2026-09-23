import GaloisForLFunctions.RHTower.Sieve.SqrtLogDecayIntegral

/-!
# The tail integral of the weight `exp(−c√(log t))/t`

The weight `exp(−c√(log t))/t` has an elementary antiderivative:

```text
G(t) = (2/c²)·(1 + c√(log t))·exp(−c√(log t)),        G′(t) = −exp(−c√(log t))/t .
```

So the improper tail `∫_a^∞ exp(−c√(log t))/t dt` is exactly `G(a)`, with no change of variables
and no comparison test.  Since `1 + y ≤ 2·exp(y/2)`, the tail obeys
`G(a) ≤ (4/c²)·exp(−(c/2)√(log a))` — again the decay constant halves, and again that is the price
of the crude bound on the polynomial factor rather than slack in the integration.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics MeasureTheory Set

/-- The antiderivative of `−exp(−c√(log t))/t`. -/
noncomputable def sqrtLogTail (c t : ℝ) : ℝ :=
  2 / c ^ (2 : ℕ) * ((1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t)))

theorem sqrtLogTail_nonneg {c t : ℝ} (hc : 0 < c) : 0 ≤ sqrtLogTail c t := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
  have : (0 : ℝ) ≤ 1 + c * Real.sqrt (Real.log t) := by positivity
  unfold sqrtLogTail
  positivity

/-- `−G` has derivative `exp(−c√(log t))/t`. -/
theorem hasDerivAt_neg_sqrtLogTail {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => -sqrtLogTail c x)
      (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hL : (0 : ℝ) < Real.log t := Real.log_pos ht
  have hs : (0 : ℝ) < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hL
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht0)
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (Real.log t))) (Real.log t) :=
    Real.hasDerivAt_sqrt (ne_of_gt hL)
  have hu : HasDerivAt (fun x : ℝ => Real.sqrt (Real.log x))
      (1 / (2 * Real.sqrt (Real.log t)) * t⁻¹) t := HasDerivAt.comp t hsq hlog
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x)))
      (Real.exp (-c * Real.sqrt (Real.log t)) *
        (-c * (1 / (2 * Real.sqrt (Real.log t)) * t⁻¹))) t := (hu.const_mul (-c)).exp
  have hlin : HasDerivAt (fun x : ℝ => 1 + c * Real.sqrt (Real.log x))
      (c * (1 / (2 * Real.sqrt (Real.log t)) * t⁻¹)) t := (hu.const_mul c).const_add 1
  have hG := ((hlin.mul hexp).const_mul (2 / c ^ (2 : ℕ))).neg
  have hsne : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt hs
  have htne : t ≠ 0 := ne_of_gt ht0
  have hcne : c ≠ 0 := ne_of_gt hc
  have hval : Real.exp (-c * Real.sqrt (Real.log t)) / t
      = -(2 / c ^ (2 : ℕ) * (c * (1 / (2 * Real.sqrt (Real.log t)) * t⁻¹)
            * Real.exp (-c * Real.sqrt (Real.log t))
          + (1 + c * Real.sqrt (Real.log t))
            * (Real.exp (-c * Real.sqrt (Real.log t))
              * (-c * (1 / (2 * Real.sqrt (Real.log t)) * t⁻¹))))) := by
    field_simp
    ring
  simp only [sqrtLogTail, hval]
  exact hG

/-- `G(t) → 0`. -/
theorem tendsto_sqrtLogTail {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => sqrtLogTail c t) atTop (nhds 0) := by
  have hbase : Tendsto (fun y : ℝ => (1 + y) * Real.exp (-y)) atTop (nhds 0) := by
    have ha := Real.tendsto_exp_neg_atTop_nhds_zero
    have hb := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hsum := ha.add hb
    rw [add_zero] at hsum
    refine hsum.congr fun y => ?_
    simp only [pow_one]
    ring
  have harg : Tendsto (fun t : ℝ => c * Real.sqrt (Real.log t)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  have hcomp := hbase.comp harg
  have := hcomp.const_mul (2 / c ^ (2 : ℕ))
  rw [mul_zero] at this
  refine this.congr fun t => ?_
  simp only [sqrtLogTail, Function.comp_apply, neg_mul]

/-- `1 + y ≤ 2·exp(y/2)` for `y ≥ 0`. -/
theorem one_add_le_two_mul_exp_half (y : ℝ) : 1 + y ≤ 2 * Real.exp (y / 2) := by
  have h := Real.add_one_le_exp (y / 2)
  linarith

/-- **The tail is below the halved shape.** -/
theorem sqrtLogTail_le {c t : ℝ} (hc : 0 < c) :
    sqrtLogTail c t ≤ 4 / c ^ (2 : ℕ) * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
  have hy : (0 : ℝ) ≤ c * Real.sqrt (Real.log t) := by positivity
  have hlin := one_add_le_two_mul_exp_half (c * Real.sqrt (Real.log t))
  have hE : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log t)) := Real.exp_pos _
  have hsplit : Real.exp (c * Real.sqrt (Real.log t) / 2)
      * Real.exp (-c * Real.sqrt (Real.log t))
      = Real.exp (-(c / 2) * Real.sqrt (Real.log t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hstep : (1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t))
      ≤ 2 * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) := by
    calc (1 + c * Real.sqrt (Real.log t)) * Real.exp (-c * Real.sqrt (Real.log t))
        ≤ 2 * Real.exp (c * Real.sqrt (Real.log t) / 2)
            * Real.exp (-c * Real.sqrt (Real.log t)) :=
          mul_le_mul_of_nonneg_right hlin hE.le
      _ = 2 * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) := by
          rw [mul_assoc, hsplit]
  have hc2 : (0 : ℝ) < 2 / c ^ (2 : ℕ) := by positivity
  have := mul_le_mul_of_nonneg_left hstep hc2.le
  calc sqrtLogTail c t ≤ 2 / c ^ (2 : ℕ) * (2 * Real.exp (-(c / 2) * Real.sqrt (Real.log t))) := this
    _ = 4 / c ^ (2 : ℕ) * Real.exp (-(c / 2) * Real.sqrt (Real.log t)) := by ring

/-- The weight is integrable on every `(a,∞)` with `a > 1`. -/
theorem integrableOn_expSqrtLog_div_Ioi {c a : ℝ} (hc : 0 < c) (ha : 1 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t) (Set.Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => -sqrtLogTail c x) (l := 0)
    ?_ ?_ ?_ ?_
  · exact ((hasDerivAt_neg_sqrtLogTail hc ha).continuousAt).continuousWithinAt
  · exact fun x hx => hasDerivAt_neg_sqrtLogTail hc (lt_trans ha hx)
  · intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans (by linarith) hx
    positivity
  · simpa using (tendsto_sqrtLogTail hc).neg

/-- **The tail integral is exactly `G(a)`.** -/
theorem integral_expSqrtLog_div_Ioi {c a : ℝ} (hc : 0 < c) (ha : 1 < a) :
    ∫ t in Set.Ioi a, Real.exp (-c * Real.sqrt (Real.log t)) / t = sqrtLogTail c a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (m := 0)
    (f := fun x : ℝ => -sqrtLogTail c x)
    (f' := fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
    ((hasDerivAt_neg_sqrtLogTail hc ha).continuousAt).continuousWithinAt
    (fun x hx => hasDerivAt_neg_sqrtLogTail hc (lt_trans ha hx))
    (integrableOn_expSqrtLog_div_Ioi hc ha)
    (by simpa using (tendsto_sqrtLogTail hc).neg)
  rw [h]
  ring

end RHTower.Sieve
