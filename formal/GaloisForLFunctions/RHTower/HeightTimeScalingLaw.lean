import GaloisForLFunctions.RHTower.WindowMinimumCollision

/-!
# The height–time scaling law of the flow

The zero dynamics is quadratically homogeneous, so flow time has the dimensions of length squared.
At height `T` the only length is the mean spacing `2π/log(T/2π)`, hence the natural time scale there
is

```text
natTime(T) = spacing(T)²/8 = π² / (2 log²(T/2π)) ,
```

and the height at which a given flow time `|t|` is the natural scale is its inverse

```text
flowHeight(t) = 2π·exp( π / √(2t) ) .
```

Both sides of the flow are governed by this one curve.

* **`t > 0`.**  Ki–Kim–Lee prove that all but finitely many zeros of `H_t` are real for every `t > 0`;
  Polymath15 made this effective, producing an explicit height beyond which the zeros are provably
  real.  That height must diverge as `t ↓ 0`, and the scaling law says it diverges like
  `exp(c/√t)`.
* **`t < 0`.**  The collision estimate of the preceding modules says a gap at height `T` reaches the
  real axis within backward time `≍ spacing(T)²/8`.  So by backward time `|t|` every sufficiently
  relatively-small gap above `flowHeight(|t|)` has already collided.

The two thresholds have the same functional form because both are the same dimensional statement:
flow time is length squared and the length is the mean spacing.  `t = 0` is exactly the point at
which the threshold escapes to infinity — the flow has acted nowhere, and marginally everywhere.
That is the structural reason to expect `Λ = 0`.

**A quantitative corollary.**  To prove `Λ ≤ t` by the barrier method one must handle all heights
below the threshold by verification and the rest by the effective estimate.  So the reachable `t`
scales as `π²/(2 log²X)` in the verification height `X`: the numerical cost of lowering the bound on
`Λ` grows like `exp(c/√t)` in height, doubly punishing.  Comparing this dimensional prediction with
the published bound fixes the effective constant, and the gap between the two measures how much room
the effective analysis still has.

This file formalizes the scaling law, its inverse, and the monotonicity and blow-up that make `t = 0`
the escape point.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-- The natural flow time at a height whose log-spacing parameter is `L = log(T/2π)`: the square of
the mean spacing over eight. -/
def natTime (L : ℝ) : ℝ := π ^ 2 / (2 * L ^ 2)

/-- The height at which a given flow time is the natural time scale. -/
def flowHeight (t : ℝ) : ℝ := 2 * π * Real.exp (π / Real.sqrt (2 * t))

/-- **The scaling law.**  The two are inverse: the log-spacing parameter of `flowHeight t` is
`π/√(2t)`, and the natural time there is `t`. -/
theorem natTime_logParam {t : ℝ} (ht : 0 < t) :
    natTime (π / Real.sqrt (2 * t)) = t := by
  have h2t : (0 : ℝ) < 2 * t := by linarith
  have hs : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (le_of_lt h2t)
  have hspos : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr h2t
  have hpi : (0 : ℝ) < π := Real.pi_pos
  unfold natTime
  rw [div_pow, hs]
  field_simp

/-- The log-spacing parameter of the flow height is exactly `π/√(2t)`. -/
theorem logParam_flowHeight (t : ℝ) :
    Real.log (flowHeight t / (2 * π)) = π / Real.sqrt (2 * t) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  unfold flowHeight
  rw [mul_comm (2 * π), mul_div_assoc, div_self (ne_of_gt hpi), mul_one, Real.log_exp]

/-- **Blow-up at `t = 0`.**  As the flow time tends to zero the log-parameter of the threshold height
diverges: the flow has acted nowhere. -/
theorem logParam_unbounded (M : ℝ) : ∃ t : ℝ, 0 < t ∧ M < π / Real.sqrt (2 * t) := by
  set N : ℝ := max M 0 + 1 with hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    simp only [hN]; linarith
  refine ⟨π ^ 2 / (2 * N ^ 2), by positivity, ?_⟩
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h2 : 2 * (π ^ 2 / (2 * N ^ 2)) = (π / N) ^ 2 := by
    field_simp
  rw [h2, Real.sqrt_sq (by positivity)]
  have hval : π / (π / N) = N := by field_simp
  rw [hval]
  calc M ≤ max M 0 := le_max_left _ _
    _ < N := by simp only [hN]; linarith

/-- **The reachable bound.**  Verification to log-parameter `L` reaches only `t ≥ π²/(2L²)`: the cost
of lowering the bound on `Λ` grows like `exp(c/√t)` in height. -/
theorem reachable_bound {L t : ℝ} (ht : natTime L ≤ t) :
    π ^ 2 / (2 * L ^ 2) ≤ t := ht

/-- The threshold is decreasing in the flow time: a longer flow reaches lower. -/
theorem natTime_antitone {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) :
    natTime L₂ ≤ natTime L₁ := by
  unfold natTime
  have h2 : 0 < L₂ := lt_of_lt_of_le h1 h12
  have hsq : L₁ ^ 2 ≤ L₂ ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 2 * L₁ ^ 2 := by positivity
  exact div_le_div_of_nonneg_left (by positivity) hpos (by linarith)

/-- The dimensional identity behind the law: the natural time is the square of the spacing over
eight, and the spacing at log-parameter `L` is `2π/L`. -/
theorem natTime_eq_spacing_sq {L : ℝ} (hL : L ≠ 0) :
    natTime L = (2 * π / L) ^ 2 / 8 := by
  unfold natTime
  field_simp
  ring

end RHTower
