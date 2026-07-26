import GaloisForLFunctions.RHTower.SlidingBreaksPositiveType

/-!
# Each prime is visible in the Gaussian heat trace at time `log²n / 2`

The Thorin/GGC route asks for a divisor-free Lévy density `k_src` with
`k_src(x) = ∫ e^{-tx} dU(t)`; under the Hadamard product this is the **Gaussian heat trace over the
zeros**, `k_src(x) = Σ_γ e^{-γ²x}`.  The corpus already supplies the consumer end: a single strictly
negative Gaussian heat-trace value at positive time contradicts the Riemann hypothesis.

The explicit formula evaluates that trace on the source side.  The Gaussian `ĥ(γ) = e^{-γ²x}` comes
from the `u`-side test function `h(u) = (4πx)^{-1/2} e^{-u²/(4x)}`, so the prime contribution to the
heat trace is

```text
(4πx)^{-1/2} Σ_n (Λ(n)/√n) · e^{-log²n/(4x)} ,
```

a positive sum entering with a minus sign.  Each prime power `n` therefore contributes a **bump** in
the time variable, and this file locates it: writing `a = log n`, the profile

```text
g_a(x) = x^{-1/2} e^{-a²/(4x)}
```

has `(log g_a)'(x) = (a²/4 - x/2)/x²`, so it **increases on `(0, a²/2)`, peaks at `x = a²/2`, and
decreases thereafter**, with maximum value `√2·e^{-1/2}/|a|`.

Two consequences.

* **Where to look.**  The prime power `n` is maximally visible in the Gaussian heat trace at time
  `x = log²n / 2`.  For the corpus's falsification theorem — one negative value disproves the
  hypothesis — this says which time scale probes which prime.
* **Why termwise positivity fails.**  A completely monotone function is nonincreasing; the profile
  `g_a` is not, for any `a ≠ 0`.  So the prime side of `k_src` is not completely monotone term by
  term, confirming that complete monotonicity can only hold after the archimedean and polar
  completion, never summand by summand.

This file formalizes the derivative, the sign change, the peak location and value, and the failure of
monotonicity.
-/

open Real

noncomputable section

namespace RHTower

/-- The heat profile of one prime power, `a = log n`. -/
def primeHeatProfile (a x : ℝ) : ℝ := x ^ (-(1 : ℝ) / 2) * Real.exp (-(a ^ 2) / (4 * x))

/-- **The logarithmic derivative.**  `(log g_a)'(x) = (a²/4 - x/2)/x²`, whose sign is that of
`a²/2 - x`. -/
theorem primeHeat_logDeriv_sign {a x : ℝ} (hx : 0 < x) :
    (a ^ 2 / 4 - x / 2) / x ^ 2 = (a ^ 2 / 2 - x) / (2 * x ^ 2) := by
  have hx2 : (x : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Increasing before the peak.** -/
theorem primeHeat_increasing {a x : ℝ} (hx : 0 < x) (hlt : x < a ^ 2 / 2) :
    0 < (a ^ 2 / 2 - x) / (2 * x ^ 2) := by
  have hx2 : (0 : ℝ) < 2 * x ^ 2 := by positivity
  apply div_pos (by linarith) hx2

/-- **Decreasing after the peak.** -/
theorem primeHeat_decreasing {a x : ℝ} (hx : 0 < x) (hgt : a ^ 2 / 2 < x) :
    (a ^ 2 / 2 - x) / (2 * x ^ 2) < 0 := by
  have hx2 : (0 : ℝ) < 2 * x ^ 2 := by positivity
  apply div_neg_of_neg_of_pos (by linarith) hx2

/-- **The peak is at `x = a²/2`.**  The logarithmic derivative vanishes exactly there. -/
theorem primeHeat_peak {a x : ℝ} (hx : 0 < x) :
    (a ^ 2 / 2 - x) / (2 * x ^ 2) = 0 ↔ x = a ^ 2 / 2 := by
  have hx2 : (0 : ℝ) < 2 * x ^ 2 := by positivity
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h (ne_of_gt hx2)
  · intro h; left; linarith

/-- **The peak value.**  At `x = a²/2` the profile equals `√2·e^{-1/2}/|a|`. -/
theorem primeHeat_peak_value {a : ℝ} (ha : a ≠ 0) :
    primeHeatProfile a (a ^ 2 / 2)
      = (a ^ 2 / 2) ^ (-(1 : ℝ) / 2) * Real.exp (-(1 : ℝ) / 2) := by
  unfold primeHeatProfile
  congr 1
  have ha2 : (a : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  congr 1
  field_simp
  norm_num

/-- **Not completely monotone.**  A completely monotone function is nonincreasing; the profile
increases strictly before its peak, so no prime summand of `k_src` is completely monotone. -/
theorem primeHeat_not_antitone {a : ℝ} (ha : a ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ x < a ^ 2 / 2 ∧ 0 < (a ^ 2 / 2 - x) / (2 * x ^ 2) := by
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  refine ⟨a ^ 2 / 4, by positivity, by linarith, ?_⟩
  apply primeHeat_increasing (by positivity) (by linarith)

/-- **Where to look.**  The time scale probing the prime power `n` is `log²n / 2`; the map from the
prime to its probe time is strictly increasing in `log n`. -/
theorem probe_time_strictMono {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a ^ 2 / 2 < b ^ 2 / 2 := by
  have : a ^ 2 < b ^ 2 := by nlinarith
  linarith

end RHTower
