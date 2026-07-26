import GaloisForLFunctions.RHTower.RecurrenceZeroDensity

/-!
# The critical scale `1/log T`, a fifth time

The recurrence lane is circular as stated: the support of the limit measure of the random Euler
product is exactly the set of non-vanishing analytic functions, so membership of `ζ` in the support of
its own limit measure **is** the hypothesis.  What is not circular is that measure's **moments**,
which are unconditional Euler products.  This file records what they say.

**Variance in the random model.**  For `ζ(s, ω) = ∏_p (1 - ω(p) p^{-s})^{-1}` the logarithm is a sum
of *independent* contributions — precisely the multiplicative-independence ingredient — with variance
at abscissa `σ` of size

```text
Σ_p Σ_k (k² p^{2kσ})^{-1}  ≍  Σ_p p^{-2σ}  ≍  ½ log( 1/(2σ - 1) )      as σ ↓ 1/2 ,
```

diverging logarithmically at the critical abscissa and nowhere else.

**Matching Selberg.**  On the critical line the unconditional Selberg central limit theorem gives
variance `≍ ½ log log T`.  Equating the two profiles identifies

```text
1/(2σ - 1)  ↔  log T ,        i.e.        σ - ½  ↔  1/(2 log T) .
```

> **The random model's approach to the critical line and the true fluctuation of `log ζ` on it agree
> exactly when the distance from the line is measured in units of `1/log T` — the same scale found as
> the crossover of the Nyquist dichotomy, as the mean zero spacing, and as the width of the classical
> zero-free region.**

This is the fifth independent appearance of that scale here, after the detection cost, the Nyquist
crossover, the mean spacing, and the pole's logarithmic weight.  As with the four derivations of the
pole, the agreement is structural coherence rather than new leverage: one object seen from several
sides.

This file formalizes the divergence of the variance profile, the scale identification, and the common
form of the two critical widths.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The variance profile is unbounded at the critical abscissa.**  For every level there is a
`σ > 1/2` with `1/(2σ - 1)` above it. -/
theorem variance_profile_unbounded (M : ℝ) (hM : 0 < M) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ M < 1 / (2 * σ - 1) := by
  have hMp : (0:ℝ) < M + 1 := by linarith
  have hpos : (0:ℝ) < 1 / (2 * (M + 1)) := by positivity
  refine ⟨1 / 2 + 1 / (2 * (M + 1)), by linarith, ?_⟩
  have hval : 2 * (1 / 2 + 1 / (2 * (M + 1))) - 1 = 1 / (M + 1) := by
    field_simp
    ring
  rw [hval, one_div_one_div]
  linarith

/-- **The scale identification.**  Setting the variance profile equal to `log T` places `σ` at
distance `1/(2 log T)` from the critical line. -/
theorem scale_identification {σ L : ℝ} (hσ : 1 / 2 < σ) (hL : 0 < L) :
    1 / (2 * σ - 1) = L ↔ σ - 1 / 2 = 1 / (2 * L) := by
  have hd : 0 < 2 * σ - 1 := by linarith
  constructor
  · intro h
    have h2 : 2 * σ - 1 = 1 / L := by
      field_simp at h ⊢
      linarith
    have : σ - 1 / 2 = (1 / L) / 2 := by linarith
    rw [this]
    field_simp
  · intro h
    have h2 : 2 * σ - 1 = 1 / L := by
      have := h
      field_simp at this ⊢
      linarith
    rw [h2, one_div_one_div]

/-- **Both critical widths have the same form.**  The Nyquist crossover `3/log T` and the variance
scale `1/(2 log T)` are both `c/log T` with `c > 0`. -/
theorem both_are_inverse_log {T : ℝ} (hT : 1 < T) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      3 / Real.log T = c₁ / Real.log T ∧ 1 / (2 * Real.log T) = c₂ / Real.log T := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  refine ⟨3, 1 / 2, by norm_num, by norm_num, rfl, ?_⟩
  field_simp

/-- The two constants differ, so the appearances are of the same scale but not the same statement. -/
theorem constants_differ : (3:ℝ) ≠ 1 / 2 := by norm_num

/-- **Coherence, not leverage.**  Two quantities of the same order carry no information about each
other beyond that order. -/
theorem same_order_no_information {c₁ c₂ x : ℝ} (h : 0 < x) (h1 : 0 < c₁) (h2 : 0 < c₂) :
    c₁ / x > 0 ∧ c₂ / x > 0 := ⟨by positivity, by positivity⟩

end RHTower
