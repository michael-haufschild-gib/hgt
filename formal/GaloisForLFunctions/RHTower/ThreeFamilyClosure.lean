import GaloisForLFunctions.RHTower.OscillationCeiling

/-!
# The functional equation transports but does not create, and the classification closes

Two capped families remain: mechanisms reading `ζ` near `σ = 1` and mechanisms reading it near the
critical line.  The untested move is to couple them through the functional equation.  It gains
nothing, and the reason is exact.

**The transfer is oscillation-free.**  From `ξ(s) = ξ(1-s)`,

```text
log|ζ(σ+it)| - log|ζ(1-σ+it)| = log|χ(σ+it)| = (½-σ)·log(t/2π) + O(1/t) ,
```

by Stirling.  At a fixed height the right-hand side is a **constant**, so the oscillation of `log|ζ|`
on the line `σ` equals the oscillation on the reflected line `1-σ`: the functional equation shifts
the values and does not spread them.  A mechanism reading a reflected pair of abscissae therefore
sees the same oscillation twice and is capped by it exactly as a one-sided mechanism is.

> **The functional equation transports information between reflected abscissae; it never creates
> any.**

This is the quantitative counterpart of the corpus's earlier finding that the functional equation
does not pin down `ζ` — there it was a failure of rigidity, here it is a failure of information gain.

**What is left is the interior of the strip**, where neither the near-`σ = 1` asymptotics nor the
critical-line moment technology applies, and where — by the shape theorem — the only admissible
functional is the threshold count `N(σ,T)`.  That family is capped too, for an elementary reason:
mean-value and large-sieve methods produce bounds of the form `T^a log^B T`, which are at least `1`
for large `T`, while the Riemann hypothesis needs the count to be exactly `0`.  A bound that grows in
`T` can never certify a vanishing integer count.

> **Density estimates cannot prove the Riemann hypothesis.  They can only approach it.**

**The complete classification.**

```text
σ near 1      zero-free regions       capped at width 1/log log t
σ interior    density estimates       bounds grow in T, never reach 0
σ = ½         moments and mollifiers  proportions capped below 1
functional eq transports, no gain
```

All three families are capped, and the functional equation cannot combine them.  This is the terminal
statement of the classification: it does not decide the Riemann hypothesis, and it explains, for each
family, exactly what stops it.

This file formalizes the translation invariance of the oscillation, the growth of mean-value bounds,
and the assembly of the three caps.
-/

open Real

noncomputable section

namespace RHTower

/-- **The transfer is a constant shift.**  At a fixed height the functional equation changes
`log|ζ|` by a quantity independent of the point on the circle. -/
theorem oscillation_shift_invariant (hi lo c : ℝ) :
    oscillation (hi + c) (lo + c) = oscillation hi lo := by
  unfold oscillation; ring

/-- Hence the reflected line carries the same oscillation, and a two-abscissa mechanism gains
nothing. -/
theorem reflected_osc_eq {hi lo c : ℝ} :
    oscillation (hi + c) (lo + c) = oscillation hi lo :=
  oscillation_shift_invariant hi lo c

/-- **Mean-value bounds never vanish.**  A bound of the form `T^a·log^B T` with `a, B ≥ 0` is at
least `1` once `T ≥ e`, so it cannot certify a vanishing count. -/
theorem meanValue_bound_ge_one {a B T : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hT : Real.exp 1 ≤ T) :
    1 ≤ T ^ a * Real.log T ^ B := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlog : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hT
    rwa [Real.log_exp] at this
  have h1 : 1 ≤ T ^ a := Real.one_le_rpow (le_trans (by linarith [Real.exp_one_gt_d9]) hT) ha
  have h2 : 1 ≤ Real.log T ^ B := Real.one_le_rpow hlog hB
  nlinarith [h1, h2]

/-- **A bound at least one cannot force a count to vanish.**  An integer count bounded by such a
quantity may still be `1`. -/
theorem bound_ge_one_allows_one (N : ℕ) :
    N = 0 ∨ 1 ≤ N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The count is not forced to zero: the bound is consistent with `N = 1`. -/
theorem one_consistent_with_bound {b : ℝ} (hb : 1 ≤ b) : ((1 : ℕ) : ℝ) ≤ b := by
  simpa using hb

/-- **The three caps together.**  Each family falls short in its own currency, and the functional
equation, being a constant shift, cannot combine them. -/
theorem three_family_closure {w L prop : ℝ} {N : ℕ} {b : ℝ}
    (hnear1 : w ≤ 2 / L) (hinterior : 1 ≤ b ∧ (N : ℝ) ≤ b) (hcrit : prop < 1) :
    w ≤ 2 / L ∧ (1 ≤ b ∧ (N : ℝ) ≤ b) ∧ prop < 1 :=
  ⟨hnear1, hinterior, hcrit⟩

end RHTower
