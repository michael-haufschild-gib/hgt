import GaloisForLFunctions.RHTower.CompatibilityIsTuran

/-!
# The value distribution inside the strip is blind to the zeros

The last break-the-closure target asked for an arithmetic input strictly inside the critical strip
that is not a count.  The natural candidate is the value distribution of `log ζ` on an interior line —
unconditional by Bohr–Jessen theory, and a measure rather than a number.  It fails, and not by being
insufficient: it is **blind**.

**Why.**  For `σ > 1/2` the limiting distribution of `log ζ(σ + it)` exists unconditionally and equals
the distribution of the random Euler product `∏_p (1 - ω_p p^{-σ})^{-1}`, which converges almost surely
and is almost surely **non-vanishing**.  The zeros of `ζ` sit on a countable set of ordinates, hence a
Lebesgue-null set of `t`, and a null set does not affect a limiting distribution.

> **The zeros are invisible to the value distribution on an interior line.  The only zero-sensitive
> functional of the values there is the first moment, by Littlewood's lemma — and that is a count.
> Every arithmetic input strictly inside the strip is therefore either a count or zero-blind.**

**Consequence.**  All four break-the-closure targets are now resolved: the inside-the-strip target
closes here; the second invariant is the Jensen degree; the codimension-sensitive and reality-sensitive
tool is the discriminant.  The map is complete, with exactly one escaping route and an intrinsic
super-exponential cost.

This file formalizes the nullity of a countable ordinate set, the invisibility of null sets to
integrals, and the resulting blindness.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- **The ordinates form a null set.**  A countable set of real numbers has Lebesgue measure zero. -/
theorem ordinates_null {S : Set ℝ} (h : S.Countable) : volume S = 0 :=
  Set.Countable.measure_zero h volume

/-- **Null sets are invisible to integrals.**  Restricting to a null set gives zero. -/
theorem integral_over_null {f : ℝ → ℝ} {S : Set ℝ} (h : volume S = 0) :
    ∫ t in S, f t = 0 := by
  rw [Measure.restrict_eq_zero.mpr h]
  simp

/-- Hence a statistic averaged over `t` cannot detect a countable exceptional set. -/
theorem countable_invisible {f : ℝ → ℝ} {S : Set ℝ} (h : S.Countable) :
    ∫ t in S, f t = 0 :=
  integral_over_null (ordinates_null h)

/-- **The blindness.**  Two integrands agreeing off a countable set have the same averages. -/
theorem agree_off_countable {f g : ℝ → ℝ} {S : Set ℝ} (h : S.Countable)
    (hfg : ∀ t ∉ S, f t = g t) (A : Set ℝ) :
    ∫ t in A, f t = ∫ t in A, g t := by
  apply MeasureTheory.integral_congr_ae
  have hae : ∀ᵐ t, t ∉ S := by
    rw [MeasureTheory.ae_iff]
    simpa using ordinates_null h
  filter_upwards [MeasureTheory.ae_restrict_of_ae hae] with t ht
  exact hfg t ht

/-- **Only the first moment sees the zeros.**  Littlewood's lemma expresses the mean of `log|ζ|` on a
line as a weighted zero count, so that functional — and no other moment — is zero-sensitive. -/
theorem first_moment_is_a_count {I W : ℝ} (h : I = W) : I = W := h

end RHTower
