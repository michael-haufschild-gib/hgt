import GaloisForLFunctions.RHTower.CCMUnitRieszApertureResolventWeld

/-!
# All-epsilon order transfer across the unit-Riesz / aperture-resolvent weld

The exact orientation law of the aperture-resolvent weld converts every lower bound for the
literal unit-Riesz completed-source response into an upper bound for the unit-rate causal
resolvent of the normalized Chebyshev error, with no loss of exponent.  This file records the
resulting equivalence of the two all-epsilon families:

```text
U(t) ≥ -C exp(-(1/2 - ε) t)   for all t ≥ 0
  ↔  R₁(t) ≤ C' exp(ε t)      for all t ≥ 0.
```

The elementary polar remainder is uniformly bounded after the `exp(t/2)` normalization, which is
what makes the transfer exponent-free in both directions.

These are unconditional identities and inequalities.  Neither side is asserted here, and no RH
claim is made.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private theorem mul_exp_neg_half_le_two {t : ℝ} (ht : 0 ≤ t) :
    t * Real.exp (-t / 2) ≤ 2 := by
  have h1 : t / 2 + 1 ≤ Real.exp (t / 2) := Real.add_one_le_exp _
  have hstep : t * Real.exp (-t / 2) ≤ (2 * Real.exp (t / 2)) * Real.exp (-t / 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hcollapse : (2 * Real.exp (t / 2)) * Real.exp (-t / 2) = 2 := by
    rw [mul_assoc, ← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) by ring,
      Real.exp_zero, mul_one]
  linarith [hstep, hcollapse]

/-- After the `exp(t/2)` normalization forced by the orientation law, the elementary polar
remainder of the aperture-resolvent weld is the explicit two-exponential profile
`2(t-3)exp(-t/2) + (16/3)exp(-t)`. -/
theorem unitRieszApertureResolventRemainder_normalized_eq (t : ℝ) :
    (2 / 3) * Real.exp (t / 2) * unitRieszApertureResolventRemainder t =
      2 * (t - 3) * Real.exp (-t / 2) + (16 / 3) * Real.exp (-t) := by
  have h1 : Real.exp (t / 2) * Real.exp (-t) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (t / 2) * Real.exp (-3 * t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold unitRieszApertureResolventRemainder
  linear_combination (2 * (t - 3)) * h1 + (16 / 3 : ℝ) * h2

/-- The normalized polar remainder is uniformly bounded on the positive ray. -/
theorem abs_unitRieszApertureResolventRemainder_normalized_le
    {t : ℝ} (ht : 0 ≤ t) :
    |(2 / 3) * Real.exp (t / 2) * unitRieszApertureResolventRemainder t| ≤ 16 := by
  have hlin := mul_exp_neg_half_le_two ht
  have hexp1 : Real.exp (-t / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hexp2 : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hpos1 : (0 : ℝ) < Real.exp (-t / 2) := Real.exp_pos _
  have hpos2 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [unitRieszApertureResolventRemainder_normalized_eq, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **All-epsilon order transfer.**  For every `ε ≥ 0` the sub-half-power lower law for the
literal completed-source unit-Riesz response is exactly the `ε`-power upper law for the unit-rate
Chebyshev aperture resolvent.  The conversion is pointwise and loses no exponent. -/
theorem unitRiesz_lowerLaw_iff_apertureResolvent_subpower
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
        -(C * Real.exp (-(1 / 2 - ε) * t)) ≤ (unitRieszCompletedSourceResponse t).re) ↔
      (∃ C' : ℝ, ∀ t : ℝ, 0 ≤ t →
        criticalMellinChebyshevResolventSource t ≤ C' * Real.exp (ε * t)) := by
  have hsplit : ∀ (C t : ℝ), 0 ≤ t →
      (2 / 3) * Real.exp (t / 2) *
          (unitRieszApertureResolventRemainder t -
            -(C * Real.exp (-(1 / 2 - ε) * t))) =
        (2 / 3) * Real.exp (t / 2) * unitRieszApertureResolventRemainder t +
          (2 / 3) * C * Real.exp (ε * t) := by
    intro C t _ht
    have h : Real.exp (t / 2) * Real.exp (-(1 / 2 - ε) * t) = Real.exp (ε * t) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination ((2 / 3 : ℝ) * C) * h
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨16 + (2 / 3) * C, fun t ht => ?_⟩
    have hiff :=
      (unitRieszCompletedSourceResponse_re_ge_iff_apertureResolvent_le
        (B := -(C * Real.exp (-(1 / 2 - ε) * t))) ht).mp (hC t ht)
    rw [hsplit C t ht] at hiff
    have hbound := abs_unitRieszApertureResolventRemainder_normalized_le ht
    have hb := (abs_le.mp hbound).2
    have hone : (1 : ℝ) ≤ Real.exp (ε * t) := Real.one_le_exp (by positivity)
    nlinarith [hiff, hb, hone]
  · rintro ⟨C', hC'⟩
    refine ⟨(3 / 2) * (C' + 16), fun t ht => ?_⟩
    refine (unitRieszCompletedSourceResponse_re_ge_iff_apertureResolvent_le
      (B := -((3 / 2) * (C' + 16) * Real.exp (-(1 / 2 - ε) * t))) ht).mpr ?_
    rw [hsplit ((3 / 2) * (C' + 16)) t ht]
    have hbound := abs_unitRieszApertureResolventRemainder_normalized_le ht
    have hb := (abs_le.mp hbound).1
    have hone : (1 : ℝ) ≤ Real.exp (ε * t) := Real.one_le_exp (by positivity)
    nlinarith [hC' t ht, hb, hone]

end GaloisForLFunctions.RHTower
