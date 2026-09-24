import GaloisForLFunctions.RHTower.ZetaTwoThirdsOffLineMomentConstant
import GaloisForLFunctions.RHTower.OffLineMomentCensusBridge

/-!
# The mollified mean-square gate constant has an exponential floor

The two-thirds consumer turns a mollified mean-square gate `ZetaMollifiedMeanSquareGate R c` into

```text
4π · offLineMoment V ≤ (log c − (5/3) R + η) V     for every η > 0 and all large V.
```

The off-line first moment is a sum of nonnegative terms.  A coefficient `log c − (5/3) R < 0` would
therefore force `0 ≤ (negative) · V` for arbitrarily large `V`, which is false.  Hence **every**
gate constant obeys

```text
c ≥ exp((5/3) R),
```

an unconditional lower bound for the mollified mean square on the Levinson abscissa
`σ₀ = ½ − R / log T₂`, proved purely from zero counting.  Two consequences:

* the two-thirds Levinson consumer can never return a negative off-line moment bound, so this
  route cannot prove the Riemann Hypothesis — only `offLineMoment V ≤ C V` with `C ≥ 0`;
* the mollified mean square cannot be pushed below `exp((5/3)R)` times the window length, however
  the mollifier is chosen.  This is the sharp form of the mean-square floor.
-/

open Filter

namespace RHTower

noncomputable section

/-- **The structural obstruction.**  Any eventual linear upper bound for the off-line first moment
has a nonnegative slope: the moment is a sum of nonnegative terms, so a negative slope would force
`0 ≤ (negative) · V` at arbitrarily large `V`.

Consequently no consumer of this shape can prove the Riemann Hypothesis.  RH is equivalent to
`offLineMoment V = 0` for every `V`, a pointwise statement; the best an eventual linear bound can
say is `offLineMoment V = o(V)`, reached exactly when the slope is zero. -/
theorem offLineMoment_slope_nonneg {κ : ℝ}
    (h : ∀ᶠ V in Filter.atTop, 4 * Real.pi * offLineMoment V ≤ κ * V) : 0 ≤ κ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨V, hV1, hV2⟩ := (h.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
  have hnn : 0 ≤ offLineMoment V := offLineMoment_nonneg V
  have hπ : 0 < Real.pi := Real.pi_pos
  nlinarith [hV1, hV2, hnn, hπ, hcon]

/-- **The gate constant floor.**  Every mollified mean-square gate constant satisfies
`(5/3) R ≤ log c`. -/
theorem five_thirds_mul_le_log_of_zetaMollifiedMeanSquareGate
    {R c : ℝ} (hR : 0 < R) (hc : 1 ≤ c) (hg : ZetaMollifiedMeanSquareGate R c) :
    (5 / 3) * R ≤ Real.log c := by
  by_contra hcon
  push Not at hcon
  set η : ℝ := ((5 / 3) * R - Real.log c) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have h := eventually_offLineMoment_le_of_zetaGate_twoThirds hR hc hη0 hg
  obtain ⟨V, hV1, hV2⟩ := (h.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
  have hnn : 0 ≤ offLineMoment V := offLineMoment_nonneg V
  have hπ : 0 < Real.pi := Real.pi_pos
  have hneg : Real.log c - (5 / 3) * R + η < 0 := by rw [hη]; linarith
  nlinarith [hV1, hV2, hnn, hπ, hneg]

/-- **The exponential floor for the gate constant.** -/
theorem exp_five_thirds_mul_le_of_zetaMollifiedMeanSquareGate
    {R c : ℝ} (hR : 0 < R) (hc : 1 ≤ c) (hg : ZetaMollifiedMeanSquareGate R c) :
    Real.exp ((5 / 3) * R) ≤ c := by
  have h := five_thirds_mul_le_log_of_zetaMollifiedMeanSquareGate hR hc hg
  have hc0 : 0 < c := by linarith
  calc Real.exp ((5 / 3) * R) ≤ Real.exp (Real.log c) := Real.exp_le_exp.mpr h
    _ = c := Real.exp_log hc0

/-- **The no-go.**  No mollified mean-square gate exists below the exponential floor. -/
theorem not_zetaMollifiedMeanSquareGate_of_lt_exp
    {R c : ℝ} (hR : 0 < R) (hc : 1 ≤ c) (hlt : c < Real.exp ((5 / 3) * R)) :
    ¬ ZetaMollifiedMeanSquareGate R c := fun hg =>
  absurd (exp_five_thirds_mul_le_of_zetaMollifiedMeanSquareGate hR hc hg) (not_le.mpr hlt)

/-- **The two-thirds consumer never returns a negative coefficient.**  Whatever gate is supplied,
the resulting off-line moment bound has a nonnegative slope, so the route cannot force the
off-line first moment to vanish. -/
theorem zetaGate_twoThirds_coefficient_nonneg
    {R c : ℝ} (hR : 0 < R) (hc : 1 ≤ c) (hg : ZetaMollifiedMeanSquareGate R c) :
    0 ≤ Real.log c - (5 / 3) * R := by
  have h := five_thirds_mul_le_log_of_zetaMollifiedMeanSquareGate hR hc hg
  linarith

/-- **The general two-gate consumer never returns a negative coefficient either.** -/
theorem gates_coefficient_nonneg {κ₀ R c₁ c₂ δ : ℝ} (hκ₀ : 0 ≤ κ₀) (hR : 0 < R)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hδ : 0 < δ)
    (hmargin : κ₀ + 2 * δ < 1 - Real.log c₂ / R)
    (hg₁ : ZetaMollifiedMeanSquareGate R c₁) (hg₂ : LevinsonMeanSquareGate R c₂) :
    0 ≤ Real.log c₁ - (1 + κ₀) * R := by
  by_contra hcon
  push Not at hcon
  set η : ℝ := ((1 + κ₀) * R - Real.log c₁) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have h := eventually_offLineMoment_le_of_gates hκ₀ hR hc₁ hc₂ hδ hmargin hη0 hg₁ hg₂
  obtain ⟨V, hV1, hV2⟩ := (h.and (Filter.eventually_gt_atTop (0 : ℝ))).exists
  have hnn : 0 ≤ offLineMoment V := offLineMoment_nonneg V
  have hπ : 0 < Real.pi := Real.pi_pos
  have hneg : Real.log c₁ - (1 + κ₀) * R + η < 0 := by rw [hη]; linarith
  nlinarith [hV1, hV2, hnn, hπ, hneg]

end

end RHTower
