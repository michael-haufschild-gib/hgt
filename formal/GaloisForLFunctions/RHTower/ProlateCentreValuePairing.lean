import GaloisForLFunctions.RHTower.ProlateProfileDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The rescaled profile pairs at its centre value

The Hermite rescaling `u_c(ξ) = Φ(ξ/√c)` flattens the profile: for a fixed integrable weight `W`,
each point `ξ` is dragged to the origin as the bandwidth grows, so

```text
⟨u_c, W⟩ = ∫ Φ(ξ/√c) W(ξ) dξ ⟶ Φ(0) · ∫ W .
```

Only two facts about `Φ` are used — continuity at the origin and global boundedness — and both are
free for a time–band eigenfunction: it is continuous by construction, and
`abs_le_of_bandTransform_eigen` makes it decay, hence bounded.

This is the non-degeneracy engine of the prolate-to-oscillator comparison.  Applied to `W = φₙ` it
says the pairing that sits in the *denominator* of the ladder pin tends to `Φ(0)·∫φₙ`, a fixed
nonzero number whenever the mode does not vanish at the centre; applied to the explicit weight
`ξ²(ξ²−2n−1)φₙ + 2ξφₙ′` it says the *numerator* stays bounded.  The quotient is then `O(1/c)`.
-/

open MeasureTheory Filter

open scoped Topology

noncomputable section

namespace RHTower

/-- Dragging to the origin: `ξ/√c → 0` as the bandwidth grows. -/
theorem tendsto_div_sqrt_atTop (ξ : ℝ) :
    Tendsto (fun c : ℝ => ξ / Real.sqrt c) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop

/-- **The rescaled pairing converges to the centre value.** -/
theorem tendsto_integral_rescaled_mul {Φ : ℝ → ℝ} {B : ℝ}
    (hΦ : Continuous Φ) (hbdd : ∀ x, |Φ x| ≤ B)
    {W : ℝ → ℝ} (hW : Integrable W) :
    Tendsto (fun c : ℝ => ∫ ξ, Φ (ξ / Real.sqrt c) * W ξ) atTop (𝓝 (Φ 0 * ∫ ξ, W ξ)) := by
  have hlimint : (∫ ξ, Φ 0 * W ξ) = Φ 0 * ∫ ξ, W ξ := MeasureTheory.integral_const_mul _ _
  rw [← hlimint]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun ξ => B * |W ξ|) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun c => ?_
    exact ((hΦ.comp (continuous_id.div_const (Real.sqrt c))).aestronglyMeasurable).mul hW.1
  · refine Eventually.of_forall fun c => ?_
    refine Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hbdd _) (abs_nonneg _)
  · exact (hW.abs).const_mul B
  · refine Eventually.of_forall fun ξ => ?_
    have hinner : Tendsto (fun c : ℝ => Φ (ξ / Real.sqrt c)) atTop (𝓝 (Φ 0)) :=
      (hΦ.continuousAt).tendsto.comp (tendsto_div_sqrt_atTop ξ)
    exact hinner.mul_const (W ξ)

/-! ## The ladder distance vanishes -/

/-- **The rescaled eigenvalue reaches the oscillator rung.**  If the ladder pin holds in the form

```text
d(c) · ⟨u_c, V⟩ = ⟨u_c, W⟩ / c
```

with `V` and `W` integrable and the centre pairing `Φ(0)·∫V` nonzero, then `d(c) → 0`.  The
numerator stays bounded because the pairing converges; the denominator carries the whole bandwidth.
-/
theorem tendsto_zero_of_ladderPin {Φ : ℝ → ℝ} {B : ℝ}
    (hΦ : Continuous Φ) (hbdd : ∀ x, |Φ x| ≤ B)
    {W V : ℝ → ℝ} (hW : Integrable W) (hV : Integrable V)
    (hne : Φ 0 * (∫ ξ, V ξ) ≠ 0) {d : ℝ → ℝ}
    (hd : ∀ c : ℝ, d c * (∫ ξ, Φ (ξ / Real.sqrt c) * V ξ)
      = (∫ ξ, Φ (ξ / Real.sqrt c) * W ξ) / c) :
    Tendsto d atTop (𝓝 0) := by
  have hN := tendsto_integral_rescaled_mul hΦ hbdd hW
  have hD := tendsto_integral_rescaled_mul hΦ hbdd hV
  have h1 : Tendsto (fun c : ℝ => (∫ ξ, Φ (ξ / Real.sqrt c) * W ξ) / c) atTop (𝓝 0) := by
    have h := hN.mul tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using h
  have h2 : Tendsto (fun c : ℝ => ((∫ ξ, Φ (ξ / Real.sqrt c) * W ξ) / c)
      / (∫ ξ, Φ (ξ / Real.sqrt c) * V ξ)) atTop (𝓝 0) := by
    have h := h1.div hD hne
    rw [zero_div] at h
    exact h
  refine h2.congr' ?_
  filter_upwards [hD.eventually_ne hne] with c hc
  rw [div_eq_iff hc]
  exact (hd c).symm

end RHTower

end
