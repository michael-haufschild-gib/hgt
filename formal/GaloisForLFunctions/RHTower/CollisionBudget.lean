import GaloisForLFunctions.RHTower.BurgersFieldDamping

/-!
# The exact pair field, and the collision budget

Two additions to the backward-flow collision criterion, both elementary and both exact.

**The exact field is a product, not a square.** The surrounding zeros enter the gap equation through
`Σ_y [(x₁ − y)(x₂ − y)]⁻¹`, not through `Σ_y (x − y)⁻²`. The two agree to leading order as the gap
closes, but the product form is what the Calogero velocities actually produce, with no approximation:
the single-term identity `(x₂ − y)⁻¹ − (x₁ − y)⁻¹ = −(x₂ − x₁)·[(x₁ − y)(x₂ − y)]⁻¹` converts the
velocity difference into the gap equation `−4/δ + 2δΔ` exactly. Every term of the product field is
positive for `y` outside the gap, since both factors then share a sign.

**The collision is fast compared with the field's own decay.** The frozen-field collision time is
`τ* = (1/4Δ)·log(2/(2−θ))` with `θ = Δu₀`, and the damping comparison `v' = −2v²` has timescale
`1/(2Δ)`. Their ratio is the dimensionless budget

  `2Δτ* = ½·log(2/(2 − θ))`,

which is bounded whenever the collision happens at all, and tends to zero with `θ`. Over that
interval the comparison field decays by the factor `(1 + ½log(2/(2−θ)))⁻¹`, strictly below one for
every `θ > 0`. So the damping does not merely fail to amplify the field — it supplies a definite
favourable drift during the collision, and the size of that drift is fixed by `θ` alone.

Together these say what a rigorous collision lemma has to absorb: only the transport term, over an
interval whose length is a bounded fraction of the damping timescale, against a quantified headwind.
-/

open Real

namespace RHTower

noncomputable section

/-- **The single-term product identity.** The contribution of one outside zero to the difference of
Calogero velocities is the gap times the reciprocal product. -/
theorem pair_field_term {x₁ x₂ y : ℝ} (h₁ : y ≠ x₁) (h₂ : y ≠ x₂) :
    (x₂ - y)⁻¹ - (x₁ - y)⁻¹ = -((x₂ - x₁) * ((x₁ - y) * (x₂ - y))⁻¹) := by
  have hy1 : x₁ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁)
  have hy2 : x₂ - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂)
  field_simp
  ring

/-- **The exact gap equation.** The difference of Calogero velocities of a pair, in a finite
surrounding field, is exactly `−4/δ + 2δ·Δ` with `Δ` the reciprocal-product field. -/
theorem gap_velocity_exact {x₁ x₂ : ℝ} (S : Finset ℝ) (hne : x₁ ≠ x₂)
    (hS : ∀ y ∈ S, y ≠ x₁ ∧ y ≠ x₂) :
    (-2) * ((x₂ - x₁)⁻¹ + ∑ y ∈ S, (x₂ - y)⁻¹)
        - (-2) * ((x₁ - x₂)⁻¹ + ∑ y ∈ S, (x₁ - y)⁻¹)
      = -4 / (x₂ - x₁) + 2 * (x₂ - x₁) * ∑ y ∈ S, ((x₁ - y) * (x₂ - y))⁻¹ := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hswap : (x₁ - x₂)⁻¹ = -(x₂ - x₁)⁻¹ := by
    rw [show x₁ - x₂ = -(x₂ - x₁) by ring, inv_neg]
  have hsum : (∑ y ∈ S, (x₂ - y)⁻¹) - ∑ y ∈ S, (x₁ - y)⁻¹
      = -((x₂ - x₁) * ∑ y ∈ S, ((x₁ - y) * (x₂ - y))⁻¹) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨h₁, h₂⟩ := hS y hy
    exact pair_field_term h₁ h₂
  rw [hswap]
  linear_combination (-2 : ℝ) * hsum

/-- **The collision budget.** Measured against the field's own damping timescale `1/(2Δ)`, the
frozen-field collision consumes exactly `½·log(2/(2−θ))` of it. -/
theorem collision_budget {D u₀ : ℝ} (hD : 0 < D) :
    2 * D * ((1 / (4 * D)) * Real.log (2 / (2 - D * u₀)))
      = Real.log (2 / (2 - D * u₀)) / 2 := by
  field_simp
  ring

/-- **The damping headwind is strictly favourable.** Over the collision interval the comparison
field decays by a factor strictly below one whenever the gap is genuinely sub-threshold. -/
theorem damping_headwind_lt_one {D u₀ : ℝ} (hD : 0 < D) (hpos : 0 < D * u₀)
    (hθ : D * u₀ < 2) :
    D / (1 + Real.log (2 / (2 - D * u₀)) / 2) < D := by
  have hden : (0 : ℝ) < 2 - D * u₀ := by linarith
  have hgt : (1 : ℝ) < 2 / (2 - D * u₀) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hlog : 0 < Real.log (2 / (2 - D * u₀)) := Real.log_pos hgt
  have h1 : (1 : ℝ) < 1 + Real.log (2 / (2 - D * u₀)) / 2 := by linarith
  calc D / (1 + Real.log (2 / (2 - D * u₀)) / 2) < D / 1 :=
        div_lt_div_of_pos_left hD one_pos h1
    _ = D := div_one D

end

end RHTower
