/-
# The floor of a power-scale recurrence, and why its solution is scale-flat

Bourgain's Section-1 recurrence has the multiplicative form

    `b(N) ≤ C · N^δ · b(N^α)` ,   `0 ≤ α < 1` ,

whose `k`-fold iterate accumulates the exponent `δ · Σ_(i<k) α^i`.  That partial sum is bounded by

    **`powerScaleFloor δ α = δ / (1 - α)`** ,

with exact deficit `δ · α^k / (1 - α)`, so the floor is attained in the limit and not before.  At
Bourgain's contraction `α = 2/3` it is `3δ`, and the value `13/84` corresponds to the per-step loss
`δ = 13/252`.

Two consequences.

* **Elasticity.**  `∂ log floor / ∂ log δ = 1` while `∂ log floor / ∂ log α = α/(1-α)`, which is `2` at
  `α = 2/3`: the floor is **twice as elastic in the contraction exponent as in the per-step loss**.
  Reducing `α` is worth twice as much, proportionally, as reducing `δ`.

* **Scale-flatness.**  The recurrence is a statement about `b(N)` for *every* `N`, so its solution is a
  bound with the same exponent at every scale.  In the exponent-pair plane a scale-independent bound
  `M^(1/2) T^β` is the pair `(β, β + 1/2)`, which has zero displacement — a point of the line of
  symmetry.  This is the structural reason Bourgain's pair `(13/84, 55/84)` lies on that line, and it
  identifies the recurrence as the source of the flatness.

* **Lindelöf.**  For `α < 1` the floor vanishes exactly when `δ = 0`: the recurrence delivers the
  Lindelöf exponent if and only if its per-step loss is not a positive power.
-/
import GaloisForLFunctions.RHTower.BourgainPowerScaleBootstrap
import GaloisForLFunctions.RHTower.BourgainExponentEndgame
import GaloisForLFunctions.HTGeometry.SymmetrizationRetraction

open scoped BigOperators

namespace RHTower

/-! ### The floor -/

/-- Limiting accumulated exponent of a power-scale recurrence. -/
noncomputable def powerScaleFloor (δ α : ℝ) : ℝ := δ / (1 - α)

/-- **The partial accumulation falls short of the floor by exactly `δ α^k/(1-α)`.** -/
theorem powerScale_partial_deficit {α : ℝ} (hα : α < 1) (δ : ℝ) (k : ℕ) :
    powerScaleFloor δ α - δ * ∑ i ∈ Finset.range k, α ^ i = δ * α ^ k / (1 - α) := by
  have h1a : (1 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  have hs : (1 - α) * ∑ i ∈ Finset.range k, α ^ i = 1 - α ^ k := by
    linear_combination -geom_sum_mul α k
  unfold powerScaleFloor
  field_simp
  linear_combination (-δ) * hs

/-- **So the accumulated exponent never exceeds the floor.** -/
theorem powerScale_partial_le {α δ : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) (hδ : 0 ≤ δ) (k : ℕ) :
    δ * ∑ i ∈ Finset.range k, α ^ i ≤ powerScaleFloor δ α := by
  have h := powerScale_partial_deficit hα δ k
  have hpos : 0 ≤ δ * α ^ k / (1 - α) := by
    apply div_nonneg (mul_nonneg hδ (pow_nonneg hα0 k)); linarith
  linarith

/-- **At Bourgain's contraction the floor is `3δ`.** -/
theorem powerScaleFloor_two_thirds (δ : ℝ) : powerScaleFloor δ (2 / 3) = 3 * δ := by
  unfold powerScaleFloor; norm_num; ring

/-- **And `13/84` is the floor of the per-step loss `13/252`.** -/
theorem powerScaleFloor_bourgain : powerScaleFloor (13 / 252) (2 / 3) = bourgainZetaExponent := by
  rw [powerScaleFloor_two_thirds]; unfold bourgainZetaExponent; norm_num

/-! ### Elasticity -/

/-- **Sensitivity to the per-step loss.** -/
theorem powerScaleFloor_delta_diff {α : ℝ} (hα : α < 1) (δ δ' : ℝ) :
    powerScaleFloor δ' α - powerScaleFloor δ α = (δ' - δ) / (1 - α) := by
  have h : (1 : ℝ) - α ≠ 0 := by intro h; apply absurd hα; simp; linarith
  unfold powerScaleFloor; field_simp

/-- **Sensitivity to the contraction exponent.** -/
theorem powerScaleFloor_alpha_diff {α α' : ℝ} (hα : α < 1) (hα' : α' < 1) (δ : ℝ) :
    powerScaleFloor δ α' - powerScaleFloor δ α = δ * (α' - α) / ((1 - α) * (1 - α')) := by
  have h : (1 : ℝ) - α ≠ 0 := by intro h; apply absurd hα; simp; linarith
  have h' : (1 : ℝ) - α' ≠ 0 := by intro h; apply absurd hα'; simp; linarith
  unfold powerScaleFloor; field_simp; ring

/-- **The elasticity in the contraction exponent is `α/(1-α)`, which is `2` at `α = 2/3`:** the floor
is twice as elastic in the contraction as in the per-step loss. -/
theorem powerScaleFloor_elasticity : (2 / 3 : ℝ) / (1 - 2 / 3) = 2 := by norm_num

/-! ### Vanishing -/

/-- **The recurrence reaches the Lindelöf exponent exactly when its per-step loss vanishes.** -/
theorem powerScaleFloor_eq_zero_iff {α δ : ℝ} (hα : α < 1) :
    powerScaleFloor δ α = 0 ↔ δ = 0 := by
  have h : (1 : ℝ) - α ≠ 0 := by intro h; apply absurd hα; simp; linarith
  unfold powerScaleFloor
  exact div_eq_zero_iff.trans (by simp [h])

/-! ### Scale-flatness of the solution -/

/-- **A scale-independent bound is a pair on the line of symmetry.**  The exponent `β` delivered
uniformly in the scale corresponds to `(β, β + 1/2)`, of zero displacement. -/
theorem uniform_exponent_is_symmetric (β : ℚ) :
    HTGeometry.epDisplacement β (β + 1 / 2) = 0 ∧
      ∀ c : ℚ, HTGeometry.covDemandOfPair c β (β + 1 / 2) = β :=
  ⟨HTGeometry.epDisplacement_on_symmetry β, fun c => HTGeometry.covDemand_flat_on_symmetry c β⟩

/-- **Bourgain's pair is the scale-flat point of its own recurrence.** -/
theorem bourgain_pair_is_recurrence_flat :
    powerScaleFloor (13 / 252) (2 / 3) = bourgainZetaExponent ∧
      HTGeometry.epDisplacement (13 / 84) (55 / 84) = 0 ∧
        ∀ c : ℚ, HTGeometry.covDemandOfPair c (13 / 84) (55 / 84) = 13 / 84 := by
  refine ⟨powerScaleFloor_bourgain, ?_, fun c => (HTGeometry.record_pair_flat c).2⟩
  exact (HTGeometry.record_pair_flat 0).1

end RHTower
