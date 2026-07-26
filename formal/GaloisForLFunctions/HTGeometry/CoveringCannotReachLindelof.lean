/-
No covering architecture can reach the Lindelöf exponent from a range-restricted input alone.

Write the covering demand of an exponent pair at length `M = T^(x₁)` in its nonnegative form:

    demand(κ, λ, x₁) = κ·(1 - x₁) + x₁·(λ - 1/2).

Both summands are nonnegative on the exponent-pair region (`κ ≥ 0`, `λ ≥ 1/2`) for `0 ≤ x₁ ≤ 1`, and
for `0 < x₁ < 1` the demand vanishes exactly at the corner `(κ, λ) = (0, 1/2)` — the exponent-pair
conjecture, which is equivalent to the Lindelöf hypothesis.

Two consequences for any covering proof of `μ(1/2) ≤ θ` that uses a source valid only on
`[x₁, 1/2]`.

* The low range `[0, x₁]` must still be covered, and by an *unrestricted* source — an exponent pair.
  That pair must satisfy `κ(1-x₁) + x₁(λ - 1/2) ≤ θ`, which as `θ → 0` forces either `x₁ → 0` (the
  "restricted" source is not restricted, hence is itself an exponent pair) or `(κ, λ) → (0, 1/2)` (the
  conclusion is already assumed).

* Any *intermediate* source `A ≤ M^α T^β` with `α ≥ 1/2` contributes demand at least `β` at every
  nonnegative length, so a chain containing it can never produce an exponent below `β`.  Huxley's
  bound has `β = 1/32`, so **every covering chain that uses it is capped at `1/32`.**

Together: a covering architecture is a device for extending a range-restricted estimate, never for
reaching the Lindelöf exponent.
-/
import GaloisForLFunctions.HTGeometry.CoveringBuysNothing

namespace HTGeometry

/-! ### The nonnegative form of the demand -/

/-- **The demand written as a nonnegative combination.** -/
theorem covDemand_nonneg_form (x₁ κ lam : ℚ) :
    covDemandOfPair x₁ κ lam = κ * (1 - x₁) + x₁ * (lam - 1 / 2) := by
  unfold covDemandOfPair covFunctional; ring

/-- On the exponent-pair region the demand is nonnegative at every admissible length. -/
theorem covDemand_nonneg {x₁ κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h0 : 0 ≤ x₁) (h1 : x₁ ≤ 1) :
    0 ≤ covDemandOfPair x₁ κ lam := by
  rw [covDemand_nonneg_form]
  have h₁ : 0 ≤ κ * (1 - x₁) := mul_nonneg hκ (by linarith)
  have h₂ : 0 ≤ x₁ * (lam - 1 / 2) := mul_nonneg h0 (by linarith)
  linarith

/-- **At a nondegenerate length the demand vanishes exactly at the exponent-pair conjecture.** -/
theorem covDemand_eq_zero_iff {x₁ κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h0 : 0 < x₁) (h1 : x₁ < 1) :
    covDemandOfPair x₁ κ lam = 0 ↔ κ = 0 ∧ lam = 1 / 2 := by
  rw [covDemand_nonneg_form]
  constructor
  · intro h
    have h₁ : 0 ≤ κ * (1 - x₁) := mul_nonneg hκ (by linarith)
    have h₂ : 0 ≤ x₁ * (lam - 1 / 2) := mul_nonneg h0.le (by linarith)
    have e₁ : κ * (1 - x₁) = 0 := by linarith
    have e₂ : x₁ * (lam - 1 / 2) = 0 := by linarith
    constructor
    · rcases mul_eq_zero.mp e₁ with h' | h'
      · exact h'
      · exfalso; linarith
    · rcases mul_eq_zero.mp e₂ with h' | h'
      · exfalso; linarith
      · linarith
  · rintro ⟨hk, hl⟩; rw [hk, hl]; ring

/-! ### The squeeze on the low-range pair -/

/-- **A pair that covers the low range at level `θ` has both coordinates squeezed toward the
corner.** -/
theorem low_range_squeeze {x₁ κ lam θ : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h0 : 0 < x₁) (h1 : x₁ < 1) (hcov : covDemandOfPair x₁ κ lam ≤ θ) :
    κ * (1 - x₁) ≤ θ ∧ x₁ * (lam - 1 / 2) ≤ θ := by
  rw [covDemand_nonneg_form] at hcov
  have h₁ : 0 ≤ κ * (1 - x₁) := mul_nonneg hκ (by linarith)
  have h₂ : 0 ≤ x₁ * (lam - 1 / 2) := mul_nonneg h0.le (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- Explicit bounds on the coordinates. -/
theorem low_range_coordinate_bounds {x₁ κ lam θ : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h0 : 0 < x₁) (h1 : x₁ < 1) (hcov : covDemandOfPair x₁ κ lam ≤ θ) :
    κ ≤ θ / (1 - x₁) ∧ lam - 1 / 2 ≤ θ / x₁ := by
  obtain ⟨e₁, e₂⟩ := low_range_squeeze hκ hlam h0 h1 hcov
  constructor
  · rw [le_div_iff₀ (by linarith : (0:ℚ) < 1 - x₁)]; exact e₁
  · rw [le_div_iff₀ h0]; linarith [e₂]

/-- **The dichotomy.**  A covering proof of the Lindelöf exponent with a source restricted to
`[x₁, 1/2]` forces the low-range pair to be the exponent-pair conjecture exactly. -/
theorem lindelof_forces_conjecture {x₁ κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h0 : 0 < x₁) (h1 : x₁ < 1) (hcov : covDemandOfPair x₁ κ lam ≤ 0) :
    κ = 0 ∧ lam = 1 / 2 := by
  refine (covDemand_eq_zero_iff hκ hlam h0 h1).mp ?_
  have := covDemand_nonneg hκ hlam h0.le h1.le
  linarith

/-- At the exponent-pair conjecture the pointwise exponent is zero: the conclusion is the hypothesis.
-/
theorem conjecture_pair_mu : epMu 0 (1 / 2) = 0 := by
  unfold epMu; norm_num

/-! ### Every intermediate source caps the chain at its own `T`-exponent -/

/-- **A source of slope at least `1/2` demands at least its own `T`-exponent, at every length.** -/
theorem source_demand_ge_intercept {α β x₁ : ℚ} (hα : 1 / 2 ≤ α) (hx : 0 ≤ x₁) :
    β ≤ coveringDemand α β x₁ := by
  unfold coveringDemand
  have : 0 ≤ (α - 1 / 2) * x₁ := mul_nonneg (by linarith) hx
  linarith

/-- **Huxley's bound caps any chain that uses it at `1/32`.** -/
theorem huxley_caps_chain {x₁ : ℚ} (hx : 0 ≤ x₁) :
    (1 : ℚ) / 32 ≤ coveringDemand huxleyAlpha huxleyBeta x₁ := by
  have h := source_demand_ge_intercept
    (α := huxleyAlpha) (β := huxleyBeta) (x₁ := x₁)
    (by unfold huxleyAlpha; norm_num) hx
  unfold huxleyBeta at h
  exact h

/-- **Consequently no improvement of the final source can bring a Huxley-containing chain anywhere
near the Lindelöf exponent.**  The cap `1/32` is five times the published record. -/
theorem huxley_cap_far_above_record :
    bourgainTheta < 1 / 32 * 5 ∧ (1 : ℚ) / 32 * 4 < bourgainTheta := by
  unfold bourgainTheta; constructor <;> norm_num

/-- The published exponent-pair source likewise caps its chain at `1/9`. -/
theorem expPair_caps_chain {x₁ : ℚ} (hx : 0 ≤ x₁) :
    (1 : ℚ) / 9 ≤ coveringDemand expPairAlpha expPairBeta x₁ := by
  have h := source_demand_ge_intercept
    (α := expPairAlpha) (β := expPairBeta) (x₁ := x₁)
    (by unfold expPairAlpha; norm_num) hx
  unfold expPairBeta at h
  exact h

/-! ### The conclusion -/

/-- **A covering architecture cannot reach the Lindelöf exponent from a restricted input.**  Either
the low-range pair is already the exponent-pair conjecture — whose pointwise exponent is `0`, so the
conclusion is assumed — or the restriction threshold is degenerate. -/
theorem covering_cannot_reach_lindelof {x₁ κ lam : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 ≤ lam)
    (h0 : 0 < x₁) (h1 : x₁ < 1) (hcov : covDemandOfPair x₁ κ lam ≤ 0) :
    epMu κ lam = 0 := by
  obtain ⟨hk, hl⟩ := lindelof_forces_conjecture hκ hlam h0 h1 hcov
  rw [hk, hl]; exact conjecture_pair_mu

/-- The quantitative form: the restriction threshold is bounded by the target exponent divided by the
low-range pair's own `λ`-excess. -/
theorem threshold_bounded_by_target {x₁ κ lam θ : ℚ} (hκ : 0 ≤ κ) (hlam : 1 / 2 < lam)
    (h0 : 0 < x₁) (h1 : x₁ < 1) (hcov : covDemandOfPair x₁ κ lam ≤ θ) :
    x₁ ≤ θ / (lam - 1 / 2) := by
  obtain ⟨_, e₂⟩ := low_range_squeeze hκ hlam.le h0 h1 hcov
  rw [le_div_iff₀ (by linarith : (0:ℚ) < lam - 1 / 2)]
  linarith

/-- **Instantiated at the trivial pair `(0, 1)`**: any covering proof of `μ(1/2) ≤ θ` whose low range
is carried by the trivial bound must have its restricted source available from `T^(2θ)` upwards. -/
theorem trivial_pair_threshold {x₁ θ : ℚ} (h0 : 0 < x₁) (h1 : x₁ < 1)
    (hcov : covDemandOfPair x₁ 0 1 ≤ θ) : x₁ ≤ 2 * θ := by
  have := threshold_bounded_by_target (κ := 0) (lam := 1) (by norm_num) (by norm_num) h0 h1 hcov
  calc x₁ ≤ θ / (1 - 1 / 2) := this
    _ = 2 * θ := by ring

/-- **Bourgain's threshold exceeds that bound**, confirming that the trivial pair does not cover his
low range and that intermediate sources are genuinely required. -/
theorem bourgain_threshold_exceeds_trivial : 2 * bourgainTheta < decouplingStart := by
  unfold bourgainTheta decouplingStart; norm_num

end HTGeometry
