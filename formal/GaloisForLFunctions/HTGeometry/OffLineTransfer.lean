/-
Transferring a growth bound from off the critical line to the critical line.

The growth exponent `μ` of the zeta function is convex, and the functional equation gives
`μ(σ) - μ(1-σ) = 1/2 - σ`.  Taking the convex combination of `σ` and `1-σ` at parameter `1/2` and
substituting the functional equation yields the exact transfer

    **μ(1/2) ≤ μ(σ) + (σ - 1/2)/2   for every σ.**

Equivalently, the symmetrised exponent `ν(σ) = μ(σ) + (σ - 1/2)/2` is convex and symmetric about
`σ = 1/2`, hence minimised there, with `ν(1/2) = μ(1/2)`.

Two instances.

* `μ(1) = 0` gives `μ(1/2) ≤ 1/4` — the convexity bound, recovered.
* The bound `μ(7/10) ≤ 3/40` gives `μ(1/2) ≤ 7/40`, better than convexity but short of `13/84`.

Reading the transfer backwards, an off-line bound at `σ` beats the record only when
`μ(σ) ≤ 13/84 - (σ - 1/2)/2`.  At `σ = 7/10` that threshold is `23/420`, and `3/40` misses it by
`17/840`.

Both hypotheses are stated as fields of a structure rather than assumed globally, so every theorem
below is unconditional given only convexity and the functional equation.
-/
import GaloisForLFunctions.HTGeometry.FunctionalEquationScaleContact

namespace HTGeometry

/-- The two standard properties of the growth exponent used here. -/
structure GrowthExponent where
  /-- The growth exponent `μ(σ)`. -/
  mu : ℚ → ℚ
  /-- Convexity, in midpoint form. -/
  midpointConvex : ∀ a b : ℚ, mu ((a + b) / 2) ≤ (mu a + mu b) / 2
  /-- The functional equation's effect on the exponent. -/
  functionalEquation : ∀ σ : ℚ, mu σ - mu (1 - σ) = 1 / 2 - σ

namespace GrowthExponent

variable (G : GrowthExponent)

/-- The symmetrised exponent. -/
def nu (σ : ℚ) : ℚ := G.mu σ + (σ - 1 / 2) / 2

/-- **The symmetrised exponent is symmetric about the critical line.** -/
theorem nu_symm (σ : ℚ) : G.nu (1 - σ) = G.nu σ := by
  unfold nu
  have h := G.functionalEquation σ
  linarith

/-- At the critical line the symmetrised exponent is the growth exponent. -/
@[simp] theorem nu_at_half : G.nu (1 / 2) = G.mu (1 / 2) := by
  unfold nu; ring

/-- **The transfer.**  A growth bound anywhere transfers to the critical line with a linear penalty. -/
theorem mu_half_le (σ : ℚ) : G.mu (1 / 2) ≤ G.mu σ + (σ - 1 / 2) / 2 := by
  have hmid := G.midpointConvex σ (1 - σ)
  have hpt : (σ + (1 - σ)) / 2 = 1 / 2 := by ring
  rw [hpt] at hmid
  have hfe := G.functionalEquation σ
  linarith

/-- Equivalently: the critical value is the minimum of the symmetrised exponent. -/
theorem nu_min_at_half (σ : ℚ) : G.nu (1 / 2) ≤ G.nu σ := by
  rw [nu_at_half]
  unfold nu
  exact G.mu_half_le σ

/-- **An off-line bound beats a target only above the transfer threshold.** -/
theorem transfer_threshold (σ θ : ℚ) (h : G.mu σ ≤ θ - (σ - 1 / 2) / 2) :
    G.mu (1 / 2) ≤ θ := by
  have := G.mu_half_le σ
  linarith

end GrowthExponent

/-! ### Instances -/

/-- **The convexity bound, recovered from the transfer at `σ = 1`.** -/
theorem convexity_bound_from_transfer (G : GrowthExponent) (h : G.mu 1 = 0) :
    G.mu (1 / 2) ≤ 1 / 4 := by
  have := G.mu_half_le 1
  rw [h] at this
  linarith

/-- The published bound at `σ = 7/10`. -/
def muSevenTenths : ℚ := 3 / 40

/-- **It transfers to `μ(1/2) ≤ 7/40`.** -/
theorem transfer_from_seven_tenths (G : GrowthExponent) (h : G.mu (7 / 10) ≤ muSevenTenths) :
    G.mu (1 / 2) ≤ 7 / 40 := by
  have ht := G.mu_half_le (7 / 10)
  unfold muSevenTenths at h
  linarith

/-- **Better than convexity, short of the record.** -/
theorem seven_fortieths_between : (13 : ℚ) / 84 < 7 / 40 ∧ (7 : ℚ) / 40 < 1 / 4 := by
  constructor <;> norm_num

/-- The bound at `σ = 7/10` that would be needed to match the record. -/
def recordThresholdAtSevenTenths : ℚ := 23 / 420

/-- **The threshold is `23/420`, and the published bound misses it by `17/840`.** -/
theorem seven_tenths_shortfall :
    recordThresholdAtSevenTenths = bourgainTheta - (7 / 10 - 1 / 2) / 2 ∧
      muSevenTenths - recordThresholdAtSevenTenths = 17 / 840 := by
  constructor
  · unfold recordThresholdAtSevenTenths bourgainTheta; norm_num
  · unfold muSevenTenths recordThresholdAtSevenTenths; norm_num

/-- **And such a bound would indeed match the record.** -/
theorem threshold_would_match_record (G : GrowthExponent)
    (h : G.mu (7 / 10) ≤ recordThresholdAtSevenTenths) :
    G.mu (1 / 2) ≤ bourgainTheta := by
  refine G.transfer_threshold (7 / 10) bourgainTheta ?_
  unfold recordThresholdAtSevenTenths bourgainTheta at *
  linarith

/-- **The transfer penalty grows linearly in the distance from the critical line**, at rate `1/2`.
So a bound at `σ` is worth the record only if it is better than the record by half the distance. -/
theorem transfer_penalty (σ σ' : ℚ) :
    ((σ' - 1 / 2) / 2) - ((σ - 1 / 2) / 2) = (σ' - σ) / 2 := by ring

/-- The threshold as a function of the abscissa, and its value at the two published points. -/
def transferThreshold (θ σ : ℚ) : ℚ := θ - (σ - 1 / 2) / 2

@[simp] theorem transferThreshold_at_half (θ : ℚ) : transferThreshold θ (1 / 2) = θ := by
  unfold transferThreshold; ring

/-- **The threshold reaches zero at `σ = 1/2 + 2θ`** — beyond that abscissa no finite bound can
transfer to the record, since `μ ≥ 0`. -/
theorem transferThreshold_zero_at (θ : ℚ) : transferThreshold θ (1 / 2 + 2 * θ) = 0 := by
  unfold transferThreshold; ring

/-- **For the current record that abscissa is `13/42 + 1/2 = 34/42 = 17/21`.**  An off-line bound is
useless for the record beyond `σ = 17/21 ≈ 0.8095`. -/
theorem transfer_useless_beyond :
    (1 : ℚ) / 2 + 2 * bourgainTheta = 17 / 21 := by
  unfold bourgainTheta; norm_num

/-- The published off-line point sits well inside the useful range. -/
theorem seven_tenths_inside : (7 : ℚ) / 10 < 17 / 21 := by norm_num

end HTGeometry
