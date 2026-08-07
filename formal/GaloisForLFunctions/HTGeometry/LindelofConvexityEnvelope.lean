/-
The unconditional envelope of the growth exponent, with the convexity premise discharged.

The two growth-exponent interfaces already in the tree carry different axiom sets.
`GrowthExponent` (`OffLineTransfer`) has midpoint convexity and the functional equation, and its
off-line transfer results are stated with the edge value `μ(1) = 0` as an explicit premise.
`ConvexGrowthExponent` (`DisproofRoute`) has full convexity, the functional equation,
nonnegativity, **and** `μ(1) = 0` as a field, together with the bridge `toGrowthExponent`.

So on the `ConvexGrowthExponent` side every premise of the form `μ(1) = 0` is free.  This file
discharges it and records what the discharged transfer gives:

* `μ(0) = 1/2` — the functional equation read at the edge;
* `μ(σ) ≥ 1/2 - σ` everywhere — the functional equation against nonnegativity;
* `μ(σ) ≤ (1 - σ)/2` on `[0, 1]` — the classical convexity bound in full, from the chord
  joining `(0, 1/2)` to `(1, 0)`;
* `μ(1/2) ≤ 1/4` — its value on the critical line, previously available only with an explicit
  `μ(1) = 0` premise (`convexity_bound_from_transfer`);
* antitonicity of `μ` on `(-∞, 1]`, and the general chord `μ(σ') ≤ ((1-σ')/(1-σ))·μ(σ)`
  generalising `mu_le_chord` from the base point `1/2` to an arbitrary base point;
* the resulting two-sided envelope, which is tight exactly at `σ = 0` and at `σ = 1`;
* nonnegativity of the transfer band width at the *true* critical value, discharging the
  `θ < 1/4` side condition of the band lemmas for the exponent itself.

No new analytic input is used: everything here is the existing convexity, functional-equation and
transfer machinery with its `μ(1) = 0` premise supplied by the structure's own field.
-/
import GaloisForLFunctions.HTGeometry.VanishingTransfer
import GaloisForLFunctions.HTGeometry.OffLineTransfer
import GaloisForLFunctions.HTGeometry.TransferBand

namespace HTGeometry

namespace ConvexGrowthExponent

variable (G : ConvexGrowthExponent)

/-! ### The edge value and the lower envelope -/

/-- **The exponent at the edge of the critical strip is `1/2`.**  The functional equation relates
`μ(0)` to `μ(1)`, and `μ(1) = 0` is a field of the structure, so no premise is needed. -/
theorem mu_zero : G.mu 0 = 1 / 2 := by
  have h := G.functionalEquation 0
  rw [show (1 : ℚ) - 0 = 1 by norm_num, G.atOne] at h
  linarith

/-- **The lower envelope.**  The functional equation against nonnegativity of the reflected value
gives `μ(σ) ≥ 1/2 - σ` at every abscissa.  This is the inequality form of
`mu_pos_of_lt_half`, valid also to the right of the critical line where it is vacuous. -/
theorem mu_ge_half_sub (σ : ℚ) : 1 / 2 - σ ≤ G.mu σ := by
  have hfe := G.functionalEquation σ
  have hnn := G.nonneg (1 - σ)
  linarith

/-! ### The chord from an arbitrary base point -/

/-- **The general chord to the edge.**  For `σ ≤ σ' ≤ 1` with `σ < 1`, convexity against
`μ(1) = 0` contracts the value at `σ` by the ratio of the distances to the edge.  The case
`σ = 1/2` is `mu_le_chord`. -/
theorem mu_le_chord_general {σ σ' : ℚ} (hσ : σ < 1) (h1 : σ ≤ σ') (h2 : σ' ≤ 1) :
    G.mu σ' ≤ (1 - σ') / (1 - σ) * G.mu σ := by
  have hd : 0 < 1 - σ := by linarith
  have ht0 : (0 : ℚ) ≤ (1 - σ') / (1 - σ) := by
    apply div_nonneg <;> linarith
  have ht1 : (1 - σ') / (1 - σ) ≤ 1 := by
    rw [div_le_one hd]; linarith
  have hcv := G.convex σ 1 ((1 - σ') / (1 - σ)) ht0 ht1
  have hne : (1 : ℚ) - σ ≠ 0 := ne_of_gt hd
  have hcancel : (1 - σ') / (1 - σ) * (1 - σ) = 1 - σ' := div_mul_cancel₀ _ hne
  have hpt : (1 - σ') / (1 - σ) * σ + (1 - (1 - σ') / (1 - σ)) * 1 = σ' := by
    have hrw : (1 - σ') / (1 - σ) * σ + (1 - (1 - σ') / (1 - σ)) * 1
        = 1 - (1 - σ') / (1 - σ) * (1 - σ) := by ring
    rw [hrw, hcancel]; ring
  rw [hpt, G.atOne] at hcv
  linarith

/-- **The exponent is antitone up to the edge.**  Moving right toward `σ = 1` cannot increase the
exponent: the chord contracts by a factor at most one and the values are nonnegative. -/
theorem mu_antitone {σ σ' : ℚ} (h1 : σ ≤ σ') (h2 : σ' ≤ 1) : G.mu σ' ≤ G.mu σ := by
  rcases eq_or_lt_of_le (le_trans h1 h2) with h | hlt
  · have hσ' : σ' = σ := le_antisymm (by rw [h]; exact h2) h1
    exact le_of_eq (congrArg G.mu hσ')
  · have hd : 0 < 1 - σ := by linarith
    have ht1 : (1 - σ') / (1 - σ) ≤ 1 := by
      rw [div_le_one hd]; linarith
    have ht0 : (0 : ℚ) ≤ (1 - σ') / (1 - σ) := by
      apply div_nonneg <;> linarith
    have hchord := G.mu_le_chord_general hlt h1 h2
    have hnn := G.nonneg σ
    nlinarith

/-! ### The classical convexity bound, unconditionally -/

/-- **The convexity bound in full.**  On the closed strip `[0, 1]` the exponent lies below the
chord joining `(0, 1/2)` to `(1, 0)`.  Both endpoint values are supplied by the structure —
`μ(0) = 1/2` from the functional equation and `μ(1) = 0` from `atOne` — so the statement carries no
premise beyond membership in the strip. -/
theorem mu_le_half_one_sub {σ : ℚ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) : G.mu σ ≤ (1 - σ) / 2 := by
  have hcv := G.convex 0 1 (1 - σ) (by linarith) (by linarith)
  have hpt : (1 - σ) * (0 : ℚ) + (1 - (1 - σ)) * 1 = σ := by ring
  rw [hpt, G.mu_zero, G.atOne] at hcv
  linarith

/-- **The convexity bound on the critical line, with the `μ(1) = 0` premise discharged.**  This is
`convexity_bound_from_transfer` applied through the structure's own edge value; equivalently the
vanishing transfer read at the vanishing point `s = 1`. -/
theorem mu_half_le_quarter : G.mu (1 / 2) ≤ 1 / 4 := by
  have h := G.mu_half_le_of_vanishing G.atOne
  linarith

/-- The same bound obtained through the `GrowthExponent` bridge, showing the two routes agree. -/
theorem mu_half_le_quarter_via_transfer : G.mu (1 / 2) ≤ 1 / 4 := by
  have h := convexity_bound_from_transfer G.toGrowthExponent G.atOne
  simpa only [toGrowthExponent] using h

/-! ### The two-sided envelope -/

/-- **The unconditional envelope.**  On the closed strip the exponent is trapped between the
functional equation's lower line and the convexity chord, and is nonnegative. -/
theorem mu_envelope {σ : ℚ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    1 / 2 - σ ≤ G.mu σ ∧ 0 ≤ G.mu σ ∧ G.mu σ ≤ (1 - σ) / 2 :=
  ⟨G.mu_ge_half_sub σ, G.nonneg σ, G.mu_le_half_one_sub h0 h1⟩

/-- **The envelope closes exactly at the two edges.**  At `σ = 0` the lower line and the chord both
equal `1/2`, and at `σ = 1` both bounds vanish, so the exponent is pinned there. -/
theorem mu_envelope_pinned : G.mu 0 = 1 / 2 ∧ G.mu 1 = 0 := ⟨G.mu_zero, G.atOne⟩

end ConvexGrowthExponent

/-- **The envelope has positive width away from the left edge.**  The chord exceeds the functional
equation's lower line by exactly `σ/2`, so the two bounds coincide only at `σ = 0`. -/
theorem envelope_width (σ : ℚ) : (1 - σ) / 2 - (1 / 2 - σ) = σ / 2 := by ring

/-- **The envelope bounds agree exactly at the left edge.** -/
theorem envelope_tight_iff (σ : ℚ) : (1 - σ) / 2 = 1 / 2 - σ ↔ σ = 0 := by
  constructor <;> intro h <;> linarith

namespace ConvexGrowthExponent

variable (G : ConvexGrowthExponent)

/-- **The transfer band at the true critical value has nonnegative width.**  The band lemmas are
stated for a record `θ` with the side condition `θ < 1/4`; for the exponent's own critical value the
convexity bound supplies `θ ≤ 1/4` unconditionally, which already forces the width to be
nonnegative to the right of the critical line. -/
theorem transferBandWidth_nonneg_of_true_value {σ : ℚ} (hσ : 1 / 2 ≤ σ) :
    0 ≤ transferBandWidth (G.mu (1 / 2)) σ := by
  rw [transferBandWidth_eq]
  have hq := G.mu_half_le_quarter
  nlinarith

/-- **Any vanishing point of the exponent lies in `[1/2, 1]` up to the edge value.**  The bracket of
the vanishing set, with both ends now premise-free: `μ(1) = 0` is a field, and every vanishing point
is at least `1/2`. -/
theorem vanishing_bracket_unconditional :
    G.mu 1 = 0 ∧ ∀ s : ℚ, G.mu s = 0 → 1 / 2 ≤ s :=
  ⟨G.atOne, fun _ hs => G.vanishing_ge_half hs⟩

end ConvexGrowthExponent

end HTGeometry
