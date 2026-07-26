/-
The disproof side: a single point of positivity anywhere in `(1/2, 1)` refutes the Lindelöf
hypothesis.

Convexity of the growth exponent has been used so far in one direction only — from a bound at `σ` to
a bound at `1/2`.  Run it the other way.  For `1/2 ≤ σ ≤ 1`, write `σ` as the convex combination

    σ = t·(1/2) + (1 - t)·1 ,     t = 2(1 - σ) ,

so convexity together with `μ(1) = 0` gives

    **μ(σ) ≤ 2(1 - σ)·μ(1/2)** ,   equivalently   **μ(1/2) ≥ μ(σ) / (2(1 - σ))**   for `σ < 1`.

Hence:

* the Lindelöf hypothesis `μ(1/2) = 0` forces `μ(σ) = 0` on the whole interval `[1/2, 1]`;
* conversely a **single** abscissa `σ₀ ∈ (1/2, 1)` with `μ(σ₀) > 0` refutes it.

This is the exact converse of the convexity prediction used in the transfer band, and it is the
campaign's first statement bearing on the *disproof* side.  None of the fixed-point barriers proved
for `σ = 1/2` applies to it: they are all statements about the critical line, whereas a refutation may
be witnessed anywhere in the open interval.
-/
import GaloisForLFunctions.HTGeometry.TransferBand

namespace HTGeometry

/-- A growth exponent with full convexity, the functional equation, nonnegativity, and the known
value at `σ = 1`. -/
structure ConvexGrowthExponent where
  /-- The growth exponent `μ(σ)`. -/
  mu : ℚ → ℚ
  /-- Convexity. -/
  convex : ∀ a b t : ℚ, 0 ≤ t → t ≤ 1 → mu (t * a + (1 - t) * b) ≤ t * mu a + (1 - t) * mu b
  /-- The functional equation's effect on the exponent. -/
  functionalEquation : ∀ σ : ℚ, mu σ - mu (1 - σ) = 1 / 2 - σ
  /-- Nonnegativity. -/
  nonneg : ∀ σ : ℚ, 0 ≤ mu σ
  /-- The classical value on the edge of the critical strip. -/
  atOne : mu 1 = 0

namespace ConvexGrowthExponent

variable (G : ConvexGrowthExponent)

/-- Midpoint convexity, specialised from convexity. -/
theorem midpointConvex (a b : ℚ) : G.mu ((a + b) / 2) ≤ (G.mu a + G.mu b) / 2 := by
  have h := G.convex a b (1 / 2) (by norm_num) (by norm_num)
  have hpt : (1 / 2 : ℚ) * a + (1 - 1 / 2) * b = (a + b) / 2 := by ring
  rw [hpt] at h
  linarith

/-- The associated `GrowthExponent`, so the transfer results apply. -/
def toGrowthExponent : GrowthExponent :=
  { mu := G.mu
    midpointConvex := G.midpointConvex
    functionalEquation := G.functionalEquation }

/-! ### The reverse direction of convexity -/

/-- **Convexity from `(1/2, μ(1/2))` to `(1, 0)`.** -/
theorem mu_le_chord {σ : ℚ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) :
    G.mu σ ≤ 2 * (1 - σ) * G.mu (1 / 2) := by
  have ht0 : (0 : ℚ) ≤ 2 * (1 - σ) := by linarith
  have ht1 : 2 * (1 - σ) ≤ 1 := by linarith
  have h := G.convex (1 / 2) 1 (2 * (1 - σ)) ht0 ht1
  have hpt : 2 * (1 - σ) * (1 / 2 : ℚ) + (1 - 2 * (1 - σ)) * 1 = σ := by ring
  rw [hpt, G.atOne] at h
  linarith

/-- **The reverse transfer.**  A value off the critical line bounds the critical value from below. -/
theorem mu_half_ge {σ : ℚ} (h1 : 1 / 2 ≤ σ) (h2 : σ < 1) :
    G.mu σ / (2 * (1 - σ)) ≤ G.mu (1 / 2) := by
  have hpos : 0 < 2 * (1 - σ) := by linarith
  rw [div_le_iff₀ hpos]
  have := G.mu_le_chord h1 h2.le
  linarith [this]

/-! ### The disproof principle -/

/-- **A single point of positivity in the open interval refutes the Lindelöf hypothesis.** -/
theorem positivity_refutes_lindelof {σ : ℚ} (h1 : 1 / 2 < σ) (h2 : σ < 1)
    (hpos : 0 < G.mu σ) : 0 < G.mu (1 / 2) := by
  have hle := G.mu_le_chord (le_of_lt h1) h2.le
  have hpos2 : (0 : ℚ) < 2 * (1 - σ) := by linarith
  nlinarith

/-- **Conversely the Lindelöf hypothesis forces the exponent to vanish on the whole interval.** -/
theorem lindelof_forces_vanishing {σ : ℚ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1)
    (hLH : G.mu (1 / 2) = 0) : G.mu σ = 0 := by
  have hle := G.mu_le_chord h1 h2
  rw [hLH] at hle
  have := G.nonneg σ
  linarith

/-- **The equivalence.**  `μ(1/2) = 0` if and only if `μ` vanishes identically on `[1/2, 1]`. -/
theorem lindelof_iff_vanishes :
    G.mu (1 / 2) = 0 ↔ ∀ σ : ℚ, 1 / 2 ≤ σ → σ ≤ 1 → G.mu σ = 0 := by
  constructor
  · intro hLH σ h1 h2
    exact G.lindelof_forces_vanishing h1 h2 hLH
  · intro h
    exact h (1 / 2) le_rfl (by norm_num)

/-- The refutation threshold at an abscissa: any positive lower bound suffices, and it amplifies by
the factor `1/(2(1-σ))`. -/
theorem refutation_amplification {σ v : ℚ} (h1 : 1 / 2 ≤ σ) (h2 : σ < 1)
    (hv : v ≤ G.mu σ) : v / (2 * (1 - σ)) ≤ G.mu (1 / 2) := by
  have hpos : 0 < 2 * (1 - σ) := by linarith
  have := G.mu_half_ge h1 h2
  have hmono : v / (2 * (1 - σ)) ≤ G.mu σ / (2 * (1 - σ)) := by
    apply div_le_div_of_nonneg_right' hv hpos
  linarith
where
  div_le_div_of_nonneg_right' {a b c : ℚ} (hab : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
    rw [div_le_div_iff_of_pos_right hc]; exact hab

end ConvexGrowthExponent

/-! ### The amplification factor -/

/-- The factor by which a lower bound at `σ` amplifies on the critical line. -/
def refutationAmplifier (σ : ℚ) : ℚ := 1 / (2 * (1 - σ))

/-- At `σ = 7/10` the amplifier is `5/3`. -/
@[simp] theorem amplifier_at_seven_tenths : refutationAmplifier (7 / 10) = 5 / 3 := by
  unfold refutationAmplifier; norm_num

/-- **The amplifier is `1` on the critical line and grows without bound toward `σ = 1`.** -/
theorem amplifier_at_half : refutationAmplifier (1 / 2) = 1 := by
  unfold refutationAmplifier; norm_num

/-- The amplifier increases with the abscissa. -/
theorem amplifier_mono {σ σ' : ℚ} (h1 : σ < σ') (h2 : σ' < 1) :
    refutationAmplifier σ < refutationAmplifier σ' := by
  unfold refutationAmplifier
  have hpos : 0 < 2 * (1 - σ') := by linarith
  have hpos' : 0 < 2 * (1 - σ) := by linarith
  rw [div_lt_div_iff₀ hpos' hpos]
  linarith

/-- **So the further from the critical line a positivity witness is found, the more it proves.**  A
lower bound `v` at `σ` yields `v/(2(1-σ))` on the critical line; at `σ = 7/10` that is `5v/3`. -/
theorem amplification_summary :
    refutationAmplifier (1 / 2) = 1 ∧ refutationAmplifier (7 / 10) = 5 / 3 ∧
      refutationAmplifier (1 / 2) < refutationAmplifier (7 / 10) := by
  refine ⟨amplifier_at_half, amplifier_at_seven_tenths, ?_⟩
  rw [amplifier_at_half, amplifier_at_seven_tenths]; norm_num

end HTGeometry
