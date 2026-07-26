/-
The subconvexity record as a vanishing statement.

Combining the off-line transfer `μ(1/2) ≤ μ(σ) + (σ - 1/2)/2` with a vanishing point gives the clean
consequence

    **μ(σ*) = 0  ⟹  μ(1/2) ≤ (σ* - 1/2)/2** ,

where `σ*` is the left endpoint of the zero set of `μ`.  Three readings.

* At `σ* = 1` it returns the convexity bound `1/4`.
* At `σ* = 1/2 + 2·(13/84) = 17/21` it returns **exactly the current record `13/84`**.
* At `σ* = 1/2` it returns `μ(1/2) = 0` — the Lindelöf hypothesis.

So the whole subconvexity problem is the question of how far left of `σ = 1` the exponent can be shown
to vanish, at the exchange rate `dμ(1/2)/dσ* = 1/2`.  Proving `μ(s) = 0` for any `s < 17/21` beats the
record; the distance from `17/21` to `1/2` is `13/42`.

Read backwards, `σ* ≥ 2μ(1/2) + 1/2`, which for `μ(1/2) ≥ 0` recovers the functional equation's
bracket `σ* ≥ 1/2` and shows that any strict improvement of that bracket refutes the hypothesis.
-/
import GaloisForLFunctions.HTGeometry.VanishingAbscissa

namespace HTGeometry

namespace ConvexGrowthExponent

variable (G : ConvexGrowthExponent)

/-! ### The vanishing transfer -/

/-- **A vanishing point bounds the critical value by half its distance from the critical line.** -/
theorem mu_half_le_of_vanishing {s : ℚ} (hs : G.mu s = 0) :
    G.mu (1 / 2) ≤ (s - 1 / 2) / 2 := by
  have h := G.toGrowthExponent.mu_half_le s
  simp only [toGrowthExponent] at h
  rw [hs] at h
  linarith

/-- **Read backwards: the vanishing point is at least `2μ(1/2) + 1/2`.** -/
theorem vanishing_ge {s : ℚ} (hs : G.mu s = 0) : 2 * G.mu (1 / 2) + 1 / 2 ≤ s := by
  have := G.mu_half_le_of_vanishing hs
  linarith

/-- **The functional equation's bracket, recovered**: any vanishing point is at least `1/2`. -/
theorem vanishing_ge_half {s : ℚ} (hs : G.mu s = 0) : 1 / 2 ≤ s := by
  have h := G.vanishing_ge hs
  have := G.nonneg (1 / 2)
  linarith

/-- **A vanishing point strictly below `1/2 + 2θ` beats the record `θ`.** -/
theorem vanishing_beats_record {s θ : ℚ} (hs : G.mu s = 0) (h : s < 1 / 2 + 2 * θ) :
    G.mu (1 / 2) < θ := by
  have := G.mu_half_le_of_vanishing hs
  linarith

/-- **A vanishing point at exactly `1/2 + 2θ` matches the record.** -/
theorem vanishing_matches_record {s θ : ℚ} (hs : G.mu s = 0) (h : s = 1 / 2 + 2 * θ) :
    G.mu (1 / 2) ≤ θ := by
  have hb := G.mu_half_le_of_vanishing hs
  rw [h] at hb
  linarith

/-- **Vanishing at the critical line is the Lindelöf hypothesis.** -/
theorem vanishing_at_half_is_lindelof (hs : G.mu (1 / 2) = 0) : G.mu (1 / 2) = 0 := hs

/-- **The exchange rate is `1/2`.**  Moving a vanishing point left by `δ` lowers the bound on the
critical value by `δ/2`. -/
theorem exchange_rate (s δ : ℚ) : (s - 1 / 2) / 2 - ((s - δ) - 1 / 2) / 2 = δ / 2 := by ring

end ConvexGrowthExponent

/-! ### The record as a vanishing abscissa -/

/-- The abscissa whose vanishing reproduces a given record. -/
def recordVanishingAbscissa (θ : ℚ) : ℚ := 1 / 2 + 2 * θ

/-- **For the current record it is `17/21`.** -/
@[simp] theorem recordVanishingAbscissa_bourgain :
    recordVanishingAbscissa bourgainTheta = 17 / 21 := by
  unfold recordVanishingAbscissa bourgainTheta; norm_num

/-- It agrees with the abscissa beyond which the off-line transfer is useless. -/
theorem recordVanishingAbscissa_eq_transfer_zero (θ : ℚ) :
    transferThreshold θ (recordVanishingAbscissa θ) = 0 := by
  unfold recordVanishingAbscissa
  exact transferThreshold_zero_at θ

/-- **For the convexity bound it is `1`.** -/
@[simp] theorem recordVanishingAbscissa_convexity : recordVanishingAbscissa (1 / 4) = 1 := by
  unfold recordVanishingAbscissa; norm_num

/-- **For the Lindelöf target it is `1/2`.** -/
@[simp] theorem recordVanishingAbscissa_lindelof : recordVanishingAbscissa 0 = 1 / 2 := by
  unfold recordVanishingAbscissa; norm_num

/-- The abscissa is increasing in the record, so better records correspond to abscissae further
left. -/
theorem recordVanishingAbscissa_mono {θ θ' : ℚ} (h : θ < θ') :
    recordVanishingAbscissa θ < recordVanishingAbscissa θ' := by
  unfold recordVanishingAbscissa; linarith

/-- **The distance still to travel**: from the record's abscissa `17/21` to the Lindelöf abscissa
`1/2` is `13/42`. -/
theorem distance_to_lindelof :
    recordVanishingAbscissa bourgainTheta - recordVanishingAbscissa 0 = 13 / 42 := by
  rw [recordVanishingAbscissa_bourgain, recordVanishingAbscissa_lindelof]; norm_num

/-- And from the convexity bound's abscissa `1` to the record's `17/21` is `4/21` — the ground
covered since 1921, in these coordinates. -/
theorem distance_covered :
    recordVanishingAbscissa (1 / 4) - recordVanishingAbscissa bourgainTheta = 4 / 21 := by
  rw [recordVanishingAbscissa_convexity, recordVanishingAbscissa_bourgain]; norm_num

/-- **The whole problem in one line.**  A century of subconvexity has moved the vanishing abscissa
from `1` to `17/21`, a distance of `4/21`; the Lindelöf hypothesis is the remaining `13/42`, which is
`13/8` times as far. -/
theorem the_ledger :
    recordVanishingAbscissa (1 / 4) - recordVanishingAbscissa bourgainTheta = 4 / 21 ∧
      recordVanishingAbscissa bourgainTheta - recordVanishingAbscissa 0 = 13 / 42 ∧
      (13 : ℚ) / 42 = (13 / 8) * (4 / 21) := by
  refine ⟨distance_covered, distance_to_lindelof, by norm_num⟩

/-! ### Bracket completeness -/

/-- **Any strict improvement of the lower bracket refutes the hypothesis.**  If every vanishing point
exceeds `1/2`, then `μ(1/2) ≠ 0`. -/
theorem lower_bracket_improvement_refutes (G : ConvexGrowthExponent)
    (h : ∀ s : ℚ, G.mu s = 0 → 1 / 2 < s) : G.mu (1 / 2) ≠ 0 := by
  intro hzero
  exact absurd (h (1 / 2) hzero) (by norm_num)

/-- **Any improvement of the upper bracket below `17/21` improves the record.** -/
theorem upper_bracket_improvement_improves_record (G : ConvexGrowthExponent) {s : ℚ}
    (hs : G.mu s = 0) (h : s < 17 / 21) : G.mu (1 / 2) < bourgainTheta := by
  refine G.vanishing_beats_record hs ?_
  unfold bourgainTheta
  linarith

end HTGeometry
