/-
Two measurements of the remaining distance: on the disproof side and on the proof side.

**Disproof side.**  A refutation needs `μ(σ) > 0` at some `σ ∈ (1/2, 1)`, i.e. a lower bound of the
form `exp(δ · log T)` — logarithmic exponent `1`.  The strongest known omega-results in that range
have the shape `exp(c (log T)^(1-σ) (log log T)^(-σ))`, of logarithmic exponent `1 - σ`.  So the
deficit in the logarithmic exponent is

    **1 - (1 - σ) = σ** ,

which on `[1/2, 1]` is at least `1/2`, attained only at the critical line.  Everywhere on the interval
the known lower bounds are at most the square root of what a refutation requires, measured in the
exponent of `log T`.

**Proof side.**  At abscissa `σ` the record threshold is `θ - (σ-1/2)/2` and the convexity prediction
is `2θ(1-σ)`.  Their ratio

    **R(σ) = (θ - (σ-1/2)/2) / (2θ(1-σ))**

is the fraction of the convexity prediction one must achieve.  It equals `1` at the critical line and
decreases to `0` at `σ = 1/2 + 2θ`.  So there is a genuine trade-off: near the line only a slight
improvement on convexity is needed, but at the hardest point; far from the line the point is easier
but the required improvement is proportionally larger.  At `σ = 7/10` with `θ = 13/84` the fraction is
`23/39`.
-/
import GaloisForLFunctions.HTGeometry.DisproofRoute

namespace HTGeometry

/-! ### The refutation deficit, in the exponent of `log T` -/

/-- Logarithmic exponent of the strongest known omega-results at abscissa `σ`. -/
def omegaLogExponent (σ : ℚ) : ℚ := 1 - σ

/-- Logarithmic exponent a refutation requires. -/
def refutationLogExponent : ℚ := 1

/-- The deficit between them. -/
def refutationDeficit (σ : ℚ) : ℚ := refutationLogExponent - omegaLogExponent σ

/-- **The deficit is exactly `σ`.** -/
@[simp] theorem refutationDeficit_eq (σ : ℚ) : refutationDeficit σ = σ := by
  unfold refutationDeficit refutationLogExponent omegaLogExponent; ring

/-- **On the closed interval the deficit is at least `1/2`,** attained only at the critical line. -/
theorem refutationDeficit_ge_half {σ : ℚ} (h : 1 / 2 ≤ σ) : 1 / 2 ≤ refutationDeficit σ := by
  rw [refutationDeficit_eq]; exact h

/-- **And the known logarithmic exponent is at most `1/2` there.** -/
theorem omegaLogExponent_le_half {σ : ℚ} (h : 1 / 2 ≤ σ) : omegaLogExponent σ ≤ 1 / 2 := by
  unfold omegaLogExponent; linarith

/-- **So known omega-results reach at most the square root of what a refutation needs**, uniformly on
the interval: their logarithmic exponent is at most half of the required one. -/
theorem omega_at_most_square_root {σ : ℚ} (h : 1 / 2 ≤ σ) :
    2 * omegaLogExponent σ ≤ refutationLogExponent := by
  unfold omegaLogExponent refutationLogExponent; linarith

/-- The deficit grows toward the edge of the strip. -/
theorem refutationDeficit_mono {σ σ' : ℚ} (h : σ < σ') :
    refutationDeficit σ < refutationDeficit σ' := by
  rw [refutationDeficit_eq, refutationDeficit_eq]; exact h

/-- **The disproof trade-off.**  The deficit is smallest just above the critical line, where the
amplifier is weakest; it is largest near `σ = 1`, where the amplifier is strongest. -/
theorem disproof_tradeoff :
    refutationDeficit (1 / 2) = 1 / 2 ∧ refutationAmplifier (1 / 2) = 1 ∧
      refutationDeficit (7 / 10) = 7 / 10 ∧ refutationAmplifier (7 / 10) = 5 / 3 := by
  refine ⟨by simp, amplifier_at_half, by simp, amplifier_at_seven_tenths⟩

/-! ### The band ratio on the proof side -/

/-- The fraction of the convexity prediction that must be achieved at abscissa `σ`. -/
def bandRatio (θ σ : ℚ) : ℚ := transferThreshold θ σ / convexityPrediction θ σ

/-- **On the critical line the whole prediction must be achieved.** -/
theorem bandRatio_at_half {θ : ℚ} (hθ : θ ≠ 0) : bandRatio θ (1 / 2) = 1 := by
  unfold bandRatio
  rw [transferThreshold_at_half, convexityPrediction_at_half]
  exact div_self hθ

/-- **At `σ = 7/10` with the current record the fraction is `23/39`.** -/
@[simp] theorem bandRatio_at_seven_tenths : bandRatio bourgainTheta (7 / 10) = 23 / 39 := by
  unfold bandRatio transferThreshold convexityPrediction bourgainTheta; norm_num

/-- **The fraction vanishes at `σ = 1/2 + 2θ`,** beyond which no finite bound helps. -/
theorem bandRatio_zero_at (θ : ℚ) : bandRatio θ (1 / 2 + 2 * θ) = 0 := by
  unfold bandRatio
  rw [transferThreshold_zero_at]
  simp

/-- The fraction is strictly less than one off the critical line. -/
theorem bandRatio_lt_one {θ σ : ℚ} (hθ0 : 0 < θ) (hθ : θ < 1 / 4)
    (h1 : 1 / 2 < σ) (h2 : σ < 1) : bandRatio θ σ < 1 := by
  unfold bandRatio
  have hden : 0 < convexityPrediction θ σ := by
    unfold convexityPrediction; nlinarith
  rw [div_lt_one hden]
  unfold transferThreshold convexityPrediction
  nlinarith

/-- **The trade-off, stated.**  Moving away from the critical line lowers the fraction of the
convexity prediction that must be achieved, but every barrier the campaign proved lives at
`σ = 1/2` exactly, so the point itself becomes easier. -/
theorem proof_side_tradeoff :
    bandRatio bourgainTheta (7 / 10) < 1 ∧
      transferBandWidth bourgainTheta (7 / 10) = 4 / 105 ∧
      transferBandWidth bourgainTheta (1 / 2) = 0 := by
  refine ⟨by rw [bandRatio_at_seven_tenths]; norm_num, band_at_seven_tenths, ?_⟩
  rw [transferBandWidth_eq]; ring

/-! ### The two sides compared -/

/-- **Both sides are measured, and neither is closed.**  On the proof side a fraction `23/39` of the
convexity prediction at `σ = 7/10` suffices, of which `15/32` of the band is already banked; on the
disproof side the logarithmic-exponent deficit is `7/10`, with nothing banked. -/
theorem both_sides_measured :
    bandRatio bourgainTheta (7 / 10) = 23 / 39 ∧
      capturedFraction = 15 / 32 ∧
      refutationDeficit (7 / 10) = 7 / 10 ∧
      omegaLogExponent (7 / 10) = 3 / 10 := by
  refine ⟨bandRatio_at_seven_tenths, rfl, by simp, ?_⟩
  unfold omegaLogExponent; norm_num

end HTGeometry
