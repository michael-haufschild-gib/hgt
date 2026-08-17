import GaloisForLFunctions.RHTower.SuzukiToeplitzSechWall
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The source-alignment slack law

A negative normalized-Hankel edge is useless to the source unless the source sees it.  The exact
amount by which it may fail to is the excess of the edge over its sharp threshold.

With `q` the required energy-ratio gain and `r` the edge, the two bottom-edge deficits of the even
and odd source spectral measures satisfy

`Δ_e + q Δ_o ≤ 1/(1-r) - q/(1+r) = (1+q)(r - r_*)/(1-r²)`,   `r_* = (q-1)/(q+1)`,

which is a one-line rearrangement of the energy-ratio requirement.  The right side vanishes exactly
at the sharp threshold, and `r_*` is the same Möbius expression `(κ_Ξ - κ₀)/(1 - κ_Ξ κ₀)` that the
`sech` wall coarsens.

Both deficits are integrals of nonnegative weights that are bounded below away from the edge, so
Markov's inequality converts the slack into an explicit mass bound for the part of each spectral
measure at distance `δ` from the edge.  At the sharp threshold the slack is zero, both measures
collapse onto the edge, and the two source directions become bottom-edge eigenvectors.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## The sharp threshold -/

/-- The required energy-ratio gain, from the target defect and the common-channel fidelity. -/
def alignmentGain (κXi κ₀ : ℝ) : ℝ := ((1 + κXi) * (1 - κ₀)) / ((1 - κXi) * (1 + κ₀))

/-- **`(242)`: the sharp edge threshold is the Möbius difference.** -/
theorem rStar_eq {κXi κ₀ : ℝ} (hXi : |κXi| < 1) (h0 : |κ₀| < 1) :
    (alignmentGain κXi κ₀ - 1) / (alignmentGain κXi κ₀ + 1)
      = (κXi - κ₀) / (1 - κXi * κ₀) := by
  rcases abs_lt.mp hXi with ⟨hx1, hx2⟩
  rcases abs_lt.mp h0 with ⟨h01, h02⟩
  have hd1 : (0 : ℝ) < 1 - κXi := by linarith
  have hd2 : (0 : ℝ) < 1 + κ₀ := by linarith
  have hn1 : (0 : ℝ) < 1 + κXi := by linarith
  have hn2 : (0 : ℝ) < 1 - κ₀ := by linarith
  have hden : (0 : ℝ) < 1 - κXi * κ₀ := by nlinarith
  have hd : (0 : ℝ) < (1 - κXi) * (1 + κ₀) := by positivity
  have hGp : 0 < alignmentGain κXi κ₀ := by
    rw [alignmentGain]; positivity
  rw [div_eq_div_iff (by linarith) (by linarith)]
  rw [alignmentGain]
  field_simp
  ring

/-- The gain exceeds one exactly when the target defect exceeds the common-channel fidelity. -/
theorem one_lt_alignmentGain {κXi κ₀ : ℝ} (hXi : |κXi| < 1) (h0 : |κ₀| < 1)
    (hlt : κ₀ < κXi) : 1 < alignmentGain κXi κ₀ := by
  rcases abs_lt.mp hXi with ⟨hx1, hx2⟩
  rcases abs_lt.mp h0 with ⟨h01, h02⟩
  rw [alignmentGain, lt_div_iff₀ (by nlinarith)]
  nlinarith

/-! ## The slack law -/

/-- **`(246)`, first form: the energy-ratio requirement is exactly the slack law.** -/
theorem slack_le {Ae Ao Δe Δo q r : ℝ} (hAo : 0 < Ao)
    (hΔe : Δe = 1 / (1 - r) - Ae) (hΔo : Δo = Ao - 1 / (1 + r))
    (hratio : q ≤ Ae / Ao) :
    Δe + q * Δo ≤ 1 / (1 - r) - q / (1 + r) := by
  have hAe : q * Ao ≤ Ae := by
    rw [le_div_iff₀ hAo] at hratio
    linarith
  rw [hΔe, hΔo]
  have : q * (Ao - 1 / (1 + r)) = q * Ao - q / (1 + r) := by ring
  rw [this]
  linarith

/-- **`(246)`, second form: the slack is the excess over the sharp threshold.** -/
theorem slack_eq {q r : ℝ} (hq : 0 < q) (hr : |r| < 1) :
    1 / (1 - r) - q / (1 + r) = (1 + q) * (r - (q - 1) / (q + 1)) / (1 - r ^ 2) := by
  rcases abs_lt.mp hr with ⟨hr1, hr2⟩
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have h2 : (0 : ℝ) < 1 + r := by linarith
  have h3 : (0 : ℝ) < q + 1 := by linarith
  have h4 : (1 : ℝ) - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h4]
  field_simp
  ring

/-- The slack vanishes exactly at the sharp threshold. -/
theorem slack_eq_zero_iff {q r : ℝ} (hq : 0 < q) (hr : |r| < 1) :
    1 / (1 - r) - q / (1 + r) = 0 ↔ r = (q - 1) / (q + 1) := by
  rcases abs_lt.mp hr with ⟨hr1, hr2⟩
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have h2 : (0 : ℝ) < 1 + r := by linarith
  have h3 : (0 : ℝ) < q + 1 := by linarith
  rw [slack_eq hq hr, div_eq_zero_iff]
  constructor
  · rintro (hnum | hden)
    · rcases mul_eq_zero.mp hnum with h | h
      · linarith
      · linarith
    · nlinarith
  · intro h
    left
    rw [h]
    ring

/-! ## The two pointwise edge weights -/

/-- The even bottom-edge weight dominates the edge distance up to `2(1-r)`. -/
theorem edge_le_even_weight {r t : ℝ} (hr1 : r < 1) (ht1 : -r ≤ t) (ht2 : t ≤ 1) :
    t + r ≤ 2 * (1 - r) * ((t + r) / ((1 - r) * (1 + t))) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have htr : (0 : ℝ) ≤ t + r := by linarith
  have hval : 2 * (1 - r) * ((t + r) / ((1 - r) * (1 + t)))
      = 2 * (t + r) / (1 + t) := by
    field_simp
  rw [hval, le_div_iff₀ h1t]
  nlinarith

/-- The odd bottom-edge weight dominates the edge distance up to `(1+r)²`. -/
theorem edge_le_odd_weight {r t : ℝ} (hr0 : 0 ≤ r) (ht1 : -r ≤ t) (ht2 : t < 1) :
    t + r ≤ (1 + r) ^ 2 * ((t + r) / ((1 - t) * (1 + r))) := by
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have htr : (0 : ℝ) ≤ t + r := by linarith
  have hval : (1 + r) ^ 2 * ((t + r) / ((1 - t) * (1 + r)))
      = (1 + r) * (t + r) / (1 - t) := by
    field_simp
  rw [hval, le_div_iff₀ h1t]
  nlinarith

/-- Away from the edge the even weight is bounded below. -/
theorem even_weight_ge {r t δ : ℝ} (hr1 : r < 1) (hδ : 0 < δ)
    (ht1 : -r + δ ≤ t) (ht2 : t ≤ 1) :
    δ / (2 * (1 - r)) ≤ (t + r) / ((1 - r) * (1 + t)) := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h1t2 : (1 : ℝ) + t ≤ 2 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have ha : δ * ((1 - r) * (1 + t)) ≤ δ * ((1 - r) * 2) := by
    nlinarith [mul_nonneg (mul_nonneg hδ.le h1r.le) (by linarith : (0 : ℝ) ≤ 2 - (1 + t))]
  have hb : δ * ((1 - r) * 2) ≤ (t + r) * (2 * (1 - r)) := by nlinarith
  linarith

/-- Away from the edge the odd weight is bounded below. -/
theorem odd_weight_ge {r t δ : ℝ} (hr0 : 0 ≤ r) (hδ : 0 < δ)
    (ht1 : -r + δ ≤ t) (ht2 : t < 1) :
    δ / ((1 + r) ^ 2) ≤ (t + r) / ((1 - t) * (1 + r)) := by
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1t2 : (1 : ℝ) - t ≤ 1 + r := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have ha : δ * ((1 - t) * (1 + r)) ≤ δ * ((1 + r) * (1 + r)) := by
    nlinarith [mul_nonneg (mul_nonneg hδ.le h1r.le) (by linarith : (0 : ℝ) ≤ (1 + r) - (1 - t))]
  have hb : δ * ((1 + r) * (1 + r)) ≤ (t + r) * ((1 + r) ^ 2) := by nlinarith
  linarith

/-! ## Markov's bound for the off-edge mass -/

/-- **`(247)`: the slack bounds the spectral mass away from the bottom edge.**  A nonnegative
weight bounded below on the far set converts an integral bound into a measure bound. -/
theorem measure_le_of_deficit {μ : Measure ℝ} {w : ℝ → ℝ} {E : Set ℝ} {S c Δ : ℝ}
    (hw : ∀ t, 0 ≤ w t) (hint : Integrable w μ)
    (hΔ : Δ = ∫ t, w t ∂μ) (hΔS : Δ ≤ S)
    (hmeas : MeasurableSet E) (hfin : μ E ≠ ⊤)
    (hlow : ∀ t ∈ E, c ≤ w t) :
    μ.real E * c ≤ S := by
  have hsub : ∫ t in E, w t ∂μ ≤ ∫ t, w t ∂μ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hw)
  have hlowint : μ.real E * c ≤ ∫ t in E, w t ∂μ := by
    have h := setIntegral_ge_of_const_le (μ := μ) (s := E) (f := w) (c := c)
      hmeas hfin hlow hint.integrableOn
    simpa [smul_eq_mul] using h
  rw [hΔ] at hΔS
  linarith

end RHTower
