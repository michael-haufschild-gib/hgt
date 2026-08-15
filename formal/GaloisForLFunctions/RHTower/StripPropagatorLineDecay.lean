import GaloisForLFunctions.RHTower.GammaRatioLineDecay
import GaloisForLFunctions.HTGeometry.GlobalPowerTailSquareIntegrable

/-!
# The Gamma propagator on a shifted line, at the exact exponent

Combining the operator bound for the propagator with the quantitative decay of the strip carrier
gives the card's displayed pair

`‖H(x+iσ)‖ ≤ C(1+|x|)^{-p}`,   `‖H(x+iσ)^{-1}‖ ≤ C(1+|x|)^{p}`,   `p = 1/2 + σ`.

The transport ratio bound follows at once, and — unlike the paper statement — it needs no ordering
or sign hypothesis on the two frequencies: the two factors are estimated separately, so

`‖H(x+iσ)H(t+iσ)^{-1}‖ ≤ C[(1+|t|)/(1+|x|)]^p`

holds for every pair.  The restriction to an outward tail in the paper is only how the estimate is
used, not what it requires.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **`(3)`, propagator half at the exact exponent.** -/
theorem exists_bound_stripPropagator_line (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
        ≤ K * (1 + |x|) ^ (-(1 / 2 + σ)) := by
  obtain ⟨C, hC, hCle⟩ := exists_bound_suzukiGammaStripCarrier hσ0 hσ1
  refine ⟨Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖) * C,
    by positivity, fun x => ?_⟩
  have hbase := norm_stripPropagator_shift_le hT hE hσ0 hσ1 x
  refine hbase.trans ?_
  calc Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖)
        * suzukiGammaStripCarrier σ x
      ≤ Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖)
        * (C * (1 + |x|) ^ (-(1 / 2 + σ))) :=
        mul_le_mul_of_nonneg_left (hCle x) (by positivity)
    _ = Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖) * C
        * (1 + |x|) ^ (-(1 / 2 + σ)) := by ring

/-- **`(3)`, inverse half at the exact exponent.** -/
theorem exists_bound_stripPropagatorInv_line (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
        ≤ K * (1 + |x|) ^ (1 / 2 + σ) := by
  obtain ⟨C, hC, hCle⟩ := exists_bound_suzukiGammaStripCarrier_inv hσ0 hσ1
  refine ⟨Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖) * C,
    by positivity, fun x => ?_⟩
  have hbase := norm_stripPropagatorInv_shift_le hT hE hσ0 hσ1 x
  refine hbase.trans ?_
  calc Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖)
        * (suzukiGammaStripCarrier σ x)⁻¹
      ≤ Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖)
        * (C * (1 + |x|) ^ (1 / 2 + σ)) :=
        mul_le_mul_of_nonneg_left (hCle x) (by positivity)
    _ = Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖) * C
        * (1 + |x|) ^ (1 / 2 + σ) := by ring

/-- **`(5)`: the transport ratio bound, with no ordering hypothesis.** -/
theorem exists_bound_stripPropagator_ratio (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x t : ℝ,
      ‖(stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)).comp
          (stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I))‖
        ≤ K * ((1 + |t|) ^ (1 / 2 + σ) * (1 + |x|) ^ (-(1 / 2 + σ))) := by
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  refine ⟨K₁ * K₂, by positivity, fun x t => ?_⟩
  have hx0 : (0 : ℝ) < 1 + |x| := by positivity
  have ht0 : (0 : ℝ) < 1 + |t| := by positivity
  calc ‖(stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)).comp
          (stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I))‖
      ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
        * ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (K₁ * (1 + |x|) ^ (-(1 / 2 + σ))) * (K₂ * (1 + |t|) ^ (1 / 2 + σ)) :=
        mul_le_mul (hb₁ x) (hb₂ t) (norm_nonneg _) (by positivity)
    _ = K₁ * K₂ * ((1 + |t|) ^ (1 / 2 + σ) * (1 + |x|) ^ (-(1 / 2 + σ))) := by ring

/-! ## The homogeneous component is square integrable on the line -/

/-- **The homogeneous term of a shifted-line solution is in `L²(ℝ)`.**  The propagator exponent
`p = 1/2 + σ` exceeds `1/2` for every `σ > 0`, which is exactly the threshold at which the square of
the propagator becomes integrable — the reason Theorem 2's homogeneous remainder needs no further
hypothesis. -/
theorem lintegral_sq_stripPropagator_apply_ne_top (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (c : X) :
    (∫⁻ x : ℝ, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2) ≠ ⊤ := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  refine GaloisForLFunctions.HTGeometry.lintegral_sq_globalPowerTail_ne_top
    (C := K * ‖c‖) (p := 1 / 2 + σ) (by linarith) fun x => ?_
  calc ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
      ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖c‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (K * (1 + |x|) ^ (-(1 / 2 + σ))) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
    _ = K * ‖c‖ * (1 + |x|) ^ (-(1 / 2 + σ)) := by ring

end GaloisForLFunctions.RHTower
