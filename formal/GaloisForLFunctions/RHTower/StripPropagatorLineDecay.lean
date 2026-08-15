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

open Complex MeasureTheory Set
open scoped ENNReal

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

/-! ## The uniform bound on a bounded frequency window -/

/-- **`(16)`'s propagator input.**  On a bounded frequency window the transport ratio is uniformly
bounded, with the explicit constant `K(1+X)^p`.  No decay is used: the window contributes only its
length, which is why the finite-interval estimate costs one power of the window and nothing more. -/
theorem exists_bound_stripPropagator_window (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {W : ℝ} (hW : 0 ≤ W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x t : ℝ, |x| ≤ W → |t| ≤ W →
      ‖(stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)).comp
          (stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I))‖ ≤ M := by
  obtain ⟨K, hK, hratio⟩ := exists_bound_stripPropagator_ratio hT hE hσ0 hσ1
  refine ⟨K * (1 + W) ^ (1 / 2 + σ), by positivity, fun x t hx ht => ?_⟩
  have hx0 : (0 : ℝ) < 1 + |x| := by positivity
  have ht0 : (0 : ℝ) < 1 + |t| := by positivity
  have hp : (0 : ℝ) < 1 / 2 + σ := by linarith
  have hxle : (1 + |x|) ^ (-(1 / 2 + σ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
    have := abs_nonneg x
    linarith
  have htle : (1 + |t|) ^ (1 / 2 + σ) ≤ (1 + W) ^ (1 / 2 + σ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hp.le
  have hxnn : (0 : ℝ) ≤ (1 + |x|) ^ (-(1 / 2 + σ)) := Real.rpow_nonneg hx0.le _
  have htnn : (0 : ℝ) ≤ (1 + |t|) ^ (1 / 2 + σ) := Real.rpow_nonneg ht0.le _
  calc ‖(stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)).comp
          (stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I))‖
      ≤ K * ((1 + |t|) ^ (1 / 2 + σ) * (1 + |x|) ^ (-(1 / 2 + σ))) := hratio x t
    _ ≤ K * ((1 + W) ^ (1 / 2 + σ) * 1) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul htle hxle hxnn (by positivity)) hK.le
    _ = K * (1 + W) ^ (1 / 2 + σ) := by ring

/-- **The propagated boundary vector, quantitatively.**  The squared line mass of `H(·+iσ)c` is at
most a fixed constant times `‖c‖²`, the constant being the mass of the weight at exponent `1+2σ`.
This is used twice in the one-block estimate: once for the homogeneous datum and once for the
boundary value accumulated at the edge of the frequency window. -/
theorem exists_bound_lintegral_sq_stripPropagator_apply (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : X,
      (∫⁻ x : ℝ, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * ‖c‖ ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  set M : ℝ≥0∞ := ∫⁻ x : ℝ, GaloisForLFunctions.HTGeometry.oneAddAbsWeight (2 * (1 / 2 + σ)) x
    with hMdef
  have hMfin : M ≠ ⊤ := by
    rw [hMdef]
    exact GaloisForLFunctions.HTGeometry.lintegral_oneAddAbsWeight_ne_top (by linarith)
  refine ⟨K ^ 2 * M.toReal, by positivity, fun c => ?_⟩
  have hpt : ∀ x : ℝ, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
      ≤ (K * ‖c‖) * (1 + |x|) ^ (-(1 / 2 + σ)) := by
    intro x
    calc ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
        ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖c‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (1 + |x|) ^ (-(1 / 2 + σ))) * ‖c‖ :=
          mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
      _ = (K * ‖c‖) * (1 + |x|) ^ (-(1 / 2 + σ)) := by ring
  have hbase := GaloisForLFunctions.HTGeometry.lintegral_sq_globalPowerTail_le hpt
  refine hbase.trans (le_of_eq ?_)
  have hMeq : M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMfin).symm
  rw [← hMdef]
  calc ENNReal.ofReal ((K * ‖c‖) ^ 2) * M
      = ENNReal.ofReal ((K * ‖c‖) ^ 2) * ENNReal.ofReal M.toReal := by rw [← hMeq]
    _ = ENNReal.ofReal ((K * ‖c‖) ^ 2 * M.toReal) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (K ^ 2 * M.toReal * ‖c‖ ^ 2) := by
        congr 1
        ring

end GaloisForLFunctions.RHTower
