import GaloisForLFunctions.RHTower.WallThirdIntegrationByParts
import GaloisForLFunctions.RHTower.WallTailRayComposition
import GaloisForLFunctions.HTGeometry.PowerTailBochnerBound

/-!
# `(48)`: the transported three-fold remainder decays quadratically

After three integrations by parts the remaining integrand is the inverse propagator against the
amplitude `∂D₂`, of size

`K₂(1+|t|)^p · C(1+|t|)^{-3} ≤ K₂C|t|^{p-3}`,

whose tail past a frequency `x ≥ 1` is `O(x^{p-2})` — absolutely convergent for every `p < 2`, which
is the whole range `0 < σ < 1`.  One more power of the propagator's own decay `x^{-p}` makes the
transported tail

`‖H(x)∫_x^∞ E ∂D₂‖ = O(x^{-2})`,

so it survives multiplication by the frequency and remains square integrable on a terminal ray.
The two-fold remainder does not: its tail integrates `t^{p-2}`, which diverges as soon as `p > 1`.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [CompleteSpace X] in
/-- The operator form of the second derivative is continuous. -/
theorem continuous_wallGeneratorD2 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (wallGeneratorD2 X σ) := by
  have h : Continuous fun t : ℝ => wallScalarD2 σ t • (ContinuousLinearMap.id ℂ X) :=
    (continuous_wallScalarD2 hσ0 hσ1).smul continuous_const
  exact h

/-- **The three-fold remainder integrand decays like `|t|^{p-3}`.** -/
theorem norm_wallThirdAmplitude_le {σ L μ₀ K₂ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {t : ℝ} (ht : 1 ≤ |t|) (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
        (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t‖
      ≤ (K₂ * wallAmplitude3Const μ₀) * |t| ^ (-(3 - (1 / 2 + σ))) := by
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hW : ‖wallPhaseMap E T σ L t‖ ≤ K₂ * (1 + |t|) ^ (1 / 2 + σ) := by
    rw [wallPhaseMap, norm_smul, norm_expPhase, one_mul]
    exact hb₂ t
  have hA := norm_invFamilyProduct2Deriv_wallGeneratorShift_le' (T := T) (L := L) hσ0 hσ1 hμ ht hfloor
  have hC3 : 0 ≤ wallAmplitude3Const μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitude3Const]
    positivity
  have hprod : ‖wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
      (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t‖
      ≤ (K₂ * (1 + |t|) ^ (1 / 2 + σ)) * (wallAmplitude3Const μ₀ * ((1 + |t|)⁻¹) ^ 3) :=
    (norm_mul_le _ _).trans (mul_le_mul hW hA (norm_nonneg _)
      (mul_nonneg hK₂ (Real.rpow_nonneg (by positivity) _)))
  refine hprod.trans ?_
  have hpow : ((1 + |t|)⁻¹) ^ 3 = (1 + |t|) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast (1 + |t|)⁻¹ 3, ← Real.rpow_neg_one (1 + |t|), ← Real.rpow_mul
      (by positivity)]
    norm_num
  have hcomb : (1 + |t|) ^ (1 / 2 + σ) * ((1 + |t|)⁻¹) ^ 3
      = (1 + |t|) ^ (-(3 - (1 / 2 + σ))) := by
    rw [hpow, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hmono : (1 + |t|) ^ (-(3 - (1 / 2 + σ))) ≤ |t| ^ (-(3 - (1 / 2 + σ))) := by
    refine Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
  calc (K₂ * (1 + |t|) ^ (1 / 2 + σ)) * (wallAmplitude3Const μ₀ * ((1 + |t|)⁻¹) ^ 3)
      = (K₂ * wallAmplitude3Const μ₀) * ((1 + |t|) ^ (1 / 2 + σ) * ((1 + |t|)⁻¹) ^ 3) := by ring
    _ = (K₂ * wallAmplitude3Const μ₀) * (1 + |t|) ^ (-(3 - (1 / 2 + σ))) := by rw [hcomb]
    _ ≤ (K₂ * wallAmplitude3Const μ₀) * |t| ^ (-(3 - (1 / 2 + σ))) :=
        mul_le_mul_of_nonneg_left hmono (mul_nonneg hK₂ hC3)

/-- The three-fold remainder integrand is continuous where the floor is open. -/
theorem continuousOn_wallThirdIntegrand {σ L : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) {S : Set ℝ}
    (hgap : ∀ t ∈ S, 0 < wallFloor T σ t + L) :
    ContinuousOn (fun t : ℝ => wallPhaseMap E T σ L t * invFamilyProduct2Deriv
      (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
      (wallGeneratorD3 X σ) t) S := by
  have hW : ContinuousOn (wallPhaseMap E T σ L) S :=
    (continuous_wallPhaseMap hEdiff hE hEne hσ0 hσ1 L).continuousOn
  have hA := continuousOn_invFamilyProduct2Deriv_of_unit
    (C := wallGeneratorShift T σ L) (C₁ := wallGeneratorD1 X σ) (C₂ := wallGeneratorD2 X σ)
    (C₃ := wallGeneratorD3 X σ) (S := S)
    (fun t _ => hasDerivAt_wallGeneratorShift T hσ0 hσ1 L t)
    (fun t ht => isUnit_wallGeneratorShift hσ0 hσ1 (hgap t ht))
    (continuous_wallGeneratorD1 hσ0 hσ1).continuousOn
    (continuous_wallGeneratorD2 hσ0 hσ1).continuousOn
    (continuous_wallGeneratorD3 hσ0 hσ1).continuousOn
  exact hW.mul hA

/-- **The three-fold remainder's tail past a frequency.** -/
theorem norm_wallThirdTail_le {σ L μ₀ K₂ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {x : ℝ} (hx : 1 ≤ x) (hfloor : ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L) :
    ‖∫ t in Ioi x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv (wallGeneratorShift T σ L)
        (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) (wallGeneratorD3 X σ) t‖
      ≤ (K₂ * wallAmplitude3Const μ₀)
        * (x ^ (1 - (3 - (1 / 2 + σ))) / ((3 - (1 / 2 + σ)) - 1)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  refine norm_integral_Ioi_le_powerTail (q := 3 - (1 / 2 + σ))
    (C := K₂ * wallAmplitude3Const μ₀) (by linarith) hx0 (fun t ht => ?_)
  have ht1 : (1 : ℝ) ≤ |t| := by
    have : x < t := ht
    rw [abs_of_pos (lt_trans hx0 this)]
    linarith
  exact norm_wallThirdAmplitude_le hσ0 hσ1 hμ hb₂ hK₂ ht1 (hfloor t ht)

/-- **`(48)`: the transported three-fold remainder is `O(x^{-2})`.** -/
theorem norm_wallThirdTail_transported_le {σ L μ₀ K₁ K₂ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {x : ℝ} (hx : 1 ≤ x) (hfloor : ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L) :
    ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        * ∫ t in Ioi x, wallPhaseMap E T σ L t * invFamilyProduct2Deriv
          (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ)
          (wallGeneratorD3 X σ) t‖
      ≤ (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * x ^ (-(2 : ℝ)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxabs : |x| = x := abs_of_pos hx0
  have hC3 : 0 ≤ wallAmplitude3Const μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitude3Const]
    positivity
  have hH : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * x ^ (-(1 / 2 + σ)) := by
    have hb := hb₁ x
    rw [hxabs] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hK₁)
    refine Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
  have hM := norm_wallThirdTail_le (E := E) hσ0 hσ1 hμ hb₂ hK₂ hx hfloor
  have hMnn : (0 : ℝ) ≤ (K₂ * wallAmplitude3Const μ₀)
      * (x ^ (1 - (3 - (1 / 2 + σ))) / ((3 - (1 / 2 + σ)) - 1)) := by
    have : (0 : ℝ) < (3 - (1 / 2 + σ)) - 1 := by linarith
    have hp : (0 : ℝ) < x ^ (1 - (3 - (1 / 2 + σ))) := Real.rpow_pos_of_pos hx0 _
    positivity
  refine le_trans (norm_mul_le _ _) ?_
  refine le_trans (mul_le_mul hH hM (norm_nonneg _) (by positivity)) (le_of_eq ?_)
  have hexp : x ^ (-(1 / 2 + σ)) * x ^ (1 - (3 - (1 / 2 + σ))) = x ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hden : (3 - (1 / 2 + σ)) - 1 = 2 - (1 / 2 + σ) := by ring
  rw [hden]
  calc K₁ * x ^ (-(1 / 2 + σ))
        * ((K₂ * wallAmplitude3Const μ₀) * (x ^ (1 - (3 - (1 / 2 + σ))) / (2 - (1 / 2 + σ))))
      = (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
        * (x ^ (-(1 / 2 + σ)) * x ^ (1 - (3 - (1 / 2 + σ)))) := by ring
    _ = (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * x ^ (-(2 : ℝ)) := by rw [hexp]

end GaloisForLFunctions.RHTower
