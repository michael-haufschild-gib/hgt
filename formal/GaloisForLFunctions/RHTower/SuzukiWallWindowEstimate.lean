import GaloisForLFunctions.RHTower.StripPropagatorLineDecay
import GaloisForLFunctions.HTGeometry.FrequencyLineSplit

/-!
# `(16)`: the finite frequency window of the variation-of-constants solution

Inside a bounded frequency window neither factor of the transport ratio is allowed to decay: the
propagator is bounded by its value at the origin and the inverse propagator by its value at the
window edge, so the whole moving-endpoint integral is dominated by a single fixed density — the
window mass of the forcing.  The window estimate then charges exactly one power of the window
length, and nothing else.

This is why the card's finite-interval bound costs `X_m` and no more: the frequency decay of the
Gamma propagator plays no role inside the window, and the only quantities that enter are the uniform
transport bound and the length.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The forced part of the variation-of-constants solution on the shifted line. -/
def forcedWindowPart (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℝ → X) (σ x : ℝ) : X :=
  stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
    (∫ t in (0 : ℝ)..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t))

/-- **`(16)`: the window estimate for the forced part.**  The squared window mass of the forced part
is at most a constant times the squared window length times the window energy of the forcing. -/
theorem lintegral_sq_forcedWindowPart_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {W : ℝ} (hW : 0 ≤ W) (b : ℝ → X)
    (hbmeas : AEMeasurable (fun t => ‖b t‖ₑ) (volume.restrict (Ioo (-W) W))) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ x in Ioo (-W) W, ‖forcedWindowPart E T b σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2 * (W - -W) ^ 2) * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ ^ 2 := by
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  set M : ℝ := K₁ * (K₂ * (1 + W) ^ (1 / 2 + σ)) with hM
  have hMnn : 0 ≤ M := by
    have : (0 : ℝ) ≤ (1 + W) ^ (1 / 2 + σ) := Real.rpow_nonneg (by linarith) _
    rw [hM]
    positivity
  refine ⟨M, hMnn, ?_⟩
  refine lintegral_sq_windowAverage_le (by linarith) hMnn hbmeas fun x hx => ?_
  -- the propagator factor
  have hxW : |x| ≤ W := by
    obtain ⟨h1, h2⟩ := hx
    rw [abs_le]
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  have hprop : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖ ≤ K₁ := by
    refine (hb₁ x).trans ?_
    have hle : (1 + |x|) ^ (-(1 / 2 + σ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
      have := abs_nonneg x
      linarith
    nlinarith [hle, hK₁]
  -- the inverse propagator factor on the window
  have hinv : ∀ t : ℝ, |t| ≤ W →
      ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖
        ≤ (K₂ * (1 + W) ^ (1 / 2 + σ)) * ‖b t‖ := by
    intro t ht
    have hbase : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)‖
        ≤ K₂ * (1 + W) ^ (1 / 2 + σ) := by
      refine (hb₂ t).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK₂.le
      refine Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖
        ≤ ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖b t‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K₂ * (1 + W) ^ (1 / 2 + σ)) * ‖b t‖ :=
          mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
  -- assemble
  have hint : ‖∫ t in (0 : ℝ)..x,
      stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ
      ≤ ENNReal.ofReal (K₂ * (1 + W) ^ (1 / 2 + σ)) * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ := by
    refine (enorm_intervalIntegral_le_window _ hxW).trans ?_
    rw [← lintegral_Ioo_eq_Icc]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    have htW : |t| ≤ W := by
      obtain ⟨h1, h2⟩ := ht
      rw [abs_le]
      exact ⟨le_of_lt h1, le_of_lt h2⟩
    have hK : (0 : ℝ) ≤ K₂ * (1 + W) ^ (1 / 2 + σ) := by
      have : (0 : ℝ) ≤ (1 + W) ^ (1 / 2 + σ) := Real.rpow_nonneg (by linarith) _
      positivity
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hinv t htW)
  calc ‖forcedWindowPart E T b σ x‖ₑ
      ≤ ENNReal.ofReal K₁ * ‖∫ t in (0 : ℝ)..x,
          stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ := by
        rw [forcedWindowPart, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK₁.le]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) _‖
            ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖_‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ K₁ * ‖_‖ := mul_le_mul_of_nonneg_right hprop (norm_nonneg _)
    _ ≤ ENNReal.ofReal K₁ * (ENNReal.ofReal (K₂ * (1 + W) ^ (1 / 2 + σ))
          * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ) := mul_le_mul' le_rfl hint
    _ = ENNReal.ofReal M * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ := by
        rw [hM, ENNReal.ofReal_mul hK₁.le, mul_assoc]

end GaloisForLFunctions.RHTower
