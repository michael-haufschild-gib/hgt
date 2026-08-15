import GaloisForLFunctions.RHTower.WallMovingTailBound
import GaloisForLFunctions.HTGeometry.ClockIteratedIntegralBound

/-!
# The datum accumulated below the frequency threshold

Everything the forced solution has accumulated below the threshold is a *fixed* vector, propagated
from there on by the Gamma transport.  Its size is one power of the threshold beyond the source's
`L¹` mass on the window: inside the window the inverse propagator grows like `(1+Y)^p`, and that is
the only growth — no ratio, no decay, since the transport has not yet been applied.

Paired with the ray decay of the propagator (`StripPropagatorRayMass`), whose `L²` mass on
`|x| > Y` is `O(Y^{1/2-p})`, the product is a single power of the threshold.  That cancellation is
what gives the one-block estimate the weight `e^{max(0,-m)}` rather than `e^{(1+σ)max(0,-m)}`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The datum accumulated below the frequency threshold. -/
def thresholdDatum (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℝ → X) (c : X) (σ Y : ℝ) : X :=
  c + ∫ t in (0 : ℝ)..Y, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)

/-- **The accumulated datum grows by at most one power of the threshold.**  Inside the window the
inverse propagator grows like `(1+Y)^p`, and Cauchy–Schwarz on `[0,Y]` costs `Y^{1/2}` more. -/
theorem norm_thresholdDatum_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 0 < Y → ∀ (b : ℝ → X) (c : X),
      IntegrableOn b (uIoc (0 : ℝ) Y) →
      ‖thresholdDatum E T b c σ Y‖
        ≤ ‖c‖ + C * (1 + Y) ^ (1 / 2 + σ) * ∫ t in uIoc (0 : ℝ) Y, ‖b t‖ := by
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  refine ⟨K₂, hK₂.le, fun Y hY b c hbint => ?_⟩
  have hp : (0 : ℝ) ≤ 1 / 2 + σ := by linarith
  have hbound : ∀ t ∈ uIoc (0 : ℝ) Y,
      ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖
        ≤ (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ‖b t‖ := by
    intro t ht
    have habs : |t| ≤ Y := by
      have h := abs_le_abs_of_mem_uIoc_zero ht
      rwa [abs_of_pos hY] at h
    have hmono : (1 + |t|) ^ (1 / 2 + σ) ≤ (1 + Y) ^ (1 / 2 + σ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) hp
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (hb₂ t).trans (mul_le_mul_of_nonneg_left hmono hK₂.le)
  have hint : IntegrableOn (fun t => (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ‖b t‖) (uIoc (0 : ℝ) Y) :=
    hbint.norm.const_mul _
  have hle := MeasureTheory.norm_integral_le_of_norm_le hint
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hbound t ht)
  have hconst : (∫ t in uIoc (0 : ℝ) Y, (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ‖b t‖)
      = (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ∫ t in uIoc (0 : ℝ) Y, ‖b t‖ := integral_const_mul _ _
  rw [hconst] at hle
  calc ‖thresholdDatum E T b c σ Y‖
      ≤ ‖c‖ + ‖∫ t in (0 : ℝ)..Y, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ :=
        norm_add_le _ _
    _ ≤ ‖c‖ + (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ∫ t in uIoc (0 : ℝ) Y, ‖b t‖ := by
        refine add_le_add le_rfl ?_
        rw [intervalIntegral.integral_of_le hY.le, ← uIoc_of_le hY.le]
        exact hle
    _ = ‖c‖ + K₂ * (1 + Y) ^ (1 / 2 + σ) * ∫ t in uIoc (0 : ℝ) Y, ‖b t‖ := by ring

/-- **The accumulated datum, in the extended norm.**  Stated this way the bound needs no
integrability at all: the extended norm of an interval integral is at most the extended mass of the
integrand, unconditionally. -/
theorem enorm_thresholdDatum_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 0 < Y → ∀ (b : ℝ → X) (c : X),
      ‖thresholdDatum E T b c σ Y‖ₑ
        ≤ ‖c‖ₑ + ENNReal.ofReal (C * (1 + Y) ^ (1 / 2 + σ))
            * ∫⁻ t in uIoc (0 : ℝ) Y, ‖b t‖ₑ := by
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  refine ⟨K₂, hK₂.le, fun Y hY b c => ?_⟩
  have hp : (0 : ℝ) ≤ 1 / 2 + σ := by linarith
  have hstep : ∀ t ∈ uIoc (0 : ℝ) Y,
      ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ
        ≤ ENNReal.ofReal (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ‖b t‖ₑ := by
    intro t ht
    have habs : |t| ≤ Y := by
      have h := GaloisForLFunctions.HTGeometry.abs_le_abs_of_mem_uIoc_zero ht
      rwa [abs_of_pos hY] at h
    have hmono : (1 + |t|) ^ (1 / 2 + σ) ≤ (1 + Y) ^ (1 / 2 + σ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) hp
    have hop : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖
        ≤ (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ‖b t‖ := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (hb₂ t).trans (mul_le_mul_of_nonneg_left hmono hK₂.le)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hop
  calc ‖thresholdDatum E T b c σ Y‖ₑ
      ≤ ‖c‖ₑ + ‖∫ t in (0 : ℝ)..Y,
          stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ := enorm_add_le _ _
    _ ≤ ‖c‖ₑ + ∫⁻ t in uIoc (0 : ℝ) Y,
          ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ :=
        add_le_add le_rfl (GaloisForLFunctions.HTGeometry.enorm_intervalIntegral_le _ 0 Y)
    _ ≤ ‖c‖ₑ + ∫⁻ t in uIoc (0 : ℝ) Y,
          ENNReal.ofReal (K₂ * (1 + Y) ^ (1 / 2 + σ)) * ‖b t‖ₑ :=
        add_le_add le_rfl (setLIntegral_mono' measurableSet_Ioc hstep)
    _ = ‖c‖ₑ + ENNReal.ofReal (K₂ * (1 + Y) ^ (1 / 2 + σ))
          * ∫⁻ t in uIoc (0 : ℝ) Y, ‖b t‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end GaloisForLFunctions.RHTower
