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

/-- On a moving-endpoint interval starting at the origin the inner frequency never exceeds the
outer one. -/
theorem abs_le_abs_of_mem_uIoc_zero {t x : ℝ} (ht : t ∈ uIoc (0 : ℝ) x) : |t| ≤ |x| := by
  rw [uIoc] at ht
  rcases le_total 0 x with hx0 | hx0
  · rw [min_eq_left hx0, max_eq_right hx0] at ht
    rw [abs_of_pos ht.1, abs_of_nonneg hx0]
    exact ht.2
  · rw [min_eq_right hx0, max_eq_left hx0] at ht
    rw [abs_of_nonpos ht.2, abs_of_nonpos hx0]
    linarith [ht.1]

theorem uIoc_zero_subset_Icc {W x : ℝ} (hx : |x| ≤ W) : uIoc (0 : ℝ) x ⊆ Icc (-W) W := by
  intro t ht
  have hxW : -W ≤ x ∧ x ≤ W := abs_le.mp hx
  have hW : (0 : ℝ) ≤ W := le_trans (abs_nonneg x) hx
  rw [uIoc] at ht
  obtain ⟨h1, h2⟩ := ht
  constructor
  · have hmin : min (0 : ℝ) x ≥ -W := le_min (by linarith) hxW.1
    linarith
  · have hmax : max (0 : ℝ) x ≤ W := max_le hW hxW.2
    linarith

/-- **`(16)`: the window estimate for the forced part, with a window-free constant.**  Inside the
moving-endpoint integral the inner frequency lies between the origin and the outer one, so the
transport ratio is bounded by a constant with *no* window factor; the window then contributes exactly
one power of its length, once from Cauchy--Schwarz inside and once from the outer average. -/
theorem exists_bound_lintegral_sq_forcedWindowPart (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ W : ℝ, 0 ≤ W → ∀ b : ℝ → X,
      AEMeasurable (fun t => ‖b t‖ₑ) (volume.restrict (Ioo (-W) W)) →
      (∫⁻ x in Ioo (-W) W, ‖forcedWindowPart E T b σ x‖ₑ ^ 2)
        ≤ ENNReal.ofReal ((M ^ 2) * (W - -W) ^ 2) * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ ^ 2 := by
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_stripPropagatorInv_line hT hE hσ0 hσ1
  refine ⟨K₁ * K₂, by positivity, fun W hW b hbmeas => ?_⟩
  refine lintegral_sq_windowAverage_le (by linarith) (by positivity) hbmeas fun x hx => ?_
  have hxW : |x| ≤ W := by
    obtain ⟨h1, h2⟩ := hx
    rw [abs_le]
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  have hx0 : (0 : ℝ) < 1 + |x| := by positivity
  set p : ℝ := 1 / 2 + σ with hpdef
  have hpnn : (0 : ℝ) ≤ p := by rw [hpdef]; linarith
  -- the transported integrand never grows past the outer frequency
  have hinner : ‖∫ t in (0 : ℝ)..x,
      stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ
      ≤ ENNReal.ofReal (K₂ * (1 + |x|) ^ p) * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ := by
    refine le_trans (enorm_intervalIntegral_le _ 0 x) ?_
    have hstep : (∫⁻ t in uIoc (0 : ℝ) x,
          ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ)
        ≤ ∫⁻ t in uIoc (0 : ℝ) x, ENNReal.ofReal (K₂ * (1 + |x|) ^ p) * ‖b t‖ₑ := by
      refine setLIntegral_mono' (measurableSet_Ioc : MeasurableSet (uIoc (0 : ℝ) x))
        fun t ht => ?_
      have habs := abs_le_abs_of_mem_uIoc_zero ht
      have hmono : (1 + |t|) ^ p ≤ (1 + |x|) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hpnn
      have hop : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖
          ≤ (K₂ * (1 + |x|) ^ p) * ‖b t‖ := by
        refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (hb₂ t).trans (mul_le_mul_of_nonneg_left hmono hK₂.le)
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hop
    refine hstep.trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioo_eq_Icc]
    exact mul_le_mul' le_rfl (lintegral_mono_set (uIoc_zero_subset_Icc hxW))
  have hprop : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |x|) ^ (-p) := hb₁ x
  have hcancel : ENNReal.ofReal (K₁ * (1 + |x|) ^ (-p)) * ENNReal.ofReal (K₂ * (1 + |x|) ^ p)
      = ENNReal.ofReal (K₁ * K₂) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hrp : (1 + |x|) ^ (-p) * (1 + |x|) ^ p = 1 := by
      rw [← Real.rpow_add hx0]
      simp
    calc K₁ * (1 + |x|) ^ (-p) * (K₂ * (1 + |x|) ^ p)
        = K₁ * K₂ * ((1 + |x|) ^ (-p) * (1 + |x|) ^ p) := by ring
      _ = K₁ * K₂ := by rw [hrp, mul_one]
  calc ‖forcedWindowPart E T b σ x‖ₑ
      ≤ ENNReal.ofReal (K₁ * (1 + |x|) ^ (-p)) * ‖∫ t in (0 : ℝ)..x,
          stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)‖ₑ := by
        rw [forcedWindowPart, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right hprop (norm_nonneg _))
    _ ≤ ENNReal.ofReal (K₁ * (1 + |x|) ^ (-p))
          * (ENNReal.ofReal (K₂ * (1 + |x|) ^ p) * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ) :=
        mul_le_mul' le_rfl hinner
    _ = ENNReal.ofReal (K₁ * K₂) * ∫⁻ t in Ioo (-W) W, ‖b t‖ₑ := by
        rw [← mul_assoc, hcancel]

end GaloisForLFunctions.RHTower
