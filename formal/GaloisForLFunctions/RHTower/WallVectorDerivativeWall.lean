import GaloisForLFunctions.RHTower.WallTailOperatorRegularity

/-!
# The vector derivative wall

The scalar wall `(42)` says that multiplying the shifted Gamma carrier by the frequency destroys
integrability.  What the scattering criterion needs is the vector form: for a *nonzero* datum the
propagated profile, weighted by the frequency, has infinite squared mass on either terminal ray.

The proof needs no sharp asymptotics.  The inverse propagator grows at most like
`(1+|x|)^{1/2+\sigma}`, so the propagator moves no vector further than that factor towards zero;
after multiplication by `x` the resulting density dominates `x^{1-2\sigma}`, whose exponent is `>-1`
for every `\sigma<1`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **A power tail whose exponent is at least `-1` has infinite mass on a terminal ray.** -/
theorem lintegral_ofReal_rpow_Ioi_eq_top {a Y : ℝ} (hY : 0 < Y) (ha : -1 ≤ a) :
    (∫⁻ x in Ioi Y, ENNReal.ofReal (x ^ a)) = ⊤ := by
  by_contra hcon
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ a) (volume.restrict (Ioi Y)) :=
    (Measurable.pow_const measurable_id a).aestronglyMeasurable
  have hcongr : (∫⁻ x in Ioi Y, ‖x ^ a‖ₑ) = ∫⁻ x in Ioi Y, ENNReal.ofReal (x ^ a) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.enorm_eq_ofReal (Real.rpow_nonneg (le_of_lt (lt_trans hY hx)) a)
  have hfin : HasFiniteIntegral (fun x : ℝ => x ^ a) (volume.restrict (Ioi Y)) := by
    rw [hasFiniteIntegral_iff_enorm, hcongr]
    exact lt_top_iff_ne_top.mpr hcon
  have hint : IntegrableOn (fun x : ℝ => x ^ a) (Ioi Y) := ⟨hmeas, hfin⟩
  have := (integrableOn_Ioi_rpow_iff hY).mp hint
  linarith

/-- The comparison constant between `(1+x)^a` and `x^a` on `[1,∞)`. -/
def rayShiftConst (a : ℝ) : ℝ := min 1 ((2 : ℝ) ^ a)

theorem rayShiftConst_pos (a : ℝ) : 0 < rayShiftConst a := by
  rw [rayShiftConst]
  exact lt_min one_pos (Real.rpow_pos_of_pos two_pos a)

theorem rayShiftConst_mul_rpow_le {a x : ℝ} (hx : 1 ≤ x) :
    rayShiftConst a * x ^ a ≤ (1 + x) ^ a := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxa : (0 : ℝ) ≤ x ^ a := Real.rpow_nonneg hx0.le a
  rcases le_or_gt 0 a with ha | ha
  · calc rayShiftConst a * x ^ a ≤ 1 * x ^ a :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hxa
      _ = x ^ a := one_mul _
      _ ≤ (1 + x) ^ a := Real.rpow_le_rpow hx0.le (by linarith) ha
  · calc rayShiftConst a * x ^ a ≤ (2 : ℝ) ^ a * x ^ a :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hxa
      _ = (2 * x) ^ a := by rw [Real.mul_rpow (by norm_num) hx0.le]
      _ ≤ (1 + x) ^ a := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) ha.le

/-- **The vector derivative wall.**  On a terminal ray the frequency-weighted propagated datum has
infinite squared mass unless the datum vanishes. -/
theorem lintegral_sq_freq_stripPropagator_eq_top {σ K₂ Y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 < K₂)
    (hY : 1 ≤ Y) {v : X} (hv : v ≠ 0) :
    (∫⁻ x in Ioi Y, ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2) = ⊤ := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  set a : ℝ := 1 - 2 * σ with ha
  set c₀ : ℝ := rayShiftConst a with hc₀
  have hc₀pos : 0 < c₀ := rayShiftConst_pos a
  set C : ℝ := ‖v‖ ^ 2 * c₀ / (4 * K₂ ^ 2) with hC
  have hCpos : 0 < C := by
    rw [hC]
    positivity
  -- the pointwise lower bound
  have hpt : ∀ x ∈ Ioi Y, ENNReal.ofReal (C * x ^ a)
      ≤ ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2 := by
    intro x hx
    have hxY : Y < x := hx
    have hx1 : (1 : ℝ) ≤ x := le_trans hY hxY.le
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hw : (0 : ℝ) < 1 + x := by linarith
    have hz : ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shift_ne_zero hσ0 x
    have hEz : E ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := branch_ne_zero hE hσ0 hσ1 x
    have hcancel := stripPropagatorInv_stripPropagator (E := E) (T := T) hz hEz v
    have hR : (0 : ℝ) ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := norm_nonneg _
    have hxabs : |x| = x := abs_of_pos hx0
    have hbound : ‖v‖
        ≤ (K₂ * (1 + x) ^ (1 / 2 + σ))
          * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := by
      calc ‖v‖ = ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v)‖ := by rw [hcancel]
        _ ≤ ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K₂ * (1 + x) ^ (1 / 2 + σ))
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := by
              refine mul_le_mul_of_nonneg_right ?_ hR
              have := hb₂ x
              rwa [hxabs] at this
    have hPsq : ((1 + x) ^ (1 / 2 + σ : ℝ)) * ((1 + x) ^ (1 / 2 + σ : ℝ))
        = (1 + x) ^ (1 + 2 * σ : ℝ) := by
      rw [← Real.rpow_add hw]
      congr 1
      ring
    have hPpos : (0 : ℝ) < (1 + x) ^ (1 + 2 * σ : ℝ) := Real.rpow_pos_of_pos hw _
    have hsq : ‖v‖ ^ 2
        ≤ (K₂ ^ 2 * (1 + x) ^ (1 + 2 * σ : ℝ))
          * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by
      have hnn : (0 : ℝ) ≤ (K₂ * (1 + x) ^ (1 / 2 + σ))
          * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := by positivity
      have := mul_le_mul hbound hbound (norm_nonneg _) hnn
      calc ‖v‖ ^ 2 = ‖v‖ * ‖v‖ := sq _
        _ ≤ ((K₂ * (1 + x) ^ (1 / 2 + σ))
              * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖)
            * ((K₂ * (1 + x) ^ (1 / 2 + σ))
              * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖) := this
        _ = (K₂ ^ 2 * ((1 + x) ^ (1 / 2 + σ : ℝ) * (1 + x) ^ (1 / 2 + σ : ℝ)))
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by ring
        _ = (K₂ ^ 2 * (1 + x) ^ (1 + 2 * σ : ℝ))
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by rw [hPsq]
    have hprod : c₀ * x ^ a * (1 + x) ^ (1 + 2 * σ : ℝ) ≤ 4 * x ^ 2 := by
      have h1 : c₀ * x ^ a ≤ (1 + x) ^ a := rayShiftConst_mul_rpow_le hx1
      have h2 : (1 + x) ^ a * (1 + x) ^ (1 + 2 * σ : ℝ) = (1 + x) ^ (2 : ℝ) := by
        rw [← Real.rpow_add hw, ha]
        congr 1
        ring
      have h3 : (1 + x) ^ (2 : ℝ) = (1 + x) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc c₀ * x ^ a * (1 + x) ^ (1 + 2 * σ : ℝ)
          ≤ (1 + x) ^ a * (1 + x) ^ (1 + 2 * σ : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hPpos.le
        _ = (1 + x) ^ 2 := by rw [h2, h3]
        _ ≤ 4 * x ^ 2 := by nlinarith
    have hkey : C * x ^ a
        ≤ x ^ 2 * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by
      rw [hC]
      have hK2 : (0 : ℝ) < 4 * K₂ ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hK2]
      nlinarith [hsq, hprod, sq_nonneg (‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖),
        Real.rpow_nonneg hx0.le a, hPpos, sq_nonneg x, hc₀pos]
    have hnormsq : ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2
        = x ^ 2 * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc ENNReal.ofReal (C * x ^ a)
        ≤ ENNReal.ofReal (‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2) := by
          rw [hnormsq]
          exact ENNReal.ofReal_le_ofReal hkey
      _ = ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2 := by
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  -- integrate the lower bound
  have hle : (∫⁻ x in Ioi Y, ENNReal.ofReal (C * x ^ a))
      ≤ ∫⁻ x in Ioi Y, ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2 := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt x hx
  have hsplit : (∫⁻ x in Ioi Y, ENNReal.ofReal (C * x ^ a))
      = ENNReal.ofReal C * ∫⁻ x in Ioi Y, ENNReal.ofReal (x ^ a) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul hCpos.le]
  have htop : (∫⁻ x in Ioi Y, ENNReal.ofReal (C * x ^ a)) = ⊤ := by
    rw [hsplit, lintegral_ofReal_rpow_Ioi_eq_top hY0 (by rw [ha]; linarith)]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCpos).ne'
  exact top_le_iff.mp (htop ▸ hle)

end GaloisForLFunctions.RHTower
