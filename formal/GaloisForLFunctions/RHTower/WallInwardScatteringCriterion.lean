import GaloisForLFunctions.RHTower.WallInwardScatteringCharge
import GaloisForLFunctions.RHTower.WallInwardTailRemainder
import GaloisForLFunctions.RHTower.WallScatteringCriterion

/-!
# `(47)` on the inward ray

The mirror of `WallScatteringCriterion`.  Every estimate the outward ray used is even in the
frequency, so the only genuinely new ingredient is the divergence of the homogeneous carrier on the
left ray, and that is again `x^{1-2σ}` with `1-2σ > -1`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
/-- Past the unit radius the reciprocal loses at most a factor two to the shift. -/
theorem rpow_neg_one_le_two_mul {u : ℝ} (hu : 1 ≤ u) :
    u ^ (-(1 : ℝ)) ≤ 2 * (1 + u) ^ (-(1 : ℝ)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have h1u : (0 : ℝ) < 1 + u := by linarith
  rw [Real.rpow_neg_one, Real.rpow_neg_one, ← sub_nonneg]
  have heq : 2 * (1 + u)⁻¹ - u⁻¹ = (2 * u - (1 + u)) / (u * (1 + u)) := by
    field_simp
  rw [heq]
  exact div_nonneg (by linarith) (by positivity)

/-- **The transported inward ray remainder survives multiplication by the frequency.** -/
theorem norm_freq_smul_transported_wallTailVectorNeg_le {σ x μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) {A : ℝ}
    (hA : (∫ L in Icc m (m + 1), ‖g L‖) ≤ A) (hx : x ≤ -1)
    (hgap : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic x, μ₀ ≤ wallFloor T σ t + L) :
    ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (wallTailVectorNeg E T g m σ x)‖
      ≤ (2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * A)
        * (1 + |x|) ^ (-(1 : ℝ)) := by
  have hx0 : (0 : ℝ) < -x := by linarith
  have hxabs : |x| = -x := abs_of_neg (by linarith)
  have hC3 : (0 : ℝ) ≤ wallAmplitude3Const μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitude3Const]
    positivity
  have hden : (0 : ℝ) < 2 - (1 / 2 + σ) := by linarith
  have hCt : (0 : ℝ) ≤ K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)) := by positivity
  have hAnn : (0 : ℝ) ≤ ∫ L in Icc m (m + 1), ‖g L‖ :=
    setIntegral_nonneg measurableSet_Icc fun L _ => norm_nonneg _
  have hIx := integrableOn_wallTailOperatorNeg_apply hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hx hgap
  have hcomm : stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (wallTailVectorNeg E T g m σ x)
      = ∫ L in Icc m (m + 1), stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallTailOperatorNeg E T σ L x (g L)) :=
    (ContinuousLinearMap.integral_comp_comm _ hIx).symm
  have hbd : ∀ L ∈ Icc m (m + 1),
      ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallTailOperatorNeg E T σ L x (g L))‖
        ≤ ((K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * (-x) ^ (-(2 : ℝ)))
          * ‖g L‖ := by
    intro L hL
    rw [← mul_apply_eq_comp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact norm_wallThirdTailNeg_transported_le hσ0 hσ1 hμ hb₁ hK₁ hb₂ hK₂ hx
      (fun t ht => hgap L hL t ht)
  have hle := MeasureTheory.norm_integral_le_of_norm_le (hg.norm.const_mul _)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL using hbd L hL)
  rw [integral_const_mul] at hle
  rw [← hcomm] at hle
  have hstep : ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (wallTailVectorNeg E T g m σ x)‖
      ≤ (-x) * (((K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * (-x) ^ (-(2 : ℝ)))
        * ∫ L in Icc m (m + 1), ‖g L‖) := by
    rw [norm_smul, Real.norm_eq_abs, hxabs]
    exact mul_le_mul_of_nonneg_left hle hx0.le
  have hpow : (-x) * (-x) ^ (-(2 : ℝ)) = (-x) ^ (-(1 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one (-x)]
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hinv : (-x) ^ (-(1 : ℝ)) ≤ 2 * (1 + (-x)) ^ (-(1 : ℝ)) :=
    rpow_neg_one_le_two_mul (by linarith)
  calc ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallTailVectorNeg E T g m σ x)‖
      ≤ (-x) * (((K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * (-x) ^ (-(2 : ℝ)))
        * ∫ L in Icc m (m + 1), ‖g L‖) := hstep
    _ = (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
        * ((-x) ^ (-(1 : ℝ)) * ∫ L in Icc m (m + 1), ‖g L‖) := by
          rw [← hpow]; ring
    _ ≤ (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
        * ((2 * (1 + (-x)) ^ (-(1 : ℝ))) * A) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hinv hA hAnn (by positivity)) hCt
    _ = (2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * A)
        * (1 + |x|) ^ (-(1 : ℝ)) := by rw [hxabs]; ring

/-- The part of the inward point-dependent remainder estimated by a bare power tail. -/
def wallRestPartNeg (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  secondBoundary T g m σ x - (Complex.I : ℂ) • thirdBoundary T g m σ x
    + (Complex.I : ℂ) • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallTailVectorNeg E T g m σ x)

theorem wallScatteringRemainderNeg_eq (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) :
    wallScatteringRemainderNeg E T g m σ x
      = (-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • firstBoundaryBlock T g m σ x
          + wallRestPartNeg E T g m σ x) := by
  rw [wallScatteringRemainderNeg, wallRestPartNeg]
  module

set_option maxHeartbeats 1000000 in
/-- **The three remaining inward point-dependent terms decay like `|x|^{-1}` after multiplication by
the frequency.** -/
theorem norm_freq_smul_wallRestPartNeg_le {σ x μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (hx : x ≤ -1)
    (hfloor : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapR : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic x, μ₀ ≤ wallFloor T σ t + L) :
    ‖x • wallRestPartNeg E T g m σ x‖
      ≤ ((3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g L‖)
            + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g' L‖))
          + (μ₀⁻¹ * wallAmplitudeConst μ₀) * (∫ L in Icc m (m + 1), ‖g L‖)
          + 2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
              * (∫ L in Icc m (m + 1), ‖g L‖))
        * (1 + |x|) ^ (-(1 : ℝ)) := by
  have hxabs : (1 : ℝ) ≤ |x| := by
    rw [abs_of_neg (by linarith : x < 0)]
    linarith
  have h2 := norm_freq_smul_secondBoundary_le (T := T) hσ0 hσ1 hμ hgd hsupp hg hg'
    (le_refl (∫ L in Icc m (m + 1), ‖g L‖)) (le_refl (∫ L in Icc m (m + 1), ‖g' L‖)) hxabs hfloor
  have h3 := norm_freq_smul_thirdBoundary_le (T := T) hσ0 hσ1 hμ hg
    (le_refl (∫ L in Icc m (m + 1), ‖g L‖)) hxabs hfloor
  have h4 := norm_freq_smul_transported_wallTailVectorNeg_le hEdiff hE hEne hσ0 hσ1 hμ hb₁ hK₁
    hb₂ hK₂ hg (le_refl (∫ L in Icc m (m + 1), ‖g L‖)) hx hgapR
  have hsmul : ∀ u : X, ‖x • ((Complex.I : ℂ) • u)‖ = ‖x • u‖ := by
    intro u
    rw [smul_comm, norm_smul, Complex.norm_I, one_mul]
  have hsplit : x • wallRestPartNeg E T g m σ x
      = x • secondBoundary T g m σ x - x • ((Complex.I : ℂ) • thirdBoundary T g m σ x)
        + x • ((Complex.I : ℂ) • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (wallTailVectorNeg E T g m σ x)) := by
    rw [wallRestPartNeg, smul_add, smul_sub]
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (norm_sub_le _ _) (le_of_eq (hsmul _))) ?_
  rw [hsmul]
  have hw : (0 : ℝ) < (1 + |x|) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  nlinarith [h2, h3, h4, hw]

/-! ## The inward vector derivative wall -/

theorem lintegral_ofReal_rpow_Iio_eq_top {a W : ℝ} (hW : W < 0) (ha : -1 ≤ a) :
    (∫⁻ x in Iio W, ENNReal.ofReal ((-x) ^ a)) = ⊤ := by
  by_contra hcon
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (-x) ^ a) (volume.restrict (Iio W)) :=
    ((Measurable.pow_const measurable_neg a)).aestronglyMeasurable
  have hcongr : (∫⁻ x in Iio W, ‖(-x) ^ a‖ₑ) = ∫⁻ x in Iio W, ENNReal.ofReal ((-x) ^ a) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hxlt : x < W := hx
    exact Real.enorm_eq_ofReal (Real.rpow_nonneg (by linarith) a)
  have hfin : HasFiniteIntegral (fun x : ℝ => (-x) ^ a) (volume.restrict (Iio W)) := by
    rw [hasFiniteIntegral_iff_enorm, hcongr]
    exact lt_top_iff_ne_top.mpr hcon
  have hint : IntegrableOn (fun x : ℝ => (-x) ^ a) (Iio W) := ⟨hmeas, hfin⟩
  have hrefl := hint.comp_neg
  rw [neg_Iio] at hrefl
  have hfin2 : IntegrableOn (fun x : ℝ => x ^ a) (Ioi (-W)) := by
    refine hrefl.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [neg_neg]
  have := (integrableOn_Ioi_rpow_iff (by linarith : (0 : ℝ) < -W)).mp hfin2
  linarith

set_option maxHeartbeats 1000000 in
/-- **The vector derivative wall on the inward ray.** -/
theorem lintegral_sq_freq_stripPropagator_negRay_eq_top {σ K₂ W : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 < K₂)
    (hW : W ≤ -1) {v : X} (hv : v ≠ 0) :
    (∫⁻ x in Iio W, ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2) = ⊤ := by
  have hW0 : W < 0 := by linarith
  have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have hc₀pos : 0 < rayShiftConst (1 - 2 * σ) := rayShiftConst_pos _
  have hCpos : 0 < ‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2) := by positivity
  have hpt : ∀ x ∈ Iio W,
      ENNReal.ofReal ((‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2))
          * (-x) ^ (1 - 2 * σ))
        ≤ ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2 := by
    intro x hx
    have hxW : x < W := hx
    have hx1 : (1 : ℝ) ≤ -x := by linarith
    have hx0 : (0 : ℝ) < -x := lt_of_lt_of_le zero_lt_one hx1
    have hw : (0 : ℝ) < 1 + (-x) := by linarith
    have hz : ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := shift_ne_zero hσ0 x
    have hEz : E ((x : ℂ) + (σ : ℂ) * Complex.I) ≠ 0 := branch_ne_zero hE hσ0 hσ1 x
    have hcancel := stripPropagatorInv_stripPropagator (E := E) (T := T) hz hEz v
    have hR : (0 : ℝ) ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := norm_nonneg _
    have hxabs : |x| = -x := abs_of_neg (by linarith)
    have hbound : ‖v‖
        ≤ (K₂ * (1 + (-x)) ^ (1 / 2 + σ))
          * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := by
      calc ‖v‖ = ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v)‖ := by rw [hcancel]
        _ ≤ ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K₂ * (1 + (-x)) ^ (1 / 2 + σ))
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := by
              refine mul_le_mul_of_nonneg_right ?_ hR
              have := hb₂ x
              rwa [hxabs] at this
    have hPsq : ((1 + (-x)) ^ (1 / 2 + σ : ℝ)) * ((1 + (-x)) ^ (1 / 2 + σ : ℝ))
        = (1 + (-x)) ^ (1 + 2 * σ : ℝ) := by
      rw [← Real.rpow_add hw]
      congr 1
      ring
    have hPpos : (0 : ℝ) < (1 + (-x)) ^ (1 + 2 * σ : ℝ) := Real.rpow_pos_of_pos hw _
    have hsq : ‖v‖ ^ 2
        ≤ (K₂ ^ 2 * (1 + (-x)) ^ (1 + 2 * σ : ℝ))
          * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by
      have hnn : (0 : ℝ) ≤ (K₂ * (1 + (-x)) ^ (1 / 2 + σ))
          * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ := by positivity
      have hmul := mul_le_mul hbound hbound (norm_nonneg _) hnn
      calc ‖v‖ ^ 2 = ‖v‖ * ‖v‖ := sq _
        _ ≤ ((K₂ * (1 + (-x)) ^ (1 / 2 + σ))
              * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖)
            * ((K₂ * (1 + (-x)) ^ (1 / 2 + σ))
              * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖) := hmul
        _ = (K₂ ^ 2 * ((1 + (-x)) ^ (1 / 2 + σ : ℝ) * (1 + (-x)) ^ (1 / 2 + σ : ℝ)))
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by ring
        _ = (K₂ ^ 2 * (1 + (-x)) ^ (1 + 2 * σ : ℝ))
            * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by rw [hPsq]
    have hprod : rayShiftConst (1 - 2 * σ) * (-x) ^ (1 - 2 * σ)
        * (1 + (-x)) ^ (1 + 2 * σ : ℝ) ≤ 4 * x ^ 2 := by
      have h1 : rayShiftConst (1 - 2 * σ) * (-x) ^ (1 - 2 * σ) ≤ (1 + (-x)) ^ (1 - 2 * σ) :=
        rayShiftConst_mul_rpow_le hx1
      have h2 : (1 + (-x)) ^ (1 - 2 * σ : ℝ) * (1 + (-x)) ^ (1 + 2 * σ : ℝ)
          = (1 + (-x)) ^ (2 : ℝ) := by
        rw [← Real.rpow_add hw]
        congr 1
        ring
      have h3 : (1 + (-x)) ^ (2 : ℝ) = (1 + (-x)) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc rayShiftConst (1 - 2 * σ) * (-x) ^ (1 - 2 * σ) * (1 + (-x)) ^ (1 + 2 * σ : ℝ)
          ≤ (1 + (-x)) ^ (1 - 2 * σ : ℝ) * (1 + (-x)) ^ (1 + 2 * σ : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hPpos.le
        _ = (1 + (-x)) ^ 2 := by rw [h2, h3]
        _ ≤ 4 * x ^ 2 := by nlinarith
    have hkey : (‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2)) * (-x) ^ (1 - 2 * σ)
        ≤ x ^ 2 * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by
      have hK2 : (0 : ℝ) < 4 * K₂ ^ 2 := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hK2]
      nlinarith [hsq, hprod, sq_nonneg (‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖),
        Real.rpow_nonneg hx0.le (1 - 2 * σ), hPpos, sq_nonneg x, hc₀pos]
    have hnormsq : ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2
        = x ^ 2 * ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc ENNReal.ofReal ((‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2))
          * (-x) ^ (1 - 2 * σ))
        ≤ ENNReal.ofReal (‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ ^ 2) := by
          rw [hnormsq]
          exact ENNReal.ofReal_le_ofReal hkey
      _ = ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2 := by
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hle : (∫⁻ x in Iio W, ENNReal.ofReal
        ((‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2)) * (-x) ^ (1 - 2 * σ)))
      ≤ ∫⁻ x in Iio W, ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) v‖ₑ ^ 2 := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact hpt x hx
  have hsplit : (∫⁻ x in Iio W, ENNReal.ofReal
        ((‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2)) * (-x) ^ (1 - 2 * σ)))
      = ENNReal.ofReal (‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2))
        * ∫⁻ x in Iio W, ENNReal.ofReal ((-x) ^ (1 - 2 * σ)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul hCpos.le]
  have htop : (∫⁻ x in Iio W, ENNReal.ofReal
      ((‖v‖ ^ 2 * rayShiftConst (1 - 2 * σ) / (4 * K₂ ^ 2)) * (-x) ^ (1 - 2 * σ))) = ⊤ := by
    rw [hsplit, lintegral_ofReal_rpow_Iio_eq_top hW0 (by linarith)]
    exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCpos).ne'
  exact top_le_iff.mp (htop ▸ hle)


/-! ## The inward criterion -/

variable [Nontrivial X]

omit [Nontrivial X] in
set_option maxHeartbeats 1000000 in
/-- **All inward point-dependent terms are square integrable after multiplication by the
frequency.** -/
theorem lintegral_sq_freq_wallScatteringRemainderNeg_ne_top {σ Y μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (hY : 1 ≤ Y) (hfloor : ∀ x ∈ Iio (-Y), μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x in Iio (-Y), ‖x • wallScatteringRemainderNeg E T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hx1 : ∀ x ∈ Iio (-Y), x ≤ -1 := by
    intro x hx
    have : x < -Y := hx
    linarith
  have hfloorL : ∀ x ∈ Iio (-Y), ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L := by
    intro x hx L hL
    have hm : m ≤ L := hL.1
    have := hfloor x hx
    linarith
  have hgapR : ∀ x ∈ Iio (-Y), ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic x, μ₀ ≤ wallFloor T σ t + L := by
    intro x hx L hL t ht
    have hxlt : x < -Y := hx
    have htx : t ≤ x := ht
    exact hfloorL t (mem_Iio.mpr (lt_of_le_of_lt htx hxlt)) L hL
  have h1 : (∫⁻ x in Iio (-Y), ‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
    have hbase := lintegral_sq_freqFirstBoundary_le (T := T) (A := Iio (-Y)) measurableSet_Iio
      hσ0 hσ1 hμ hgd hg2 hgm hg'2 hsupp hfloor
    rw [lintegral_sq_indicator_eq measurableSet_Iio] at hbase
    have hcongr : (∫⁻ x in Iio (-Y), ‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2)
        = ∫⁻ x in Iio (-Y), ‖x • firstBoundary T g σ x‖ₑ ^ 2 := by
      refine lintegral_congr fun x => ?_
      rw [firstBoundaryBlock_eq_firstBoundary hsupp]
    intro htop
    rw [← hcongr, htop, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hbase
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hbase)
  have hrest : (∫⁻ x in Iio (-Y), ‖x • wallRestPartNeg E T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_sq_negRay_powerTail_le
      (f := fun x : ℝ => x • wallRestPartNeg E T g m σ x) (p := 1) (Y := Y)
      (C := (3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g L‖)
            + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g' L‖))
          + (μ₀⁻¹ * wallAmplitudeConst μ₀) * (∫ L in Icc m (m + 1), ‖g L‖)
          + 2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
              * (∫ L in Icc m (m + 1), ‖g L‖))
      (by norm_num) hY0 (fun x hx => ?_))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · have := norm_freq_smul_wallRestPartNeg_le hEdiff hE hEne hσ0 hσ1 hμ hb₁ hK₁ hb₂ hK₂
        hgd hsupp hg hg' (hx1 x hx) (fun L hL => hfloorL x hx L hL)
        (fun L hL t ht => hgapR x hx L hL t ht)
      simpa using this
  have hpair : ∀ u v : ℝ≥0∞, (u + v) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2) := by
    intro u v
    have hle : u + v ≤ 2 * max u v :=
      (add_le_add (le_max_left u v) (le_max_right u v)).trans (by rw [two_mul])
    have hmax : max u v ^ 2 ≤ u ^ 2 + v ^ 2 := by
      rcases max_choice u v with h | h <;> rw [h]
      · exact le_self_add
      · exact le_add_self
    calc (u + v) ^ 2 ≤ (2 * max u v) ^ 2 := pow_le_pow_left' hle 2
      _ = 4 * max u v ^ 2 := by ring
      _ ≤ 4 * (u ^ 2 + v ^ 2) := mul_le_mul' le_rfl hmax
  have hcoef : ‖(-(Complex.I) / 2 : ℂ)‖ₑ ≤ 1 := by
    have hc : ‖(-(Complex.I) / 2 : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_neg, Complex.norm_I]
      norm_num
    calc ‖(-(Complex.I) / 2 : ℂ)‖ₑ = ENNReal.ofReal ‖(-(Complex.I) / 2 : ℂ)‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hc
      _ = 1 := by simp
  have hsq : ∀ x : ℝ, ‖x • wallScatteringRemainderNeg E T g m σ x‖ₑ ^ 2
      ≤ 4 * (‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2
        + ‖x • wallRestPartNeg E T g m σ x‖ₑ ^ 2) := by
    intro x
    have hstep : x • wallScatteringRemainderNeg E T g m σ x
        = (-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
            + x • wallRestPartNeg E T g m σ x) := by
      rw [wallScatteringRemainderNeg_eq]
      module
    have hnorm : ‖x • wallScatteringRemainderNeg E T g m σ x‖ₑ
        ≤ ‖x • firstBoundaryBlock T g m σ x‖ₑ + ‖x • wallRestPartNeg E T g m σ x‖ₑ := by
      rw [hstep, enorm_smul]
      calc ‖(-(Complex.I) / 2 : ℂ)‖ₑ * ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
              + x • wallRestPartNeg E T g m σ x‖ₑ
          ≤ 1 * ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
              + x • wallRestPartNeg E T g m σ x‖ₑ := mul_le_mul' hcoef le_rfl
        _ = ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
              + x • wallRestPartNeg E T g m σ x‖ₑ := one_mul _
        _ ≤ ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)‖ₑ
              + ‖x • wallRestPartNeg E T g m σ x‖ₑ := enorm_add_le _ _
        _ = ‖x • firstBoundaryBlock T g m σ x‖ₑ + ‖x • wallRestPartNeg E T g m σ x‖ₑ := by
              have hI : ‖(Complex.I : ℂ)‖ₑ = 1 := by
                rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one]
              rw [enorm_smul, hI, one_mul]
    exact le_trans (pow_le_pow_left' hnorm 2) (hpair _ _)
  have hmeasFB : AEMeasurable
      (fun x : ℝ => ‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2) (volume.restrict (Iio (-Y))) := by
    have hFB := aestronglyMeasurable_firstBoundaryBlock (T := T) hσ0 hσ1 measurableSet_Iio
      hg.aestronglyMeasurable
      (fun x hx L hL => lt_of_lt_of_le hμ (hfloorL x hx L hL))
    exact ((continuous_id.aestronglyMeasurable.smul hFB).enorm).pow_const 2
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hsq)
  rw [lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤), lintegral_add_left' hmeasFB]
  exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨h1, hrest⟩)

set_option maxHeartbeats 1000000 in
/-- **`(47)`: the Gamma derivative scattering criterion, on the inward ray.** -/
theorem lintegral_sq_freq_forcedProfile_negRay_ne_top_iff {σ Y μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 < K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (c : X) (hY : 1 ≤ Y) (hfloor : ∀ x ∈ Iic (-Y), μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x in Iio (-Y), ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2) ≠ ⊤
      ↔ wallScatteringChargeNeg E T g c m σ (-Y) = 0 := by
  have hW : (-Y : ℝ) ≤ -1 := by linarith
  have hIio : ∀ x ∈ Iio (-Y), μ₀ - m ≤ wallFloor T σ x :=
    fun x hx => hfloor x (mem_Iic.mpr (le_of_lt (mem_Iio.mp hx)))
  have hfloorL : ∀ x : ℝ, x ≤ -Y → ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L := by
    intro x hx L hL
    have hm : m ≤ L := hL.1
    have := hfloor x (mem_Iic.mpr hx)
    linarith
  have hgapR : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Iic (-Y), μ₀ ≤ wallFloor T σ t + L :=
    fun L hL t ht => hfloorL t ht L hL
  have hdecomp : ∀ x ∈ Iio (-Y), x • forcedProfile E T (blockSource g m) c σ x
      = x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallScatteringChargeNeg E T g c m σ (-Y))
        + x • wallScatteringRemainderNeg E T g m σ x := by
    intro x hx
    have hxW : x ≤ -Y := le_of_lt (mem_Iio.mp hx)
    have hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc (-Y) x, 0 < wallFloor T σ t + L := by
      intro L hL t ht
      rw [Set.uIcc_of_ge hxW] at ht
      exact lt_of_lt_of_le hμ (hfloorL t (le_trans ht.2 le_rfl) L hL)
    rw [forcedProfile_eq_chargeNeg_add_remainderNeg hEdiff hE hEne hT hσ0 hσ1 hμ hb₂ hK₂.le hg c
      hW hxW (hfloorL x hxW) (hfloorL (-Y) le_rfl) hgapI hgapR, smul_add]
  have hcongr : (∫⁻ x in Iio (-Y), ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
      = ∫⁻ x in Iio (-Y), ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (wallScatteringChargeNeg E T g c m σ (-Y))
          + x • wallScatteringRemainderNeg E T g m σ x‖ₑ ^ 2 :=
    setLIntegral_congr_fun measurableSet_Iio (fun x hx => by rw [hdecomp x hx])
  have hH : Continuous fun x : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    continuous_stripPropagator_line hEdiff hE hEne hσ0 hσ1
  have hleadm : AEStronglyMeasurable
      (fun x : ℝ => x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallScatteringChargeNeg E T g c m σ (-Y))) (volume.restrict (Iio (-Y))) :=
    (continuous_id.smul (hH.clm_apply continuous_const)).aestronglyMeasurable
  have htotm : AEStronglyMeasurable
      (fun x : ℝ => x • forcedProfile E T (blockSource g m) c σ x)
      (volume.restrict (Iio (-Y))) :=
    (continuous_id.smul
      (continuous_forcedProfile_blockSource hEdiff hE hEne hσ0 hσ1 hg c)).aestronglyMeasurable
  have hremm : AEStronglyMeasurable
      (fun x : ℝ => x • wallScatteringRemainderNeg E T g m σ x)
      (volume.restrict (Iio (-Y))) := by
    refine (htotm.sub hleadm).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    simp only [Pi.sub_apply]
    rw [hdecomp x hx]
    abel
  have hrem := lintegral_sq_freq_wallScatteringRemainderNeg_ne_top hEdiff hE hEne hσ0 hσ1 hμ
    hb₁ hK₁ hb₂ hK₂.le hgd hg2 hgm hg'2 hsupp hg hg' hY hIio
  constructor
  · intro htot
    by_contra hne
    have hlead : (∫⁻ x in Iio (-Y), ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallScatteringChargeNeg E T g c m σ (-Y))‖ₑ ^ 2) = ⊤ :=
      lintegral_sq_freq_stripPropagator_negRay_eq_top hσ0 hσ1 hE hb₂ hK₂ hW hne
    exact htot (hcongr.trans (lintegral_sq_add_eq_top hleadm hremm hlead hrem))
  · intro hzero
    rw [hcongr, hzero]
    simpa using hrem

end GaloisForLFunctions.RHTower
