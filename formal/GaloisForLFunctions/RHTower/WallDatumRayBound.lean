import GaloisForLFunctions.RHTower.WallThresholdArithmetic
import GaloisForLFunctions.RHTower.WallForcedProfileWindow
import GaloisForLFunctions.RHTower.StripPropagatorRayMass

/-!
# The propagated datum away from the threshold

At the block threshold the two contributions of the accumulated datum both land on one power of the
threshold: the initial datum is damped by the ray decay `Y^{-2σ} ≤ 1`, and the accumulated source,
which grows like `(1+Y)^{2p}` with `p = 1/2 + σ` and picks up a further `Y` from Cauchy–Schwarz on
the window, is cut back by the same ray decay through

`(1+Y)^{2p} · Y^{1-2σ} ≤ 4^p · Y²`.

This is the exponent bookkeeping of the card: `2p − 2σ = 1`.

Both frequency rays are covered at once.  The base point `W` of the datum is the signed threshold —
`Y` outwards, `−Y` inwards — and only its modulus enters the estimate, the window `[0,W]` and the
inverse propagator's growth on it being controlled by `|W|`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **The propagated datum on a region of large frequency.**  One constant, quantified before the
region, the threshold, the block and the datum. -/
theorem lintegral_sq_region_thresholdDatum_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Set ℝ), MeasurableSet A → ∀ (Y : ℝ), 1 ≤ Y →
      ((∫⁻ x in A, oneAddAbsWeight (2 * (1 / 2 + σ)) x)
        ≤ ENNReal.ofReal (Y ^ (1 - 2 * (1 / 2 + σ)) / (2 * (1 / 2 + σ) - 1))) →
      ∀ (W : ℝ), |W| = Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∫⁻ x in A, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (thresholdDatum E T (blockSource g m) c σ W)‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨C₁, hC₁, hray⟩ := exists_bound_lintegral_sq_region_stripPropagator_enorm hT hE hσ0 hσ1
  obtain ⟨C₂, hC₂, hdat⟩ := enorm_thresholdDatum_le' (T := T) hT hE hσ0 hσ1
  refine ⟨max (4 * C₁) (4 * C₁ * (C₂ ^ 2 * (Real.pi / 2) * 4 ^ (1 / 2 + σ))),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro A hA Y hY hmass W hW g c m hg2 hsupp
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  set N : ℝ := ∫ L : ℝ, ‖g L‖ ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set M : ℝ≥0∞ := ∫⁻ t in uIoc (0 : ℝ) W, ‖blockSource g m t‖ₑ with hM
  have hMsq : M ^ 2 ≤ ENNReal.ofReal Y * ENNReal.ofReal ((Real.pi / 2) * N) := by
    have h := sq_lintegral_enorm_blockSource_window_le (Y := W) hg2 hsupp
    rwa [hW] at h
  set p : ℝ := 1 / 2 + σ with hp
  have hp0 : (0 : ℝ) < p := by rw [hp]; linarith
  set K : ℝ := C₂ * (1 + Y) ^ p with hK
  have hK0 : 0 ≤ K := by
    refine mul_nonneg hC₂ (Real.rpow_nonneg (by linarith) _)
  -- the datum, squared, is a single real bound
  set D : ℝ := 4 * (‖c‖ ^ 2 + K ^ 2 * (Y * ((Real.pi / 2) * N))) with hD
  have hD0 : 0 ≤ D := by positivity
  have hdsq : ‖thresholdDatum E T (blockSource g m) c σ W‖ₑ ^ 2 ≤ ENNReal.ofReal D := by
    have h1 : ‖thresholdDatum E T (blockSource g m) c σ W‖ₑ
        ≤ ‖c‖ₑ + ENNReal.ofReal K * M := by
      have h := hdat W (blockSource g m) c
      rwa [hW, ← hK, ← hM] at h
    have h2 : ‖thresholdDatum E T (blockSource g m) c σ W‖ₑ ^ 2
        ≤ 4 * (‖c‖ₑ ^ 2 + ENNReal.ofReal K ^ 2 * M ^ 2) := by
      refine le_trans (pow_le_pow_left' h1 2) ?_
      have := sq_add_two_le ‖c‖ₑ (ENNReal.ofReal K * M)
      rwa [mul_pow] at this
    refine h2.trans ?_
    have h3 : ENNReal.ofReal K ^ 2 * M ^ 2
        ≤ ENNReal.ofReal (K ^ 2 * (Y * ((Real.pi / 2) * N))) := by
      rw [← ENNReal.ofReal_pow hK0]
      refine le_trans (mul_le_mul_left' hMsq _) (le_of_eq ?_)
      have e1 : ENNReal.ofReal Y * ENNReal.ofReal ((Real.pi / 2) * N)
          = ENNReal.ofReal (Y * ((Real.pi / 2) * N)) := (ENNReal.ofReal_mul hY0.le).symm
      have e2 : ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (Y * ((Real.pi / 2) * N))
          = ENNReal.ofReal (K ^ 2 * (Y * ((Real.pi / 2) * N))) :=
        (ENNReal.ofReal_mul (pow_nonneg hK0 2)).symm
      rw [e1, e2]
    have h4 : ‖c‖ₑ ^ 2 = ENNReal.ofReal (‖c‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    have hDeq : ENNReal.ofReal D
        = 4 * (ENNReal.ofReal (‖c‖ ^ 2) + ENNReal.ofReal (K ^ 2 * (Y * ((Real.pi / 2) * N)))) := by
      rw [hD, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    rw [h4, hDeq]
    gcongr
  refine le_trans (le_trans (hray A hA Y hY0 hmass _) (mul_le_mul_left' hdsq _)) ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real arithmetic
  have hpow : Y ^ (-(2 * σ)) ≤ 1 := rpow_neg_le_one hσ0 hY
  have hpow0 : 0 < Y ^ (-(2 * σ)) := Real.rpow_pos_of_pos hY0 _
  have hthr : (1 + Y) ^ (2 * p) * Y ^ (1 - 2 * σ) ≤ 4 ^ p * Y ^ 2 :=
    thresholdExponent_le hσ0 hY
  have hcomb : Y ^ (-(2 * σ)) * (K ^ 2 * (Y * ((Real.pi / 2) * N)))
      ≤ C₂ ^ 2 * (Real.pi / 2) * 4 ^ p * (Y ^ 2 * N) := by
    have hKsq : K ^ 2 = C₂ ^ 2 * (1 + Y) ^ (2 * p) := by
      rw [hK, mul_pow, ← Real.rpow_natCast ((1 + Y) ^ p) 2, ← Real.rpow_mul (by linarith)]
      ring_nf
    have hYc : Y ^ (-(2 * σ)) * Y = Y ^ (1 - 2 * σ) := by
      nth_rewrite 2 [show Y = Y ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hY0]
      ring_nf
    have hstep : Y ^ (-(2 * σ)) * (K ^ 2 * (Y * ((Real.pi / 2) * N)))
        = (C₂ ^ 2 * (Real.pi / 2) * N) * ((1 + Y) ^ (2 * p) * (Y ^ (-(2 * σ)) * Y)) := by
      rw [hKsq]; ring
    rw [hstep, hYc]
    have hcoef : 0 ≤ C₂ ^ 2 * (Real.pi / 2) * N := by positivity
    calc (C₂ ^ 2 * (Real.pi / 2) * N) * ((1 + Y) ^ (2 * p) * Y ^ (1 - 2 * σ))
        ≤ (C₂ ^ 2 * (Real.pi / 2) * N) * (4 ^ p * Y ^ 2) :=
          mul_le_mul_of_nonneg_left hthr hcoef
      _ = C₂ ^ 2 * (Real.pi / 2) * 4 ^ p * (Y ^ 2 * N) := by ring
  have hexp : C₁ * Y ^ (-(2 * σ)) * D
      ≤ 4 * C₁ * ‖c‖ ^ 2 + 4 * C₁ * (C₂ ^ 2 * (Real.pi / 2) * 4 ^ p) * (Y ^ 2 * N) := by
    rw [hD]
    have hA' : Y ^ (-(2 * σ)) * ‖c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
      nlinarith [sq_nonneg ‖c‖]
    nlinarith [mul_le_mul_of_nonneg_left hcomb hC₁,
      mul_le_mul_of_nonneg_left hA' hC₁]
  refine hexp.trans ?_
  have h1 : 4 * C₁ ≤ max (4 * C₁) (4 * C₁ * (C₂ ^ 2 * (Real.pi / 2) * 4 ^ p)) := le_max_left _ _
  have h2 : 4 * C₁ * (C₂ ^ 2 * (Real.pi / 2) * 4 ^ p)
      ≤ max (4 * C₁) (4 * C₁ * (C₂ ^ 2 * (Real.pi / 2) * 4 ^ p)) := le_max_right _ _
  have hc2 : 0 ≤ ‖c‖ ^ 2 := by positivity
  have hY2N : 0 ≤ Y ^ 2 * N := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hc2, mul_le_mul_of_nonneg_right h2 hY2N]

/-- **The propagated datum on the outward ray.** -/
theorem lintegral_sq_ray_thresholdDatum_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 ≤ Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (thresholdDatum E T (blockSource g m) c σ Y)‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨C, hC, h⟩ := lintegral_sq_region_thresholdDatum_le hT hE hσ0 hσ1
  refine ⟨C, hC, fun Y hY g c m hg2 hsupp => ?_⟩
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  exact h (Ioi Y) measurableSet_Ioi Y hY
    (lintegral_oneAddAbsWeight_Ioi_le (by linarith) hY0) Y (abs_of_pos hY0) g c m hg2 hsupp

/-- **The propagated datum on the inward ray.** -/
theorem lintegral_sq_negRay_thresholdDatum_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℝ), 1 ≤ Y → ∀ (g : ℝ → X) (c : X) (m : ℝ),
      MemLp g 2 (volume : Measure ℝ) → (∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) →
      (∫⁻ x in Iio (-Y), ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (thresholdDatum E T (blockSource g m) c σ (-Y))‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + Y ^ 2 * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
  obtain ⟨C, hC, h⟩ := lintegral_sq_region_thresholdDatum_le hT hE hσ0 hσ1
  refine ⟨C, hC, fun Y hY g c m hg2 hsupp => ?_⟩
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  exact h (Iio (-Y)) measurableSet_Iio Y hY
    (lintegral_oneAddAbsWeight_Iio_le (by linarith) hY0) (-Y)
    (by rw [abs_neg, abs_of_pos hY0]) g c m hg2 hsupp

end GaloisForLFunctions.RHTower
